import Mathlib

/-!
# Synthesis Search Graph Capture

For a given typeclass, runs synthesis with tracing enabled and captures the full
search tree from the trace output. The tree is converted to a structured
`SynthSearchNode` type and written as both JSON and an interactive HTML report.

The HTML output includes:
- Summary cards (result, heartbeats, node count, max depth)
- Flame graph visualization of time spent in each synthesis subtree
- Goal frequency analysis table showing repeated synthesis goals
- Hot path & fan-out display showing the critical time path
- Collapsible search tree with color-coded success/failure nodes
- Expand All / Collapse All controls, text search, and per-class filters
- Aggregated instance statistics table (top 20 by total duration)

Usage: `#synth_trace ClassName`
-/

open Lean Meta Elab Command

/-- Result of a single synthesis attempt. -/
private inductive SynthResult
  | success   -- synthesis found an instance
  | failure   -- synthesis explored and gave up
  | undef     -- synthesis got stuck
  | timeout   -- exception (typically heartbeat exhaustion)

private def SynthResult.toString : SynthResult → String
  | .success => "success"
  | .failure => "failure"
  | .undef   => "undef"
  | .timeout => "timeout"

/-- A node in the typeclass synthesis search tree. -/
private structure SynthSearchNode where
  /-- Trace class (e.g., `Meta.synthInstance.tryResolve`). -/
  cls : Name
  /-- Formatted message describing this step. -/
  msg : String
  /-- Wall-clock duration in seconds (0 if not recorded). -/
  duration : Float
  /-- Child steps. -/
  children : Array SynthSearchNode
  deriving Inhabited

/-- The complete synthesis search result for a typeclass. -/
private structure SynthSearchResult where
  /-- The typeclass name. -/
  className : Name
  /-- Whether synthesis succeeded, failed, got stuck, or timed out. -/
  result : SynthResult
  /-- Heartbeats consumed. -/
  heartbeats : Nat
  /-- The root of the search tree (from trace). -/
  root : Option SynthSearchNode
  /-- Total number of nodes in the tree. -/
  nodeCount : Nat
  /-- Maximum depth of the tree. -/
  maxDepth : Nat

/-- An entry in the hot path (critical path following maximum duration at each level). -/
private structure HotPathEntry where
  cls : Name
  msg : String
  duration : Float
  selfTime : Float
  siblingCount : Nat
  siblingNames : Array String
  isLeaf : Bool
  deriving Inhabited

/-- Build a `SynthSearchNode` from a `MessageData.trace` node.
Unwraps `.withContext` / `.withNamingContext` / `.tagged` wrappers that the trace
infrastructure adds around `.trace` nodes. -/
private partial def ofMessageData (md : MessageData) : BaseIO (Option SynthSearchNode) := do
  match md with
  | .trace data msg children =>
    let fmt ← msg.format
    let childNodes ← children.filterMapM ofMessageData
    return some {
      cls := data.cls
      msg := fmt.pretty
      duration := data.stopTime - data.startTime
      children := childNodes
    }
  | .withContext _ inner => ofMessageData inner
  | .withNamingContext _ inner => ofMessageData inner
  | .tagged _ inner => ofMessageData inner
  | _ => return none

/-- Count total nodes in a search tree. -/
private partial def SynthSearchNode.countNodes (n : SynthSearchNode) : Nat :=
  1 + n.children.foldl (fun acc c => acc + c.countNodes) 0

/-- Maximum depth of a search tree. -/
private partial def SynthSearchNode.depth (n : SynthSearchNode) : Nat :=
  1 + (n.children.foldl (fun acc c => max acc c.depth) 0)

/-- Escape a string for use inside a JSON string literal. -/
private def jsonEscapeString (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
    | '\"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c    => c.toString) ""

/-- Escape a string for safe embedding inside HTML content. -/
private def htmlEscapeString (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
    | '<' => "&lt;"
    | '>' => "&gt;"
    | '&' => "&amp;"
    | '\"' => "&quot;"
    | c   => c.toString) ""

/-- Convert a `SynthSearchNode` to a JSON string. -/
private partial def SynthSearchNode.toJson (n : SynthSearchNode) (indent : Nat := 0) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  let pad2 := String.ofList (List.replicate (indent + 2) ' ')
  let childrenJson :=
    if n.children.isEmpty then "[]"
    else "[\n" ++
      String.intercalate ",\n" (n.children.map (·.toJson (indent + 4))).toList ++
      "\n" ++ pad2 ++ "]"
  pad ++ "{\n" ++
    pad2 ++ s!"\"cls\": \"{jsonEscapeString n.cls.toString}\",\n" ++
    pad2 ++ s!"\"msg\": \"{jsonEscapeString n.msg}\",\n" ++
    pad2 ++ s!"\"duration\": {n.duration},\n" ++
    pad2 ++ "\"children\": " ++ childrenJson ++ "\n" ++
  pad ++ "}"

/-- Serialize a `SynthSearchNode` to compact JSON for the flame graph renderer.
Each node becomes `{name, cls, msg, dur, ok, children}`. -/
private partial def SynthSearchNode.toFlameJson (n : SynthSearchNode) : String :=
  let ok := if n.msg.startsWith "✅️" then "true" else "false"
  let childJson :=
    if n.children.isEmpty then "[]"
    else "[" ++ String.intercalate "," (n.children.map (·.toFlameJson)).toList ++ "]"
  "{\"name\":\"" ++ jsonEscapeString n.cls.toString ++ "\"," ++
  "\"cls\":\"" ++ jsonEscapeString n.cls.toString ++ "\"," ++
  "\"msg\":\"" ++ jsonEscapeString n.msg ++ "\"," ++
  "\"dur\":" ++ toString n.duration ++ "," ++
  "\"ok\":" ++ ok ++ "," ++
  "\"children\":" ++ childJson ++ "}"

/-- Convert a `SynthSearchResult` to a JSON string. -/
private def SynthSearchResult.toJson (r : SynthSearchResult) : String :=
  let traceJson := match r.root with
    | none => "null"
    | some node => node.toJson 2
  "{\n" ++
    s!"  \"class\": \"{jsonEscapeString r.className.toString}\",\n" ++
    s!"  \"result\": \"{r.result.toString}\",\n" ++
    s!"  \"heartbeats\": {r.heartbeats / 1000},\n" ++
    s!"  \"nodeCount\": {r.nodeCount},\n" ++
    s!"  \"maxDepth\": {r.maxDepth},\n" ++
    "  \"trace\": " ++ traceJson ++ "\n" ++
  "}\n"

/-- Generate an HTML tree node for a `SynthSearchNode`. Leaf nodes are plain
`<div>`s; interior nodes use `<details>/<summary>` for collapsible display. -/
private partial def SynthSearchNode.toHtmlNode
    (n : SynthSearchNode) (depth : Nat := 0) : String :=
  let escaped := htmlEscapeString n.msg
  -- Color class based on emoji prefix
  let colorClass :=
    if n.msg.startsWith "✅️" then "success"
    else if n.msg.startsWith "❌️" then "fail"
    else "neutral"
  -- Duration badge
  let durBadge :=
    let ms := n.duration * 1000
    let durClass := if ms > 1.0 then "dur-slow" else "dur-ok"
    s!"<span class=\"badge {durClass}\">{Float.toString (Float.round (ms * 100) / 100)}ms</span>"
  -- Cls label
  let clsLabel := s!"<span class=\"cls-label\">{htmlEscapeString n.cls.toString}</span>"
  let summary := s!"{clsLabel} {escaped} {durBadge}"
  if n.children.isEmpty then
    s!"<div class=\"leaf {colorClass}\" data-cls=\"{htmlEscapeString n.cls.toString}\"" ++
      s!" data-msg=\"{htmlEscapeString n.msg}\">{summary}</div>\n"
  else
    let open_ := if depth < 1 then " open" else ""
    let childHtml := String.join (n.children.map (·.toHtmlNode (depth + 1))).toList
    s!"<details class=\"node {colorClass}\"{open_}" ++
      s!" data-cls=\"{htmlEscapeString n.cls.toString}\"" ++
      s!" data-msg=\"{htmlEscapeString n.msg}\">\n" ++
      s!"<summary>{summary} <span class=\"child-count\">({n.children.size})</span></summary>\n" ++
      s!"<div class=\"children\">{childHtml}</div>\n" ++
      s!"</details>\n"

/-- Extract instance name from a trace message like "✅️ apply @Foo.bar" or
"❌️ apply @Foo.bar". Returns `none` if the message doesn't match. -/
private def extractInstanceName (msg : String) : Option String :=
  let s := msg.trimAscii.toString
  -- Skip the leading emoji + space
  let afterEmoji :=
    if s.startsWith "✅️" then s.drop "✅️".length |>.trimAscii.toString
    else if s.startsWith "❌️" then s.drop "❌️".length |>.trimAscii.toString
    else ""
  if afterEmoji.startsWith "apply " then
    let rest := afterEmoji.drop "apply ".length |>.trimAscii.toString
    -- Take the first word (the instance name)
    let name := (rest.takeWhile (fun c => !c.isWhitespace)).toString
    if name.isEmpty then none else some name
  else none

/-- Per-instance statistics: (tried, succeeded, failed, total duration ms). -/
private abbrev InstanceStats := Std.HashMap String (Nat × Nat × Nat × Float)

/-- Walk the tree and collect per-instance statistics. -/
private partial def SynthSearchNode.collectInstanceStats
    (n : SynthSearchNode) (acc : InstanceStats) : InstanceStats :=
  let acc := if n.cls == `Meta.synthInstance then
    match extractInstanceName n.msg with
    | some name =>
      let (tried, succ, fail, dur) := acc.getD name (0, 0, 0, 0.0)
      let isSuccess := n.msg.startsWith "✅️"
      let succ' := if isSuccess then succ + 1 else succ
      let fail' := if !isSuccess then fail + 1 else fail
      acc.insert name (tried + 1, succ', fail', dur + n.duration)
    | none => acc
  else acc
  n.children.foldl (fun a c => c.collectInstanceStats a) acc

/-- Collect unique trace class names from the tree. -/
private partial def SynthSearchNode.collectClasses
    (n : SynthSearchNode) (acc : Std.HashSet String) : Std.HashSet String :=
  let acc := acc.insert n.cls.toString
  n.children.foldl (fun a c => c.collectClasses a) acc

/-- Extract goal type from a synthesis trace message. Returns `(goal, isSuccess, isFailure)`.
Matches top-level "✅️ GoalType" / "❌️ GoalType" (not "apply") at `Meta.synthInstance`,
and "new goal GoalType" messages. -/
private def extractGoalType (msg : String) (cls : Name) : Option (String × Bool × Bool) :=
  let s := msg.trimAscii.toString
  if cls == `Meta.synthInstance then
    if s.startsWith "✅️" then
      let rest := (s.drop "✅️".length).trimAscii.toString
      if rest.startsWith "apply " || rest.isEmpty then none
      else some (rest, true, false)
    else if s.startsWith "❌️" then
      let rest := (s.drop "❌️".length).trimAscii.toString
      if rest.startsWith "apply " || rest.isEmpty then none
      else some (rest, false, true)
    else none
  else
    if s.startsWith "new goal " then
      let rest := (s.drop "new goal ".length).trimAscii.toString
      if rest.isEmpty then none else some (rest, false, false)
    else none

/-- Per-goal statistics: (attempts, successes, failures, total duration seconds). -/
private abbrev GoalStats := Std.HashMap String (Nat × Nat × Nat × Float)

/-- Walk the tree and collect per-goal-type statistics. -/
private partial def SynthSearchNode.collectGoalStats
    (n : SynthSearchNode) (acc : GoalStats) : GoalStats :=
  let acc := match extractGoalType n.msg n.cls with
    | some (goal, isSucc, isFail) =>
      let (att, succ, fail, dur) := acc.getD goal (0, 0, 0, 0.0)
      acc.insert goal (att + 1, if isSucc then succ + 1 else succ,
        if isFail then fail + 1 else fail, dur + n.duration)
    | none => acc
  n.children.foldl (fun a c => c.collectGoalStats a) acc

/-- Self-time: node duration minus sum of children's durations. -/
private def SynthSearchNode.selfTime (n : SynthSearchNode) : Float :=
  n.duration - n.children.foldl (fun acc c => acc + c.duration) 0.0

/-- Follow the child with maximum duration at each level to build the hot (critical) path.
Returns an array of `HotPathEntry` from root to leaf. -/
private partial def SynthSearchNode.hotPath (n : SynthSearchNode) : Array HotPathEntry :=
  let entry : HotPathEntry := {
    cls := n.cls, msg := n.msg, duration := n.duration, selfTime := n.selfTime
    siblingCount := 0, siblingNames := #[], isLeaf := n.children.isEmpty
  }
  if n.children.isEmpty then #[entry]
  else
    let maxChild := n.children.foldl (fun best c =>
      if c.duration > best.duration then c else best) n.children[0]!
    let sibCount := n.children.size - 1
    let others := (n.children.filter (fun c =>
      c.duration != maxChild.duration || c.msg != maxChild.msg)).qsort
        (fun a b => a.duration > b.duration)
    let sibNames := (others.extract 0 (min 5 others.size)).map (fun c =>
      let ms := Float.toString (Float.round (c.duration * 1000 * 100) / 100)
      s!"{c.msg} ({ms}ms)")
    let rest := maxChild.hotPath
    if rest.isEmpty then #[entry]
    else
      #[entry, { rest[0]! with siblingCount := sibCount, siblingNames := sibNames }]
        ++ rest.extract 1 rest.size

/-- Generate a complete self-contained HTML document for a synthesis trace. -/
private def SynthSearchResult.toHtml (r : SynthSearchResult) : String :=
  let name := htmlEscapeString r.className.toString
  let resultClass := match r.result with
    | .success => "success" | .failure => "fail" | _ => "neutral"
  -- Collect instance stats
  let stats : InstanceStats := match r.root with
    | some root => root.collectInstanceStats {}
    | none => {}
  -- Sort by total duration descending
  let statsList := stats.toList.toArray.qsort (fun a b =>
    let (_, _, _, da) := a.2; let (_, _, _, db) := b.2; da > db)
  let top20 := statsList.extract 0 (min 20 statsList.size)
  -- Build stats table rows
  let statsRows := String.join (top20.map (fun (inst, tried, succ, fail, dur) =>
    s!"<tr><td class=\"inst-name\">{htmlEscapeString inst}</td>" ++
    s!"<td>{tried}</td><td>{succ}</td><td>{fail}</td>" ++
    s!"<td>{Float.toString (Float.round (dur * 1000 * 100) / 100)}</td></tr>\n")).toList
  -- Collect unique cls values for filter checkboxes
  let clsSet := match r.root with
    | some root => root.collectClasses ∅
    | none => ∅
  let clsCheckboxes := String.join (clsSet.toList.toArray.qsort (· < ·) |>.map (fun c =>
    s!"<label><input type=\"checkbox\" class=\"cls-filter\" value=\"{htmlEscapeString c}\"" ++
    s!" checked> {htmlEscapeString c}</label>\n")).toList
  -- Tree HTML
  let treeHtml := match r.root with
    | some root => root.toHtmlNode
    | none => "<p>No trace data.</p>"
  -- Flame graph JSON
  let flameJson := match r.root with
    | some root => root.toFlameJson
    | none => "null"
  -- Goal stats
  let goalStats : GoalStats := match r.root with
    | some root => root.collectGoalStats {}
    | none => {}
  let goalStatsList := goalStats.toList.toArray.qsort (fun a b =>
    let (_, _, _, da) := a.2; let (_, _, _, db) := b.2; da > db)
  let maxAttempts := goalStatsList.foldl (fun mx (_, att, _, _, _) => max mx att) (1 : Nat)
  let goalRows := String.join (goalStatsList.map (fun (goal, att, succ, fail, dur) =>
    let ms := Float.toString (Float.round (dur * 1000 * 100) / 100)
    let avg := if att > 0 then
      Float.toString (Float.round (dur * 1000 / (Float.ofNat att) * 100) / 100)
    else "0"
    let heat := Float.toString (Float.ofNat att / Float.ofNat maxAttempts)
    s!"<tr><td class=\"goal-name\">{htmlEscapeString goal}</td>" ++
    s!"<td class=\"heat\" style=\"--h:{heat}\">{att}</td>" ++
    s!"<td>{succ}</td><td>{fail}</td>" ++
    s!"<td>{ms}</td><td>{avg}</td></tr>\n")).toList
  -- Hot path
  let hotPathEntries := match r.root with
    | some root => root.hotPath
    | none => #[]
  let totalDur := r.root.map (·.duration) |>.getD 1.0
  let (hotPathHtml, _) := hotPathEntries.foldl (fun (html, idx) e =>
    let ms := Float.toString (Float.round (e.duration * 1000 * 100) / 100)
    let selfMs := Float.toString (Float.round (e.selfTime * 1000 * 100) / 100)
    let pct := if totalDur > 0 then
      Float.toString (Float.round (e.duration / totalDur * 10000) / 100)
    else "0"
    let fanClass := if e.siblingCount >= 10 then "fan-high"
      else if e.siblingCount >= 5 then "fan-med" else "fan-low"
    let sibListHtml := if e.siblingNames.isEmpty then ""
      else s!"<div class=\"sib-list hidden\" id=\"sib-{idx}\">" ++
        String.join (e.siblingNames.map (fun sibMsg =>
          s!"<div class=\"sib-item\">{htmlEscapeString sibMsg}</div>")).toList ++
        "</div>"
    let fanBadge := if e.siblingCount > 0 then
      s!"<span class=\"fan-badge {fanClass}\" onclick=\"toggleSib({idx})\">" ++
      s!"+{e.siblingCount}</span>" ++ sibListHtml
    else ""
    let connector := if e.isLeaf then "" else "<div class=\"hp-connector\"></div>\n"
    let entry :=
      s!"<div class=\"hp-entry\">" ++
      s!"<div class=\"hp-bar\" style=\"width:{pct}%\"></div>" ++
      s!"<div class=\"hp-content\">" ++
      s!"<span class=\"cls-label\">{htmlEscapeString e.cls.toString}</span> " ++
      s!"<span class=\"hp-msg\">{htmlEscapeString e.msg}</span> " ++
      s!"<span class=\"badge dur-slow\">{ms}</span> " ++
      s!"<span class=\"badge dur-ok\">self: {selfMs}</span>" ++
      "</div>" ++
      s!"<div class=\"hp-fanout\">{fanBadge}</div>" ++
      "</div>\n" ++ connector
    (html ++ entry, idx + 1)) ("", 0)
  -- Assemble document
  s!"<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\">\n" ++
  s!"<title>Synth Trace: {name}</title>\n" ++
  "<style>\n" ++
  ":root{--bg:#1e1e2e;--fg:#cdd6f4;--card:#313244;--border:#585b70;" ++
  "--green:#a6e3a1;--red:#f38ba8;--yellow:#f9e2af;--blue:#89b4fa;" ++
  "--mauve:#cba6f7;--text:#bac2de}\n" ++
  "body{background:var(--bg);color:var(--fg);font-family:system-ui,sans-serif;" ++
  "margin:0;padding:20px;line-height:1.5}\n" ++
  "h1{color:var(--mauve);margin-bottom:10px}\n" ++
  "h2{color:var(--blue);margin-top:30px}\n" ++
  ".summary{display:flex;gap:16px;flex-wrap:wrap;margin:16px 0}\n" ++
  ".card{background:var(--card);border:1px solid var(--border);border-radius:8px;" ++
  "padding:12px 20px;min-width:120px}\n" ++
  ".card .label{font-size:12px;color:var(--text);text-transform:uppercase}\n" ++
  ".card .value{font-size:24px;font-weight:bold}\n" ++
  ".card .value.success{color:var(--green)}\n" ++
  ".card .value.fail{color:var(--red)}\n" ++
  ".card .value.neutral{color:var(--yellow)}\n" ++
  ".controls{background:var(--card);border:1px solid var(--border);border-radius:8px;" ++
  "padding:12px 16px;margin:16px 0;display:flex;gap:12px;align-items:center;flex-wrap:wrap}\n" ++
  ".controls button,.controls-btn{background:var(--blue);color:var(--bg);border:none;" ++
  "border-radius:4px;padding:6px 14px;cursor:pointer;font-size:13px}\n" ++
  ".controls button:hover,.controls-btn:hover{opacity:0.85}\n" ++
  ".controls input[type=text]{background:var(--bg);color:var(--fg);border:1px solid " ++
  "var(--border);border-radius:4px;padding:6px 10px;width:200px}\n" ++
  ".cls-filters{display:flex;gap:8px;flex-wrap:wrap;font-size:12px;margin-top:4px}\n" ++
  ".cls-filters label{color:var(--text)}\n" ++
  "table{border-collapse:collapse;width:100%;max-width:900px}\n" ++
  "th,td{border:1px solid var(--border);padding:6px 12px;text-align:left}\n" ++
  "th{background:var(--card);color:var(--blue)}\n" ++
  "td.inst-name{font-family:monospace;font-size:13px;max-width:400px;" ++
  "overflow:hidden;text-overflow:ellipsis;white-space:nowrap}\n" ++
  ".tree{margin-top:12px}\n" ++
  "details{margin-left:16px;border-left:2px solid var(--border);padding-left:8px}\n" ++
  "summary{cursor:pointer;padding:2px 0;font-family:monospace;font-size:13px;" ++
  "list-style:none}\n" ++
  "summary::-webkit-details-marker{display:none}\n" ++
  "summary::before{content:'\\25b6';display:inline-block;width:16px;transition:" ++
  "transform 0.15s;font-size:10px}\n" ++
  "details[open]>summary::before{transform:rotate(90deg)}\n" ++
  ".leaf{margin-left:16px;padding:2px 0 2px 24px;font-family:monospace;font-size:13px}\n" ++
  ".success>summary,.leaf.success{color:var(--green)}\n" ++
  ".fail>summary,.leaf.fail{color:var(--red)}\n" ++
  ".neutral>summary,.leaf.neutral{color:var(--text)}\n" ++
  ".badge{font-size:11px;padding:1px 6px;border-radius:3px;margin-left:6px}\n" ++
  ".dur-ok{background:#31324480;color:var(--text)}\n" ++
  ".dur-slow{background:#f38ba822;color:var(--red)}\n" ++
  ".cls-label{font-size:10px;background:var(--card);color:var(--mauve);" ++
  "padding:1px 5px;border-radius:3px;margin-right:4px}\n" ++
  ".child-count{font-size:11px;color:var(--text)}\n" ++
  ".hidden{display:none}\n" ++
  ".highlight{background:var(--yellow);color:var(--bg);border-radius:2px;padding:0 2px}\n" ++
  -- Flame graph CSS
  "#flame-container{position:relative;width:100%;overflow-x:auto;background:var(--card);" ++
  "border:1px solid var(--border);border-radius:8px;padding:8px;min-height:80px}\n" ++
  "#flame-tooltip{position:fixed;background:var(--bg);color:var(--fg);" ++
  "border:1px solid var(--border);border-radius:4px;padding:8px 12px;font-size:12px;" ++
  "pointer-events:none;display:none;z-index:1000;max-width:400px;" ++
  "font-family:monospace;white-space:pre-wrap}\n" ++
  -- Goal frequency table CSS
  ".goal-table th{cursor:pointer;user-select:none}\n" ++
  ".goal-table th:hover{background:var(--blue);color:var(--bg)}\n" ++
  ".goal-table th.sort-asc::after{content:' \\25B2'}\n" ++
  ".goal-table th.sort-desc::after{content:' \\25BC'}\n" ++
  "td.goal-name{font-family:monospace;font-size:13px;max-width:500px;" ++
  "overflow:hidden;text-overflow:ellipsis;white-space:nowrap}\n" ++
  "td.heat{background:rgba(243,139,168,calc(var(--h)*0.4));" ++
  "text-align:center;font-weight:bold}\n" ++
  -- Hot path CSS
  ".hp-chain{display:flex;flex-direction:column;gap:0;max-width:900px}\n" ++
  ".hp-entry{position:relative;background:var(--card);border:1px solid var(--border);" ++
  "border-radius:6px;padding:10px 14px;display:flex;align-items:center;" ++
  "gap:12px;overflow:visible}\n" ++
  ".hp-bar{position:absolute;left:0;top:0;bottom:0;" ++
  "background:linear-gradient(90deg,rgba(243,139,168,0.15),rgba(243,139,168,0.05));" ++
  "pointer-events:none}\n" ++
  ".hp-content{position:relative;flex:1;font-family:monospace;font-size:13px;" ++
  "overflow:hidden;text-overflow:ellipsis;white-space:nowrap}\n" ++
  ".hp-msg{color:var(--fg)}\n" ++
  ".hp-fanout{position:relative;flex-shrink:0}\n" ++
  ".fan-badge{display:inline-block;padding:2px 8px;border-radius:10px;font-size:11px;" ++
  "font-weight:bold;cursor:pointer}\n" ++
  ".fan-high{background:var(--red);color:var(--bg)}\n" ++
  ".fan-med{background:var(--yellow);color:var(--bg)}\n" ++
  ".fan-low{background:var(--card);color:var(--text);border:1px solid var(--border)}\n" ++
  ".sib-list{position:absolute;right:0;top:100%;background:var(--bg);" ++
  "border:1px solid var(--border);border-radius:4px;padding:6px;z-index:1000;" ++
  "min-width:300px;max-height:200px;overflow-y:auto;box-shadow:0 4px 12px rgba(0,0,0,0.5)}\n" ++
  ".sib-item{font-family:monospace;font-size:12px;color:var(--text);padding:2px 4px;" ++
  "border-bottom:1px solid var(--border)}\n" ++
  ".sib-item:last-child{border-bottom:none}\n" ++
  ".hp-connector{width:2px;height:16px;background:var(--border);margin-left:24px}\n" ++
  "</style>\n</head><body>\n" ++
  -- Title + Summary cards
  s!"<h1>Synth Trace: {name}</h1>\n" ++
  "<div class=\"summary\">\n" ++
  s!"<div class=\"card\"><div class=\"label\">Result</div>" ++
  s!"<div class=\"value {resultClass}\">{htmlEscapeString r.result.toString}</div></div>\n" ++
  s!"<div class=\"card\"><div class=\"label\">Heartbeats</div>" ++
  s!"<div class=\"value\">{r.heartbeats / 1000}</div></div>\n" ++
  s!"<div class=\"card\"><div class=\"label\">Nodes</div>" ++
  s!"<div class=\"value\">{r.nodeCount}</div></div>\n" ++
  s!"<div class=\"card\"><div class=\"label\">Max Depth</div>" ++
  s!"<div class=\"value\">{r.maxDepth}</div></div>\n" ++
  "</div>\n" ++
  -- Flame Graph
  "<h2>Flame Graph</h2>\n" ++
  "<div id=\"flame-container\"><div id=\"flame-svg\"></div></div>\n" ++
  "<button class=\"controls-btn\" id=\"flame-reset\" " ++
  "style=\"margin-top:8px\">Reset Zoom</button>\n" ++
  "<div id=\"flame-tooltip\"></div>\n" ++
  -- Goal Frequency Analysis
  "<h2>Goal Frequency Analysis</h2>\n" ++
  "<table class=\"goal-table\"><thead><tr>" ++
  "<th>Goal</th><th>Attempts</th><th>Successes</th><th>Failures</th>" ++
  "<th>Total ms</th><th>Avg ms</th></tr></thead>\n" ++
  s!"<tbody>{goalRows}</tbody></table>\n" ++
  -- Hot Path & Fan-out
  "<h2>Hot Path &amp; Fan-out</h2>\n" ++
  s!"<div class=\"hp-chain\">{hotPathHtml}</div>\n" ++
  -- Controls (existing, moved down)
  "<div class=\"controls\">\n" ++
  "<button onclick=\"expandAll()\">Expand All</button>\n" ++
  "<button onclick=\"collapseAll()\">Collapse All</button>\n" ++
  "<input type=\"text\" id=\"search\" placeholder=\"Search messages...\" " ++
  "oninput=\"doSearch()\">\n" ++
  s!"<div class=\"cls-filters\">{clsCheckboxes}</div>\n" ++
  "</div>\n" ++
  -- Instance Statistics
  "<h2>Instance Statistics</h2>\n" ++
  "<table><thead><tr><th>Instance</th><th>Tried</th><th>Succeeded</th>" ++
  "<th>Failed</th><th>Total ms</th></tr></thead>\n" ++
  s!"<tbody>{statsRows}</tbody></table>\n" ++
  -- Search Tree
  "<h2>Search Tree</h2>\n" ++
  s!"<div class=\"tree\">{treeHtml}</div>\n" ++
  -- JavaScript
  "<script>\n" ++
  -- Flame graph JS
  "var flameData=" ++ flameJson ++ ";\n" ++
  "(function(){\n" ++
  "if(!flameData)return;\n" ++
  "var c=document.getElementById('flame-svg');\n" ++
  "var tt=document.getElementById('flame-tooltip');\n" ++
  "var cur=flameData;\n" ++
  "function md(n){return n.children.length===0?1:1+Math.max(0," ++
  "...n.children.map(md))}\n" ++
  "function render(node){\n" ++
  "var W=c.parentElement.clientWidth-16||900;\n" ++
  "var bH=22,gap=2,d=Math.min(md(node),40);\n" ++
  "var H=d*(bH+gap)+4;\n" ++
  "var s='<svg width=\"'+W+'\" height=\"'+H+'\">';\n" ++
  "function draw(n,x,w,y,p){\n" ++
  "if(w<0.5)return;\n" ++
  "var f=n.ok?'#a6e3a1':'#f38ba8';\n" ++
  "s+='<rect x=\"'+x+'\" y=\"'+y+'\" width=\"'+Math.max(w-1,1)+" ++
  "'\" height=\"'+bH+'\" fill=\"'+f+'\" opacity=\"0.7\" rx=\"2\"" ++
  " data-p=\"'+p+'\" style=\"cursor:pointer\"/>';\n" ++
  "if(w>60){var lb=n.name.split('.').pop();" ++
  "s+='<text x=\"'+(x+3)+'\" y=\"'+(y+15)+" ++
  "'\" font-size=\"11\" fill=\"#1e1e2e\" pointer-events=\"none\">'+" ++
  "lb+'</text>';}\n" ++
  "if(n.children.length>0){\n" ++
  "var td=n.children.reduce(function(a,b){return a+b.dur},0)||1;\n" ++
  "var minW=3;\n" ++
  "var cx=x;\n" ++
  "for(var i=0;i<n.children.length;i++){\n" ++
  "var cw=Math.max((n.children[i].dur/td)*w,minW);\n" ++
  "draw(n.children[i],cx,cw,y+bH+gap,p+'.'+i);\n" ++
  "cx+=cw;}}}\n" ++
  "draw(node,0,W,2,'R');\n" ++
  "s+='</svg>';\n" ++
  "c.innerHTML=s;\n" ++
  "c.querySelectorAll('rect').forEach(function(el){\n" ++
  "el.addEventListener('mousemove',function(e){\n" ++
  "var n=getN(cur,el.dataset.p);if(!n)return;\n" ++
  "var st=n.dur-n.children.reduce(function(a,b){return a+b.dur},0);\n" ++
  "tt.textContent=n.cls+'\\n'+n.msg+'\\nDuration: '+" ++
  "(n.dur*1000).toFixed(2)+'ms\\nSelf: '+(st*1000).toFixed(2)+'ms';\n" ++
  "tt.style.display='block';tt.style.left=(e.clientX+12)+'px';" ++
  "tt.style.top=(e.clientY+12)+'px';});\n" ++
  "el.addEventListener('mouseout',function(){tt.style.display='none';});\n" ++
  "el.addEventListener('click',function(){\n" ++
  "var n=getN(cur,el.dataset.p);\n" ++
  "if(n&&n.children.length>0){cur=n;render(n);}});});}\n" ++
  "function getN(r,p){\n" ++
  "if(!p||p==='R')return r;\n" ++
  "var ps=p.split('.').slice(1);var n=r;\n" ++
  "for(var i=0;i<ps.length;i++){var idx=parseInt(ps[i]);" ++
  "if(!n.children[idx])return null;n=n.children[idx];}\n" ++
  "return n;}\n" ++
  "render(flameData);\n" ++
  "window.addEventListener('resize',function(){render(cur)});\n" ++
  "document.getElementById('flame-reset').addEventListener('click'," ++
  "function(){cur=flameData;render(flameData);});\n" ++
  "})();\n" ++
  -- Goal table sorting JS
  "document.querySelectorAll('.goal-table th').forEach(function(th,idx){\n" ++
  "th.addEventListener('click',function(){\n" ++
  "var table=th.closest('table'),tbody=table.querySelector('tbody');\n" ++
  "var rows=Array.from(tbody.querySelectorAll('tr'));\n" ++
  "var asc=th.classList.contains('sort-asc');\n" ++
  "table.querySelectorAll('th').forEach(function(t){" ++
  "t.classList.remove('sort-asc','sort-desc')});\n" ++
  "th.classList.add(asc?'sort-desc':'sort-asc');\n" ++
  "rows.sort(function(a,b){\n" ++
  "var av=a.cells[idx].textContent,bv=b.cells[idx].textContent;\n" ++
  "var an=parseFloat(av),bn=parseFloat(bv);\n" ++
  "if(!isNaN(an)&&!isNaN(bn))return asc?an-bn:bn-an;\n" ++
  "return asc?av.localeCompare(bv):bv.localeCompare(av);});\n" ++
  "rows.forEach(function(r){tbody.appendChild(r)});});});\n" ++
  -- Fan-out toggle JS
  "function toggleSib(i){var el=document.getElementById('sib-'+i);" ++
  "if(el)el.classList.toggle('hidden');}\n" ++
  -- Existing expand/collapse/search/filter JS
  "function expandAll(){document.querySelectorAll('.tree details').forEach(" ++
  "function(d){d.open=true})}\n" ++
  "function collapseAll(){document.querySelectorAll('.tree details').forEach(" ++
  "function(d){d.open=false})}\n" ++
  "function doSearch(){var q=document.getElementById('search').value.toLowerCase();\n" ++
  "document.querySelectorAll('.node,.leaf').forEach(function(el){\n" ++
  "var msg=(el.dataset.msg||'').toLowerCase();\n" ++
  "if(!q){el.classList.remove('hidden');return}\n" ++
  "if(msg.includes(q)){el.classList.remove('hidden');var p=el.parentElement;\n" ++
  "while(p){if(p.tagName==='DETAILS')p.open=true;p=p.parentElement}}\n" ++
  "})}\n" ++
  "document.querySelectorAll('.cls-filter').forEach(function(cb){\n" ++
  "cb.addEventListener('change',function(){\n" ++
  "var cls=cb.value;var show=cb.checked;\n" ++
  "document.querySelectorAll('[data-cls=\"'+cls+'\"]').forEach(function(el){\n" ++
  "el.classList.toggle('hidden',!show)})})});\n" ++
  "</script>\n</body></html>\n"

/-- Run typeclass synthesis for `className` with tracing enabled and capture
the full search tree. Uses concrete (generic) types with minimal prerequisite
instances, matching the approach in `SynthFailureBenchmarkConcrete`. -/
private def synthSearchGraph (className : Name) (maxHB : Nat) :
    MetaM SynthSearchResult := do
  let env ← getEnv
  let some _ := env.find? className | return {
    className, result := .failure, heartbeats := 0, root := none, nodeCount := 0, maxDepth := 0
  }
  withNewMCtxDepth do
    let info ← getConstInfo className
    let levels := info.levelParams.map Level.param
    let classExpr := mkConst className levels
    let classType ← inferType classExpr
    -- Step 1: Inspect telescope, collect param descriptors and old fvars
    let (oldFvars, paramInfos) ←
      forallTelescopeReducing classType fun params _body => do
        let mut infos : Array (Name × BinderInfo × Expr) := #[]
        for param in params do
          let decl ← param.fvarId!.getDecl
          infos := infos.push (decl.userName, decl.binderInfo, decl.type)
        return (params, infos)
    -- Step 2: Rebuild context outside the telescope, then synthesize with tracing
    let rec go (infos : List (Name × BinderInfo × Expr))
               (newFvars : Array Expr) : MetaM SynthSearchResult := do
      match infos with
      | [] =>
        let target := mkAppN classExpr newFvars
        -- Clear pre-existing traces and enable synthesis tracing
        resetTraceState
        let start ← IO.getNumHeartbeats
        let mut result := SynthResult.failure
        try
          let r ← withOptions (fun opts =>
            let opts := opts.setBool `trace.Meta.synthInstance true
            let opts := opts.setBool `trace.profiler true
            synthInstance.maxHeartbeats.set opts maxHB) do
            trySynthInstance target
          result := match r with
            | .some _ => .success
            | .none   => .failure
            | .undef  => .undef
        catch _ =>
          result := .timeout
        let stop ← IO.getNumHeartbeats
        let heartbeats := stop - start
        -- Build search tree from accumulated traces
        let traces ← getTraces
        let mut roots : Array SynthSearchNode := #[]
        for te in traces.toList do
          if let some node ← ofMessageData te.msg then
            roots := roots.push node
        let root : Option SynthSearchNode :=
          if roots.isEmpty then none
          else if roots.size == 1 then roots[0]?
          else some {
            cls := `root
            msg := "synthesis trace"
            duration := 0
            children := roots
          }
        let nodeCount := root.map (·.countNodes) |>.getD 0
        let maxDepth := root.map (·.depth) |>.getD 0
        return { className, result, heartbeats, root, nodeCount, maxDepth }
      | (name, bi, oldType) :: rest =>
        let n := newFvars.size
        let newType := oldType.replaceFVars (oldFvars.extract 0 n) newFvars
        withLocalDecl name bi newType fun fvar =>
          go rest (newFvars.push fvar)
    go paramInfos.toList #[]

elab "#synth_trace " id:ident hb:(num)? : command => do
  let className ← liftTermElabM <| resolveGlobalConstNoOverload id
  let maxHB := hb.map (·.getNat) |>.getD 40000
  let r ← liftTermElabM <| synthSearchGraph className maxHB
  -- Write JSON and HTML files
  let safeName := className.toString.replace "." "_"
  let jsonPath : System.FilePath := ".lake" / s!"synth_trace_{safeName}.json"
  let htmlPath : System.FilePath := ".lake" / s!"synth_trace_{safeName}.html"
  IO.FS.createDirAll jsonPath.parent.get!
  IO.FS.writeFile jsonPath r.toJson
  IO.FS.writeFile htmlPath r.toHtml
  -- Log summary
  logInfo <| s!"Synth trace for {className}:\n" ++
    s!"  Result: {r.result.toString}\n" ++
    s!"  Heartbeats: {r.heartbeats / 1000}\n" ++
    s!"  Nodes: {r.nodeCount}\n" ++
    s!"  Max depth: {r.maxDepth}\n" ++
    s!"  JSON: {jsonPath}\n" ++
    s!"  HTML: {htmlPath}"

-- Quick test with a simple class
set_option maxHeartbeats 400000 in
#synth_trace Add

set_option maxHeartbeats 800000 in
#synth_trace MeasurableSpace.CountablySeparated 4000
