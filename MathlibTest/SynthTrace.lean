import Mathlib

/-!
# Synthesis Search Graph Capture

For a given typeclass, runs synthesis with tracing enabled and captures the full
search tree from the trace output. The tree is converted to a structured
`SynthSearchNode` type and written as JSON.

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
  /-- Wall-clock duration in milliseconds (0 if not recorded). -/
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

elab "#synth_trace " id:ident : command => do
  let className ← liftTermElabM <| resolveGlobalConstNoOverload id
  let r ← liftTermElabM <| synthSearchGraph className 400000
  -- Write JSON file
  let safeName := className.toString.replace "." "_"
  let outPath : System.FilePath := ".lake" / s!"synth_trace_{safeName}.json"
  IO.FS.createDirAll outPath.parent.get!
  IO.FS.writeFile outPath r.toJson
  -- Log summary
  logInfo <| s!"Synth trace for {className}:\n" ++
    s!"  Result: {r.result.toString}\n" ++
    s!"  Heartbeats: {r.heartbeats / 1000}\n" ++
    s!"  Nodes: {r.nodeCount}\n" ++
    s!"  Max depth: {r.maxDepth}\n" ++
    s!"  Wrote: {outPath}"

-- Quick test with a simple class
set_option maxHeartbeats 0 in
#synth_trace Add
