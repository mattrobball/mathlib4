import Mathlib

/-!
# Typeclass Synthesis Failure Benchmark (Concrete Types)

For each registered typeclass, constructs maximally generic opaque type variables
with exactly the minimal instances needed to *state* the class (i.e., the
instance-implicit prerequisites from its type signature). Then attempts synthesis
of the class itself in that context. This captures the realistic expensive failure
mode where Lean traverses large portions of the instance graph before giving up.

Results are written as JSON to `.lake/synth_failure_benchmark_concrete.json`.
-/

open Lean Meta Elab Command

/-- Result of a single synthesis attempt. -/
private inductive SynthResult
  | success   -- `LOption.some`: synthesis found an instance
  | failure   -- `LOption.none`: synthesis explored and gave up
  | undef     -- `LOption.undef`: synthesis got stuck
  | timeout   -- exception (typically heartbeat exhaustion)

private def SynthResult.toString : SynthResult → String
  | .success => "success"
  | .failure => "failure"
  | .undef   => "undef"
  | .timeout => "timeout"

/-- Attempt typeclass synthesis for `className` using generic types with minimal
prerequisite instances. Returns `(heartbeats, result)`.

The approach:
1. Inspect the class's forall telescope to collect param names, binder infos, and types
2. Exit the telescope
3. Rebuild the local context with `withLocalDecl`, preserving binder infos so that
   instance-implicit params become proper local instances visible to the synthesizer
4. Synthesize at the leaf -/
private def benchSynthConcrete (className : Name) (maxHB : Nat) :
    MetaM (Nat × SynthResult) := do
  let env ← getEnv
  let some _ := env.find? className | return (0, .failure)
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
    -- Step 2: Rebuild context outside the telescope, then synthesize
    let rec go (infos : List (Name × BinderInfo × Expr))
               (newFvars : Array Expr) : MetaM (Nat × SynthResult) := do
      match infos with
      | [] =>
        let target := mkAppN classExpr newFvars
        let start ← IO.getNumHeartbeats
        let mut result := SynthResult.failure
        try
          let r ← withOptions (synthInstance.maxHeartbeats.set · maxHB) do
            trySynthInstance target
          result := match r with
            | .some _ => .success
            | .none   => .failure
            | .undef  => .undef
        catch _ =>
          result := .timeout
        let stop ← IO.getNumHeartbeats
        return (stop - start, result)
      | (name, bi, oldType) :: rest =>
        let n := newFvars.size
        let newType := oldType.replaceFVars (oldFvars.extract 0 n) newFvars
        withLocalDecl name bi newType fun fvar =>
          go rest (newFvars.push fvar)
    go paramInfos.toList #[]

/-- Escape a string for use inside a JSON string literal. -/
private def jsonEscapeString (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
    | '\"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | c    => c.toString) ""

/-- Benchmark typeclass synthesis failure costs across all registered classes using
concrete (generic) types with minimal prerequisite instances.
Results are written as JSON and a top-20 summary is logged. -/
elab "#synth_failure_benchmark_concrete" : command => do
  let env ← getEnv
  let classState := classExtension.getState env
  let classNames : Array Name :=
    classState.outParamMap.fold (fun (acc : Array Name) name _ => acc.push name) #[]
  let mut results : Array (Name × Nat × SynthResult) := #[]
  for className in classNames do
    let (hb, res) ← liftTermElabM <| benchSynthConcrete className 400000
    results := results.push (className, hb, res)
  let sorted := results.qsort (fun a b => a.2.1 > b.2.1)
  -- Build JSON
  let mut jsonEntries : Array String := #[]
  for (name, hb, res) in sorted do
    let hbUser := hb / 1000
    jsonEntries := jsonEntries.push
      s!"    \{\"class\": \"{jsonEscapeString name.toString}\", \
          \"heartbeats\": {hbUser}, \"result\": \"{res.toString}\"}"
  let json := "{\n  \"totalClasses\": " ++ toString classNames.size ++
    ",\n  \"results\": [\n" ++
    String.intercalate ",\n" jsonEntries.toList ++
    "\n  ]\n}\n"
  -- Write JSON file
  let outPath : System.FilePath := ".lake" / "synth_failure_benchmark_concrete.json"
  IO.FS.createDirAll outPath.parent.get!
  IO.FS.writeFile outPath json
  -- Log summary
  let top := sorted[:min 20 sorted.size]
  let mut summary : Array String := #[]
  for (name, hb, res) in top do
    summary := summary.push s!"  {name} {hb / 1000} ({res.toString})"
  logInfo <| "Synth failure benchmark (concrete): wrote " ++ toString classNames.size ++
    " classes to " ++ outPath.toString ++ "\nTop 20:\n" ++
    String.intercalate "\n" summary.toList

set_option maxHeartbeats 0 in
#synth_failure_benchmark_concrete
