import Mathlib

/-!
# Typeclass Synthesis Failure Benchmark

Enumerates all typeclasses in the Mathlib environment, attempts synthesis on bare
type metavariables, and records the heartbeat cost of each failure.
This provides a regression-tracking mechanism for synthesis failure times.

Results are written as JSON to `.lake/synth_failure_benchmark.json`.
-/

open Lean Meta Elab Command

/-- Attempt typeclass synthesis for `className` on fresh metavariables and return the
heartbeat cost (in raw heartbeats). Returns `0` if the class constant is not found. -/
private def benchSynthFailure (className : Name) (maxHB : Nat) : MetaM Nat := do
  let env ← getEnv
  let some _ := env.find? className | return 0
  withNewMCtxDepth do
    let classExpr ← mkConstWithFreshMVarLevels className
    let classType ← inferType classExpr
    let target ← forallTelescopeReducing classType fun params _body => do
      let mut fvars : Array Expr := #[]
      let mut mvars : Array Expr := #[]
      for param in params do
        let paramType ← inferType param
        let paramType' := paramType.replaceFVars fvars mvars
        let mvar ← mkFreshExprMVar paramType'
        fvars := fvars.push param
        mvars := mvars.push mvar
      return mkAppN classExpr mvars
    let start ← IO.getNumHeartbeats
    try
      withOptions (synthInstance.maxHeartbeats.set · maxHB) do
        let _ ← trySynthInstance target
    catch _ => pure ()
    let stop ← IO.getNumHeartbeats
    return stop - start

/-- Escape a string for use inside a JSON string literal. -/
private def jsonEscapeString (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
    | '\"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | c    => c.toString) ""

/-- Benchmark typeclass synthesis failure costs across all registered classes.
Results are written as JSON to `.lake/synth_failure_benchmark.json` and a short
summary of the top offenders is logged to the build output. -/
elab "#synth_failure_benchmark" : command => do
  let env ← getEnv
  let classState := classExtension.getState env
  let classNames : Array Name :=
    classState.outParamMap.fold (fun (acc : Array Name) name _ => acc.push name) #[]
  let mut results : Array (Name × Nat) := #[]
  for className in classNames do
    let hb ← liftTermElabM <| benchSynthFailure className 400000
    results := results.push (className, hb)
  let sorted := results.qsort (fun a b => a.2 > b.2)
  -- Build JSON
  let mut jsonEntries : Array String := #[]
  for (name, hb) in sorted do
    let hbUser := hb / 1000
    jsonEntries := jsonEntries.push
      s!"    \{\"class\": \"{jsonEscapeString name.toString}\", \"heartbeats\": {hbUser}}"
  let json := "{\n  \"totalClasses\": " ++ toString classNames.size ++
    ",\n  \"results\": [\n" ++
    String.intercalate ",\n" jsonEntries.toList ++
    "\n  ]\n}\n"
  -- Write JSON file
  let outPath : System.FilePath := ".lake" / "synth_failure_benchmark.json"
  IO.FS.createDirAll outPath.parent.get!
  IO.FS.writeFile outPath json
  -- Log a short summary
  let top := sorted[:min 20 sorted.size]
  let mut summary : Array String := #[]
  for (name, hb) in top do
    summary := summary.push s!"  {name} {hb / 1000}"
  logInfo <| "Synth failure benchmark: wrote " ++ toString classNames.size ++
    " classes to " ++ outPath.toString ++ "\nTop 20:\n" ++
    String.intercalate "\n" summary.toList

set_option maxHeartbeats 0 in
#synth_failure_benchmark
