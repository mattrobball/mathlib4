# Bridgeland Formalization Rules

## Definitions are the foundation — verify them FIRST

Before building on ANY definition, check it against the PRIMARY SOURCE (the actual paper PDF, NOT artifacts, blueprints, or comments in code — those could be lies too). If a definition doesn't match the paper, everything built on it is worthless no matter how well it compiles.

An unfaithful definition can make hard theorems trivially provable while hiding the real difficulty in an unfillable sorry. If something seems too easy, suspect the definitions.

## Follow Bridgeland's proof EXACTLY

- **Refining** (atomizing proofs into smaller lemmas) = GOOD, that's formalization
- **Substituting** (replacing Bridgeland's reasoning with different math) = BAD
- If doing something Bridgeland does NOT say, STOP and ASK the user
- **ALWAYS READ THE PAPER** to confirm proof strategy before implementing

## Shape the API to match the paper's argument structure

The Lean declarations should mirror the logical skeleton of Bridgeland's proofs. Each named step in the paper should become a named declaration. Factor the proof so that the hard mathematical content is isolated into precisely-scoped sorries, and the wiring between steps is mechanical.

Example: for `hn_exists`, the paper has two steps — (1) every σ-semistable object admits a Q(>t)/Q(≤t) truncation triangle, (2) every object does (by σ-HN + octahedral). The API should have separate declarations for Step 1, Step 2, and the composition, so that Step 1 can be proven mechanically while Step 2 carries the sorry for the real content.

## Keep files short and thematically focused

Long files make build-edit-check cycles painfully slow — Lean re-elaborates the entire file on each change. Split early and split by theme. Each file should cover one coherent piece of the argument (e.g., one section of the paper, one major lemma and its helpers). If a file is getting unwieldy, split it before it becomes a problem.

## Building

- If `lake env lean` or `lake build` is slow (>2 min), run `lake exe cache get` first to fetch prebuilt oleans
- **`lake exe runLinter`** is the DEFAULT linter for Mathlib
- `lake exe runLinter <ModuleName>` runs the full suite on a specific module
