# Plan: Unify degree-0 and degree-d monomial coefficient infrastructure

## Context

TwistedCohomology.lean (~928 lines) duplicates ~700-800 lines from StructureSheafCohomology.lean + StructureSheafAcyclicity.lean, with mechanical substitutions (`monomialCoeff` → `monomialCoeffShift`, ring loc → module loc, etc.). The degree-d versions are strictly more general and subsume degree-0 because `GradedModule.shift (𝒜 n R) 0 = 𝒜 n R` **definitionally** (`shift` is an `abbrev`, `Nat.add_zero` and eta reduction are definitional). The ultimate goal is computing H^p(P^n, O(d)) for all d ∈ ℤ, so all API should be stated for general d.

## New dependency chain

```
MonomialDecomposition.lean (UNCHANGED, 968 lines)
    ↓
MonomialCoefficient.lean (NEW, ~650 lines)
    ↓                        ↓
StructureSheafCohomology     TwistedCohomology.lean
(SIMPLIFIED, ~350 lines)     (SIMPLIFIED, ~250 lines)
H^0 ≅ R, embedding/          acyclicity for d ≥ 0
extraction                       ↓
                             StructureSheafAcyclicity.lean
                             (SIMPLIFIED, ~50 lines, d=0 corollary)
```

## Step 1: Add helper to RelativeSimplexComplex.lean (~30 lines)

**File:** `Mathlib/Topology/Sheaves/RelativeSimplexComplex.lean`

Add `relSimplexComplex_get_primitive` — extracts a primitive from an exact K_T. This 15-line pattern is repeated 5 times across the codebase.

```lean
theorem relSimplexComplex_get_primitive (T : Finset (Fin (n + 1)))
    (hexact : (relSimplexComplex T R).ExactAt (p + 1))
    (f : relSimplexCochain T R (p + 1))
    (hf : relSimplexδHom T R (p + 1) f = 0) :
    ∃ g : relSimplexCochain T R p, relSimplexδHom T R p g = f
```

**Build checkpoint:** `lake build Mathlib.Topology.Sheaves.RelativeSimplexComplex`

## Step 2: Create MonomialCoefficient.lean (~650 lines)

**File:** `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/MonomialCoefficient.lean`

**Imports:** `MonomialDecomposition`, `GradedModule.Shift`

Move from TwistedCohomology.lean with renames (drop "Shift" suffix):

| TwistedCohomology name | New name | Lines |
|---|---|---|
| `monomialElemShift` | `monomialElemMod` | ~20 |
| `smulMonomialElemShift` | `smulMonomialElem` | ~25 |
| `monomialCoeffShiftFun` + `_wd` | `monomialCoeffFun` + `_wd` (private) | ~50 |
| `monomialCoeffShift` | `monomialCoeff` | ~20 |
| `monomialCoeffShiftHom` (+ `map_add'`) | `monomialCoeffHom` | ~60 |
| `monomialCoeffShift_self` | `monomialCoeff_self` | ~15 |
| `monomialCoeffShift_ne` | `monomialCoeff_ne` | ~30 |
| `monomialCoeffShift_smulMonomialElemShift` | `monomialCoeff_smulMonomialElem` | ~45 |
| `monomialCoeffShift_coordRestrict` | `monomialCoeff_coordRestrict` | ~120 |
| `monomialCoeffShift_coordRestrict_vanish` | `monomialCoeff_coordRestrict_vanish` | ~70 |
| `monomialCoeffShift_determines_zero` | `monomialCoeff_determines_zero` (requires `hd : 0 ≤ d`) | ~90 |
| `monomialCoeffShift_finite_support` | `monomialCoeff_finite_support` | ~90 |
| `componentHomShift` | `componentHom` | ~15 |
| `componentShift_comm_δ` | `componentHom_comm_δ` | ~30 |

Also move `coeff_shift_coordProdFinsupp_eq_of_pow_eq` from StructureSheafCohomology.lean line 56 (general utility needed by coefficient proofs).

Add bridge lemma:
```lean
theorem monomialCoeff_zero_eq_zeroExpCoeffMod (S : Finset (Fin (n + 1))) :
    (monomialCoeffHom (0 : LaurentExp n) S (negSupport_zero.symm ▸ S.empty_subset) :
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) _ →+ R) =
    zeroExpCoeffMod S
```

All definitions use `{d : ℤ}` implicit, inferred from `(a : LaurentExp n d)`. The module type is `HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S)`.

**Build checkpoint:** `lake build Mathlib.AlgebraicGeometry.ProjectiveSpectrum.MonomialCoefficient`

## Step 3: Simplify TwistedCohomology.lean (928 → ~250 lines)

**File:** `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/TwistedCohomology.lean`

- **Change import** to `MonomialCoefficient` (remove `StructureSheafAcyclicity`)
- **Remove** lines 48-741 (all monomial element/coefficient infrastructure, now in MonomialCoefficient)
- **Keep** lines 744-928: the `algebraicComplex_shift_acyclic_pos` theorem (using new names from MonomialCoefficient)
- **Update** all references: `monomialCoeffShift` → `monomialCoeff`, `componentHomShift` → `componentHom`, etc.
- Use `relSimplexComplex_get_primitive` from Step 1 to simplify the proof

**Build checkpoint:** `lake build Mathlib.AlgebraicGeometry.ProjectiveSpectrum.TwistedCohomology`

## Step 4: Simplify StructureSheafCohomology.lean (943 → ~350 lines)

**File:** `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheafCohomology.lean`

- **Change import** to also include `MonomialCoefficient`

**Remove** (now in MonomialCoefficient):
- Section MonomialCoeffExtraction (lines 48-197): `coeff_shift_...`, ring-level `monomialCoeff`, orthogonality
- Section MonomialCoeffChainMap (lines 336-692): `monomialCoeff_add`, `monomialCoeffHom`, `monomialCoeffMod`, face compat, `componentHom`, `component_comm_δ`
- Section MonomialCoeffInjectivity (lines 694-808): `monomialCoeff_determines_zero`, `monomialCoeffMod_determines_zero`

**Keep and update:**
- `constRingElemHom`, `constModElemHom` (lines 205-229)
- `coordRestrict_constModElem` (line 231)
- `embeddingHom`, `embedding_comm_δ` (lines 253-293)
- `zeroExpCoeffMod_constModElem` (line 296)
- `extraction_embedding_eq`, `extraction_embedding_eq_id` (lines 315-332)
- Bridge: `componentHom_zero_apply` — now references general `componentHom` from MonomialCoefficient
- H^0 section (lines 810-941): update `monomialCoeffMod_determines_zero` → `monomialCoeff_determines_zero (le_refl 0)`, `componentHom` → general version, etc.

**Build checkpoint:** `lake build Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheafCohomology`

## Step 5: Simplify StructureSheafAcyclicity.lean (436 → ~50 lines)

**File:** `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheafAcyclicity.lean`

- **Change import** to `TwistedCohomology` (instead of `StructureSheafCohomology`)
- **Remove** all R-linearity, finite support, kernel vanishing, and the full proof
- **Replace** with one-line corollary:

```lean
theorem algebraicComplex_acyclic_pos (p : ℕ) :
    IsZero ((algebraicComplex n R (𝒜 n R)).homology (p + 1)) :=
  algebraicComplex_shift_acyclic_pos 0 (le_refl 0) p
```

**Build checkpoint:** `lake build Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheafAcyclicity`

## Step 6: Update Mathlib.lean and final build

- Run `lake exe mk_all` to regenerate import files
- Add `MonomialCoefficient` to Mathlib.lean
- Run `lake build` for full verification

## Key design decisions

1. **Naming**: General-d versions use clean names (`monomialCoeff`, `componentHom`). No "Shift" or "Mod" suffix — the type signature disambiguates.
2. **`d` is implicit**: Inferred from `(a : LaurentExp n d)`. Users write `monomialCoeff a S hS x`, not `monomialCoeff d a S hS x`.
3. **Ring-level API deleted**: The ring-level `monomialCoeff` (on `HomogeneousLocalization.Away`) is removed. Everything works at the module level. The `awayRingModuleEquiv` bridge exists in MonomialDecomposition if anyone needs it.
4. **d < 0 is future work**: `GradedModule.shift (𝒜 n R) d.toNat` gives the wrong module for d < 0 (gives structure sheaf instead of O(d)). Proper negative shift requires integer-indexed grading.
5. **Extraction/embedding kept**: Needed for future d < 0 and for H^0 computation.

## Line count summary

| File | Before | After | Delta |
|---|---|---|---|
| RelativeSimplexComplex.lean | ~1354 | ~1384 | +30 |
| MonomialDecomposition.lean | 968 | 968 | 0 |
| MonomialCoefficient.lean | 0 | ~650 | +650 |
| StructureSheafCohomology.lean | 943 | ~350 | -593 |
| StructureSheafAcyclicity.lean | 436 | ~50 | -386 |
| TwistedCohomology.lean | 928 | ~250 | -678 |
| **Total** | 4629 | ~3652 | **-977** |

Net reduction of ~1000 lines while gaining a unified general-d API.

## Verification

After each step, build the specific file to catch errors early. After all steps:
```bash
lake build Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheafAcyclicity
lake build Mathlib.AlgebraicGeometry.ProjectiveSpectrum.TwistedCohomology
```
These transitively build all dependencies. A green build confirms correctness.
