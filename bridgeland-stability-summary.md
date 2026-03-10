# Bridgeland Stability Conditions: Formalization Status

**Branch:** `feat/bridgeland-stability-conditions`
**Repository:** `mattrobball/mathlib4_fork`
**Last updated:** 2026-03-09

---

## Overview

Formalization of Bridgeland's "Stability conditions on triangulated categories" (Annals 2007),
covering Sections 2–7 and the main deformation theorem (Theorem 7.1 / Theorem 1.2).

**10 files, ~10,840 lines total.**

---

## File Inventory

| File | Lines | Sorrys | Description |
|------|-------|--------|-------------|
| `Deformation.lean` | 3365 | 10 | §7: deformation theorem, wPhaseOf, bridgeland_7_1 |
| `Slicing.lean` | 2403 | 0 | §3: HNFiltration, Slicing, Lemma 3.4, toTStructure |
| `StabilityFunction.lean` | 1997 | 0 | §2: StabilityFunction, IsSemistable, hasHN_of_finiteLength |
| `StabilityCondition.lean` | 1617 | 0 | §5-6: StabilityCondition, Lemma 6.4, Thm 1.2 skeleton |
| `IntervalCategory.lean` | 584 | 0 | §4: IntervalCat, two-heart theory, SkewedStabilityFunction |
| `HeartEquivalence.lean` | 336 | 11 | §5.3: Prop 5.3, Lemma 5.2, HeartStabilityData scaffolding |
| `GrothendieckGroup.lean` | 208 | 0 | K₀, K₀.of, K₀.lift |
| `Strict.lean` | 152 | 1 | §4: IsStrict, QuasiAbelian, StrictShortExact |
| `PostnikovTower.lean` | ~120 | 0 | Postnikov towers, factor extraction |
| `NumericalStability.lean` | ~60 | 0 | Cor 1.3 statement |

---

## Sorry Summary

### Core sorrys (5 in Deformation.lean)

These are the real blockers for completing the deformation theorem.

| # | Name | Line | Description | Depends on |
|---|------|------|-------------|------------|
| 1 | `hom_eq_zero_of_deformedPred` | 2669 | Lemma 7.6: small-gap hom-vanishing | Phase 2 (two-heart factoring) |
| 2 | `deformedSlicing.hn_exists` | 2908 | Lemma 7.7: HN in deformed slicing | Phase 3 + sorrys #1, #3, #4 |
| 3 | `P_phi_wSemistable_is_deformedPred` | 3168 | Triangle test for deformedPred | Phase 2 (quasi-abelian strict subobjects) |
| 4 | `abelianHN_to_intervalProp` | 3186 | Abelian HN → interval containment | Sorry #3 + admissibility |
| 5 | Q(ψ)-subobject finiteness | 3283 | In `bridgeland_7_1` | Sorrys #1-2 resolved first |

**Dependency chain:** #3 → #4 → #1 → #2; #5 independent but depends on #1-2.

### Scaffolding sorrys

- **Deformation.lean** (5 more): `stabilityFunctionOnP` construction sorrys (lines 3033-3109)
- **HeartEquivalence.lean** (11): HeartStabilityData, heart_equiv, P(φ) closure, Prop 5.3
- **Strict.lean** (1): `Finite.subobject_of_fullyFaithful`

### What is sorry-free

- `Slicing.lean` (2403 lines) — fully proved
- `IntervalCategory.lean` (584 lines) — fully proved
- `StabilityFunction.lean` (1997 lines) — fully proved
- `StabilityCondition.lean` (1617 lines) — fully proved
- `GrothendieckGroup.lean` (208 lines) — fully proved

---

## Implementation Progress

### Phase 1: Foundations — ~70% complete

- [x] `IsStrict`, `IsStrictMono`, `IsStrictEpi` definitions (Strict.lean)
- [x] `QuasiAbelian` class, `StrictShortExact` (Strict.lean)
- [x] Abelian instances: every abelian morphism is strict (Strict.lean)
- [x] `toTStructure_bounded` — proved (Slicing.lean)
- [x] `toTStructure_heart_iff` — proved (Slicing.lean)
- [x] `heart_shortExact_triangle` — proved (HeartEquivalence.lean)
- [x] `IsLocallyFinite` upgraded to structure with `intervalFinite` + `phaseFinite`
- [ ] `Finite.subobject_of_fullyFaithful` — 1 sorry
- [ ] `Subobject.IsStrict` predicate on subobjects
- [ ] `kernel_strictMono_of_strictEpi` / `cokernel_strictEpi_of_strictMono`

### Phase 2: Two-Heart Embedding (Lemma 4.3) — ~50% complete

- [x] Left heart embedding: `intervalProp_implies_leftHeart`
- [x] Right heart embedding: `intervalProp_implies_rightHeart`
- [x] One-sided phase bounds: `phiPlus_lt_of_triangle_with_leProp`, `phiMinus_gt_of_triangle_with_gtProp`
- [x] Kernel/image containment: `first_intervalProp_of_triangle`
- [x] Extension closure: `intervalProp_extension_closed`
- [x] Semistable phase bounds: `phiPlus_le_of_semistable_triangle`, `phiMinus_ge_of_semistable_triangle`
- [ ] Cokernel containment via right heart (requires quasi-abelian theory)
- [ ] `intervalCat_quasiAbelian`
- [ ] Strict SES ↔ triangles correspondence

### Phase 3: Quasi-Abelian HN — not started

- [ ] mdq existence in quasi-abelian finite-length categories
- [ ] HN filtration existence via mdq iteration
- [ ] Lemma 7.7 (HN in thin interval categories)

### Phase 4: Fill sorrys — not started

Depends on Phases 1-3.

---

## Key Mathematical Discoveries

### False theorems (discovered and deleted)

1. **`semistable_of_triangle_in_interval` is FALSE.** Counterexample: elliptic curve,
   triangle `L₁ → F → L₂` with `L₁ ∈ P(φ-ε)`, `F ∈ P(φ)`, `L₂ ∈ P(φ+ε)`.
   The see-saw `Im ≤ 0 + Im ≥ 0 = 0` fails (opposite signs don't force both = 0).

2. **`P_phi_closed_under_subobjects_in_heart` is FALSE.** Same counterexample:
   `O_E ∈ P(1/2)` is a heart-subobject of `F ∈ P(3/4)`.

3. **Cokernel containment in left heart is FALSE.** The Euler sequence on P¹
   (`0 → O(-1) → O² → O(1) → 0`) shows quotients can escape the interval.

**Conclusion:** Quasi-abelian theory (strict SES in P((a,b))) is genuinely needed.
Heart-subobject shortcuts don't work.

### What IS true

- `P_phi_of_heart_triangle`: If K → E → Q → K[1] with E ∈ P(φ), and BOTH K, Q
  have phases ≤ φ (and > φ-1), then K ∈ P(φ) and Q ∈ P(φ). Same-sign terms force = 0.

---

## Completed Proofs (highlights)

- K₀ additivity (including SES in P(φ))
- Sector bounds, arg convexity, phase perturbation estimates
- wPhaseOf infrastructure (indep, neg, add_two, see-saw)
- deformedSlicing construction (closedUnderIso, shift_iff)
- deformedSlicing hom-vanishing (large gap case)
- stabilityFunctionOnP + stabilityFunctionOnP_hasHN
- Lemma 3.4 phase bounds (phiPlus_lt_of_triangle, phiMinus_gt_of_triangle)
- intervalProp_of_postnikovTower (extension closure)
- bridgeland_7_1 distance bound + local finiteness (modulo sorrys)
- P(φ) admissibility, closure lemmas, truncation lemmas

---

## References

- Bridgeland, "Stability conditions on triangulated categories", Annals of Math. 2007
- Schneiders, "Quasi-abelian categories and sheaves", Mém. Soc. Math. Fr. 1999
- See also: [bridgeland-proof-blueprint.md](bridgeland-proof-blueprint.md) (full blueprint)
- See also: [bridgeland-section4-plan.md](bridgeland-section4-plan.md) (current implementation plan)
