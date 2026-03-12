# Bridgeland Stability Conditions: Formalization Status

**Branch:** `feat/bridgeland-stability-conditions`
**Repository:** `mattrobball/mathlib4_fork`
**Last updated:** 2026-03-10

---

## Overview

Formalization of Bridgeland's "Stability conditions on triangulated categories" (Annals 2007),
covering Sections 2–7 and the main deformation theorem (Theorem 7.1 / Theorem 1.2).

**10 files, ~11,027 lines total.**

---

## File Inventory

| File | Lines | Sorrys | Description |
|------|-------|--------|-------------|
| `Deformation.lean` | 3365 | 10 | §7: deformation theorem, wPhaseOf, bridgeland_7_1 |
| `Slicing.lean` | 2480 | 0 | §3: HNFiltration, Slicing, Lemma 3.4, toTStructure, ltProp/geProp |
| `StabilityFunction.lean` | 1997 | 0 | §2: StabilityFunction, IsSemistable, hasHN_of_finiteLength |
| `StabilityCondition.lean` | 1617 | 0 | §5-6: StabilityCondition, Lemma 6.4, Thm 1.2 skeleton |
| `IntervalCategory.lean` | 694 | 0 | §4: IntervalCat, two-heart theory, cokernel containment, SkewedStabilityFunction |
| `HeartEquivalence.lean` | 336 | 11 | §5.3: Prop 5.3, Lemma 5.2, HeartStabilityData scaffolding |
| `GrothendieckGroup.lean` | 208 | 0 | K₀, K₀.of, K₀.lift |
| `Strict.lean` | 252 | 0 | §4: IsStrict, QuasiAbelian, StrictShortExact, kernel/cokernel strictness |
| `PostnikovTower.lean` | ~120 | 0 | Postnikov towers, factor extraction |
| `NumericalStability.lean` | ~60 | 0 | Cor 1.3 statement |

---

## Sorry Summary

### Core sorrys (5 in Deformation.lean)

These are the real blockers for completing the deformation theorem.

| # | Name | Line | Description | Depends on |
|---|------|------|-------------|------------|
| 1 | `hom_eq_zero_of_deformedPred` | 6227 | Lemma 7.6: small-gap hom-vanishing | closed on branch |
| 2 | `deformedSlicing.hn_exists` | 6800 | Lemma 7.7: HN in deformed slicing | Phase 3 + sorry #3 |
| 3 | `P_phi_wSemistable_is_deformedPred` | 7363 | Triangle test for deformedPred | Phase 2 (quasi-abelian strict subobjects) |
| 4 | `abelianHN_to_intervalProp` | 5877 | Abelian HN → interval containment | closed on branch |
| 5 | Q(ψ)-subobject finiteness | 8106 | In `bridgeland_7_1` | Sorrys #2-3 resolved first |

**Dependency chain:** #3 → #2; #1 and #4 are now done, and #5 remains deferred until #2-3 land.

### Scaffolding sorrys

- **Deformation.lean** (5 more): `stabilityFunctionOnP` construction sorrys (lines 3033-3109)
- **HeartEquivalence.lean** (11): HeartStabilityData, heart_equiv, P(φ) closure, Prop 5.3
- **Strict.lean** (0): fully proved

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
- [x] `Finite.subobject_of_faithful_preservesMono` — proved (Strict.lean)
- [x] `isStrictMono_kernel` / `isStrictEpi_cokernel` — proved (Strict.lean)
- [ ] `Subobject.IsStrict` predicate on subobjects

### Phase 2: Two-Heart Embedding (Lemma 4.3) — complete

- [x] Left heart embedding: `intervalProp_implies_leftHeart`
- [x] Right heart embedding: `intervalProp_implies_rightHeart`
- [x] One-sided phase bounds: `phiPlus_lt_of_triangle_with_leProp`, `phiMinus_gt_of_triangle_with_gtProp`
- [x] Kernel/image containment: `first_intervalProp_of_triangle`
- [x] Extension closure: `intervalProp_extension_closed`
- [x] Semistable phase bounds: `phiPlus_le_of_semistable_triangle`, `phiMinus_ge_of_semistable_triangle`
- [x] Cokernel containment via right heart: `third_intervalProp_of_triangle`
- [x] Non-strict phase bound: `phiMinus_gt_of_triangle_with_geProp`
- [x] `intervalCat_quasiAbelian`
- [x] Strict SES ↔ triangles correspondence

### Phase 3: Quasi-Abelian HN — complete

- [x] Thin-interval selection / quotient-recursion infrastructure in `Deformation.lean`
- [x] Lemma 7.7 (HN in thin interval categories):
  `SkewedStabilityFunction.hn_exists_in_thin_interval`
- [x] Critical-path quasi-abelian HN step discharged directly in `Deformation.lean`
  rather than via a separate extracted `exists_mdq_quasiAbelian` / `hasHN_quasiAbelian`
  API

### Phase 4: Fill sorrys — in progress

Depends on Phases 1-3.

Current blocker order:

- [ ] #3 `P_phi_wSemistable_is_deformedPred`
- [x] #4 `abelianHN_to_intervalProp`
- [x] #1 `hom_eq_zero_of_deformedPred`
- [ ] #2 `deformedSlicing.hn_exists`
- [ ] #5 Q(ψ)-subobject finiteness (deferred until #2-3 land)

Current Phase 4 atomization:

1. Done: `P_phi_wSemistable_is_deformedPred` now takes the intended abelian
   `W`-semistability in `P(φ)` from `stabilityFunctionOnP`.
2. In progress: the Phase 2 strict-mono / strict-epi interval machinery now yields a
   compiled common-heart decomposition for blocker `#3`:
   - heart quotient `F_H ↠ Q_H`,
   - image triangle `I_H → F → Q_H`,
   - proof that `I_H, Q_H ∈ P(φ)`,
   - thin-interval containment for the shifted residual kernel piece,
   - explicit `W(K) + W(K_err⟦1⟧) = W(I_H)` bookkeeping,
   - compiled `W`-phase window for `K_err⟦1⟧`,
   - exposed octahedral image-factorisation helper plus the explicit heart morphism
     `K → I_H`,
   - the induced common-heart epimorphism `K →> I_H`,
   - the unshifted identity `W(K) = W(K_err) + W(I_H)`,
   - a proof that `I_H` is nonzero.
3. In progress: the blueprint's Node 7.5 inclusion machinery now has the full compiled
   inclusion transport package, not just local support lemmas.
   - the direct thin-interval `W`-phase window for `K`,
   - compiled phase transport lemmas
     `wPhaseOf_le_of_mono_P_phi_semistable` and
     `wPhaseOf_ge_of_epi_P_phi_semistable`.
   - newly compiled boundary-strip helpers
     `wPhaseOf_gt_of_geProp_target`,
     `intervalProp_of_upper_boundary_triangle`, and
     `wPhaseOf_gt_of_upper_boundary_triangle`, which isolate the upper-boundary
     quotient step in the Node 7.5 inclusion argument.
   - newly compiled strict pullback packaging:
     `interval_strictShortExact_pullback_left`,
     `interval_strictShortExact_pullback_right`,
     `interval_fIsKernel_of_strictShortExact`,
     and the full theorem `semistable_of_upper_inclusion`.
   - newly compiled dual lower-endpoint transport:
     `semistable_of_lower_inclusion`.
   - newly compiled full inclusion-case transport:
     `semistable_of_interval_inclusion`.
   - newly compiled converse target-window transport:
     `semistable_of_target_subinterval`.
   - newly compiled arbitrary-envelope transport:
     `semistable_of_target_envelope`, obtained by intersecting source and target
     envelopes and chaining `semistable_of_target_subinterval` with
     `semistable_of_interval_inclusion`.
   - audit result: the remaining terminal `K₀` sign chase in `#3` is actually
     underdetermined. The present `K`, `I_H`, `K_err⟦1⟧`, `Q_H` phase data has direct
     complex-number models, so that tail cannot be closed by more bookkeeping alone.
   - next live gap: replace the old `#3` tail by the faithful one-sided source-envelope
     rewrite. The intended source intervals are `(ψ - ε₀, φ + ε₀)` and
     `(φ - ε₀, ψ + ε₀)`, followed by transport back to `(ψ - ε₀, ψ + ε₀)` via
     `semistable_of_target_subinterval`.
   - newly compiled source-envelope scaffolding in `Deformation.lean`:
     `intervalProp_P_phi_upper_source`, `intervalProp_P_phi_lower_source`,
     `wPhaseOf_eq_upper_source_midpoint_of_mem_P_phi`, and
     `wPhaseOf_eq_lower_source_midpoint_of_mem_P_phi`.
   - audit against the original paper: the faithful `#3` proof should now pivot to
     Bridgeland's **first strict short exact sequence** argument in the thin target
     category, not back to more endpoint-sign bookkeeping.
   - newly compiled API alignment: `P_phi_wSemistable_is_deformedPred` and its immediate
     bridge now explicitly carry `ε₀ < 1 / 8`, which is the bound under which the paper's
     one-sided source envelopes are actually thin.
   - newly compiled faithful API: `Deformation.lean` now has
     `SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable`, which
     packages Bridgeland's Node 7.3 first strict short exact sequence once local thin
     subobject finiteness is available.
   - remaining gap: `#3` still needs a way to supply or bypass that local
     `hFinSub : ∀ Y, Finite (Subobject Y)` input in the one-sided source-envelope proof.
4. Done: `abelianHN_to_intervalProp` is now closed. The proof uses
   `Fin.induction` on the abelian HN chain in `P(φ)`, the compiled single-factor bridges
   `stabilityFunctionOnP_semistable_deformedPred` /
   `stabilityFunctionOnP_semistable_intervalProp`, the new local `stepTriangle`
   heart-admissibility bridge, and `intervalProp_of_triangle` to propagate interval
   containment up the chain.
5. Done: the small-gap branch of `hom_eq_zero_of_deformedPred` is now closed.
   The faithful midpoint-heart proof uses the compiled target-envelope transport on
   both sides, gets `ψ₁ ≤ ψ(im_A(f))` from the left target window, then enlarges the
   right target window by an explicit `δ > 0` so `Q_A` becomes an honest thin-interval
   object and the existing upper-inclusion semistability theorem can deliver
   `ψ(im_A(f)) ≤ ψ₂`.
   The faithful Lemma 7.6 shape is now explicit:
   for `a := (ψ₁ + ψ₂) / 2 - 1 / 2`, work in the heart `A = P((a, a + 1])`,
   factor `f` as `E ↠ im_A(f) ↪ F`, then prove
   `ker_A(f) ∈ P((a, ψ₁ + ε₀))`,
   `im_A(f) ∈ P((ψ₁ - ε₀, ψ₂ + ε₀))`,
   `coker_A(f) ∈ P((ψ₂ - ε₀, a + 1]))`.
   The two target envelopes are therefore
   `P((a, ψ₁ + ε₀))` for `E` and
   `P((ψ₂ - ε₀, a + 1))` for `F`,
   and the image comparison is made in the overlap
   `P((ψ₁ - ε₀, ψ₂ + ε₀))`.
   The compiled theorem now transports `E` and `F` to those faithful target envelopes,
   proves the left-envelope quotient inequality `ψ₁ ≤ ψ(im_A(f))`, proves the
   midpoint-heart window pieces `ker_A(f) ∈ P((a, ψ₁ + ε₀))` and
   `φ⁻(Q_A) > ψ₂ - ε₀`, and closes the target-side inequality by the explicit
   `δ`-enlargement trick on the right envelope.
   New constraint discovered during the audit:
   those target windows are thin only when `ε₀ < 1 / 8`.
   The theorem layer has now been tightened accordingly:
   `hom_eq_zero_of_deformedPred`, `hom_eq_zero_of_deformedGt_deformedLe`,
   `deformedSlicing`, `deformedSlicing_compat`, `sigma_semistable_intervalProp`,
   and `bridgeland_7_1` all now carry the faithful extra `1 / 8` hypothesis.
   Additional boundary discovery: at the endpoint `ψ₁ = ψ₂ + 2 ε₀`, the nominal
   overlap satisfies `ψ₁ - ε₀ = ψ₂ + ε₀`, so the open overlap interval can collapse.
   The closed small-gap proof therefore compares the image through the
   kernel/cokernel half-open target windows inside the midpoint heart, not by assuming
   a pre-existing `Fact (ψ₁ - ε₀ < ψ₂ + ε₀)`.

Current remaining sorry sites in `Deformation.lean`:

- `#2` `deformedSlicing.hn_exists`: line 6813
- `#3` `P_phi_wSemistable_is_deformedPred`: line 7828
- `#5` Q(ψ)-subobject finiteness: line 8106

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
