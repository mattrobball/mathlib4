# Section 4 Implementation Plan — FOLLOW BRIDGELAND EXACTLY

## NON-NEGOTIABLE CONSTRAINT

**DO NOT SHORTCUT BRIDGELAND'S PROOF STRUCTURE.**

This plan was created after a failed attempt to bypass Section 4 by embedding
interval categories into abelian hearts. External review (Codex) confirmed this
shortcut is **mathematically invalid**:

1. Concatenating per-slice abelian HN does NOT produce valid Q-HN filtrations
   (W-phases interleave across adjacent slices when phi_i - phi_j <= 2*eps0).
2. One heart cannot replace two-heart strict machinery (left heart controls
   ker/im, right heart controls coker/coim — cokernels in the left heart need
   NOT stay in the interval).

**Bridgeland's proof is the result of hard work by a brilliant mathematician.
Shortcutting it is VERY DANGEROUS. Follow the paper's structure faithfully.
Only deviate if a VERY SERIOUS problem arises — and if so, ASK FOR ADVICE
before proceeding. "Being afraid of developing theory" is NOT an excuse to
skip infrastructure.**

### What IS allowed vs what is NOT

**GOOD — Refining natural language math:**
Atomizing Bridgeland's arguments into smaller, more mechanical lemmas is not
just allowed, it is the *point* of formalization. Breaking a paragraph-long
argument into 5 standalone lemmas with clean type signatures makes the proof
more rigorous and more reusable. This is refinement, not substitution.

**BAD — Substituting different reasoning:**
Replacing Bridgeland's proof strategy with a different mathematical argument
(e.g., replacing quasi-abelian HN with abelian-heart HN) is a much bigger red
flag. The original proof was chosen for good reasons. Substitution risks
introducing subtle errors (as happened with the failed shortcut above).

**Rule of thumb:** If you are decomposing what Bridgeland says into smaller
pieces, you are formalizing. If you are doing something Bridgeland does NOT
say, you are substituting — stop and ask.

---

## Overview

~2530 new lines across 4 phases. All 5 sorry signatures are correct — none
need changing. The missing piece is proof infrastructure, not definitions.

## Phase 1: Foundation (~400 lines) — PARTIALLY COMPLETE

### Strict.lean (152 lines, was 120)
- [x] `IsStrict`, `IsStrictMono`, `IsStrictEpi` definitions
- [x] `QuasiAbelian` class
- [x] `StrictShortExact` structure
- [x] Abelian instances: `isStrict_of_abelian`, `isStrictMono_of_mono`, etc.
- [x] `Finite.subobject_of_faithful_preservesMono` — PROVED (0 sorrys)
- [ ] `Subobject.IsStrict` predicate on subobjects (not yet started)
- [x] `isStrictMono_kernel` / `isStrictEpi_cokernel` — PROVED (no quasi-abelian hyp needed)

### HeartEquivalence.lean (336 lines, was 283)
- [x] `Slicing.toTStructure_bounded` — PROVED (in Slicing.lean)
- [x] `Slicing.toTStructure_heart_iff` — PROVED (in Slicing.lean)
- [x] `TStructure.heart_shortExact_triangle` — PROVED (~80 lines)
- [ ] 8 scaffolding sorrys remain (HeartStabilityData, heart_equiv, etc.)

### Slicing.lean additions (~140 lines added)
- [x] `toTStructure_bounded` — fully proved
- [x] `toTStructure_heart_iff` — fully proved
- [x] `IsLocallyFinite` upgraded to `structure` with `intervalFinite` + `phaseFinite`
- [x] `ltProp` (P(< t)) and `geProp` (P(≥ t)) subcategory predicates
- [x] `phiPlus_lt_of_ltProp` / `phiMinus_ge_of_geProp` extraction lemmas

**Dependencies**: Independent of each other.

## Phase 2: Two-Heart Embedding Theory (~700 lines) — COMPLETE

### IntervalCategory.lean (694 lines, was 191)

This is the core of Bridgeland's Lemma 4.3. For P((a,b)) with b-a < 1:

1. [x] **Left heart embedding**: `intervalProp_implies_leftHeart` — PROVED
2. [x] **Right heart embedding**: `intervalProp_implies_rightHeart` — PROVED
3. [x] **Phase bound lemmas** (one-sided, for triangles):
   - `phiPlus_lt_of_triangle_with_leProp` — PROVED (~50 lines)
   - `phiMinus_gt_of_triangle_with_gtProp` — PROVED (~50 lines, dual)
   - `phiMinus_gt_of_triangle_with_geProp` — PROVED (~70 lines, non-strict variant)
4. [x] **Kernel/image containment**: `first_intervalProp_of_triangle` — PROVED
   - In triangle K → E → Q → K[1] with E ∈ P((a,b)), Q has leProp(a+1),
     K has gtProp(a) ⟹ K ∈ P((a,b))
5. [x] **Extension closure**: `intervalProp_extension_closed` — PROVED
   - In triangle A → E → B → A[1] with A, B ∈ P((a,b)) ⟹ E ∈ P((a,b))
6. [x] **Semistable phase bounds**: `phiPlus_le_of_semistable_triangle`,
   `phiMinus_ge_of_semistable_triangle` — PROVED
7. [x] **Cokernel containment via right heart**: `third_intervalProp_of_triangle` — PROVED
   - In triangle K → E → Q → K[1] with E ∈ P((a,b)), K has geProp(b-1),
     Q has ltProp(b) ⟹ Q ∈ P((a,b))
   - Uses right heart P([b-1, b)) with OPEN right endpoint (key insight)
   - φ⁺(Q) < b: free from ltProp(b); φ⁻(Q) > a: yoneda_exact₃ + K[1] phases ≥ b > a

### Completed Phase 2 items: quasi-abelian interval category and strict SES bridge

Items 1–7 establish the **triangle-level** containment lemmas corresponding to
Schneiders' conditions (a) and (b). These are now wired into a
`QuasiAbelian` instance on `P((a,b))`, and the strict short exact sequence
to distinguished triangle correspondence is proved for thin interval categories.

**Schneiders' criterion (Bridgeland Lemma 4.2):** P((a,b)) is quasi-abelian if
there exist abelian categories A♯, A♭ with fully faithful embeddings such that:
- (a) monos in A♯ with target in P((a,b)) have source in P((a,b))
- (b) epis in A♭ with source in P((a,b)) have target in P((a,b))

The A♯ and A♭ are **existential** — we just need to exhibit them and verify
conditions (a) and (b). The natural choices are:
- A♯ = P((a, a+1]) — left heart of t-structure from P(> a)
- A♭ = P([b-1, b)) — right heart of t-structure from P(≥ b-1)

The "embedding functors" are just full subcategory inclusions — since
P((a,b)) ⊂ A♯ and P((a,b)) ⊂ A♭ by the containment lemmas, the inclusions
are automatic from the `FullSubcategory` structure.

#### 8. Second t-structure and right heart

Done: `toTStructureGE` and the right-heart inclusion `P((a,b)) ⊂ P([b-1,b))`
are implemented, together with the needed `ltProp` / `geProp` support lemmas.

#### 9. Quasi-abelian instance

Done: `P((a,b))` now carries kernels, cokernels, pullbacks, pushouts, and the
instance `intervalCat_quasiAbelian`. The implementation follows the direct
two-heart construction rather than a separate abstract Schneiders theorem.

#### 10. Strict SES ↔ triangles

Done: `exists_distTriang_of_strictShortExact`,
`strictShortExact_of_distTriang`, and
`strictShortExact_iff_exists_distTriang` are proved in
`IntervalCategory.lean`.

Also added: `SkewedStabilityFunction` definition, `stabilityFunctionOnP` in Deformation.lean.

**Dependencies**: Phase 1.

## Phase 3: Quasi-Abelian HN (~600 lines) — COMPLETE

Implemented directly on the critical path in `Deformation.lean`, rather than first
extracting a standalone quasi-abelian HN API in `StabilityFunction.lean`.

Completed deliverables:

1. **Thin-interval selection / quotient recursion**
   - minimal-phase strict-kernel selection
   - strict quotient phase increase
   - strict SES `W`-additivity for HN concatenation
2. **Lemma 7.7**
   - `SkewedStabilityFunction.hn_exists_in_thin_interval`

Optional cleanup left for later, not on the blocker path:

1. Extract generic quasi-abelian finite-length lemmas
   - `exists_mdq_quasiAbelian`
   - `hasHN_quasiAbelian`

**Dependencies**: Phase 2.

## Phase 4: Fill the 5 Sorrys (~830 lines)

### Actual blocker order (current file state, March 11, 2026):

| Order | Sorry | Line | Lines | Depends on |
|-------|-------|------|-------|------------|
| 1 | #3 Triangle test | 7363 | ~470 | Phase 2 (quasi-abelian strict subobjects) |
| 2 | #2 HN existence | 6800 | ~350 | Phase 3 + sorry #3 |
| 3 | #5 Q(psi)-subobject finiteness | 8106 | ~80 | Sorrys #2-3 resolved first |

### Phase 4 atomization

1. **#3 statement cleanup**
   - Done: `P_phi_wSemistable_is_deformedPred` now carries the actual abelian
     `stabilityFunctionOnP` semistability hypothesis in `P(φ)`.
2. **#3 triangle test via strict interval subobjects**
   - Work in the blueprint's Node 7.5 inclusion shape, not a terminal `K₀` sign chase:
     prove interval-independence of `W`-semistability for thin enveloping categories
     and then use that to finish the deformed-predicate triangle test.
   - Immediate target theorem: `Semistable_interval_indep_enveloped` for
     `(a₁, b₁) ⊂ (a₂, b₂)` with `aᵢ + ε₀ ≤ ψ ≤ bᵢ - ε₀`.
   - Done: the common-heart factorization is now compiled through the heart quotient
     `F_H ↠ Q_H`, the image triangle `I_H → F → Q_H`, and the proof that
     `I_H, Q_H ∈ P(φ)`.
   - Done: the proof now also contains the explicit `K₀`/`W` identity
     `W(K) + W(K_err⟦1⟧) = W(I_H)` and the thin-interval `W`-phase window for the
     shifted residual term `K_err⟦1⟧`.
   - Done: the heart-side phase transport lemmas are now compiled on both sides:
     `wPhaseOf_le_of_mono_P_phi_semistable` for `I_H ↪ F` and
     `wPhaseOf_ge_of_epi_P_phi_semistable` for `F ↠ Q_H`.
   - Done: the octahedral image-factorisation helper is now exposed in
     `AbelianSubcategory`, and blocker `#3` now contains the explicit heart
     factorisation morphism `K → I_H` rather than only the derived `K₀` relation.
   - Done: the same octahedral package now gives the actual common-heart epi
     `K →> I_H`, the unshifted identity `W(K) = W(K_err) + W(I_H)`, a proof that
     `I_H` is nonzero, and the direct thin-interval `W`-phase window for `K`.
   - Done: the first Node 7.5 boundary-strip support lemmas are now compiled in
     `Deformation.lean`:
     `wPhaseOf_gt_of_geProp_target`,
     `intervalProp_of_upper_boundary_triangle`, and
     `wPhaseOf_gt_of_upper_boundary_triangle`.
     These isolate the paper's "`B₁` lies on the upper boundary strip, hence
     `phase(B₁) > ψ`" step in the inclusion-case proof.
   - Done: the pullback square is now packaged into the two strict short exact
     sequences from Bridgeland Lemma 7.5:
     `0 → K → pb(B₁) → B₁ → 0` and `0 → pb(B₁) → E → B₂ → 0`.
   - Done: the compiled theorem `semistable_of_upper_inclusion` now closes the
     upper-endpoint inclusion case `P((a, b₁)) ⊂ P((a, b₂))`.
   - Done: `interval_fIsKernel_of_strictShortExact` packages the non-balanced kernel
     recovery for strict short exact sequences in thin interval categories, which the
     inclusion proof needed.
   - Done: the dual lower-endpoint transport is now compiled as
     `semistable_of_lower_inclusion`, and the full inclusion-case Node 7.5 transport is
     packaged as `semistable_of_interval_inclusion`.
   - Done: the converse transport into a thinner target window is now also packaged as
     `semistable_of_target_subinterval`; this closes the missing midpoint-transport
     bookkeeping for future reuse in the blocker proofs.
   - Next atom: use the compiled inclusion theorem to replace the remaining ad hoc tails
     in blockers `#3` and `#1`.
   - Replaced plan: use the compiled common-heart / pullback / quotient infrastructure as
     support lemmas for the interval-independence proof. The previous "last contradiction"
     route is not strong enough on its own.
   - Audit result: the current terminal `K`, `I_H`, `K_err⟦1⟧`, `Q_H` phase inequalities
     are genuinely underdetermined; they admit direct complex-number models, so no
     further terminal sign chase should be attempted.
   - Current faithful rewrite: treat `#3` by the paper's one-sided source envelopes
     `(ψ - ε₀, φ + ε₀)` and `(φ - ε₀, ψ + ε₀)`, prove semistability there via the
     heart/pullback argument, then transport back to `(ψ - ε₀, ψ + ε₀)` with
     `semistable_of_target_subinterval`.
   - Done: `Deformation.lean` now has the first source-envelope scaffolding for that
     rewrite:
     `intervalProp_P_phi_upper_source`, `intervalProp_P_phi_lower_source`,
     `wPhaseOf_eq_upper_source_midpoint_of_mem_P_phi`, and
     `wPhaseOf_eq_lower_source_midpoint_of_mem_P_phi`.
   - Audit against Bridgeland's original Lemma 7.5/7.6 proof: the paper-faithful
     `#3` closure is not another terminal triangle-test squeeze. It should run through
     the **first strict short exact sequence** in the thin target category, exactly as
     Node 7.3 says, and then compare its image in `P(φ)` to the abelian
     `stabilityFunctionOnP` semistability of `F`.
   - Done: the `#3` bridge API itself now carries the paper's `ε₀ < 1/8` slack, so the
     documented one-sided source envelopes are genuinely thin in the formalization.
   - Done: `Deformation.lean` now has an explicit thin-category first-SES wrapper,
     `SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable`, which
     packages the Node 7.3 output once a local `hFinSub` hypothesis is supplied.
   - Remaining faithful gap: the open issue is no longer the shape of the first strict SES,
     but how to feed it into `#3`. The bridge still needs either:
     1. a local derivation of the needed `hFinSub : ∀ Y, Finite (Subobject Y)` for the
        relevant target/source envelopes from the paper's `ε₀` choice, or
     2. a direct `P(φ)`-based contradiction that bypasses a fully generic `hFinSub`.
3. **#4 abelian HN bridge**
   - Done: `abelianHN_to_intervalProp` is now closed.
   - The proof uses `stabilityFunctionOnP_hasHN`, the single-factor bridges
     `stabilityFunctionOnP_semistable_deformedPred` /
     `stabilityFunctionOnP_semistable_intervalProp`, a local heart-admissibility
     `stepTriangle`, and `Fin.induction` on the abelian HN chain to propagate
     `Q.intervalProp` up to the top object.
4. **#1 small-gap hom-vanishing**
   - Done: the small-gap branch now has a compiled common-heart entry point:
     helper lemmas transport phase-confinement bounds into a shared heart
     `P((a,a+1])`, and the branch now constructs the ambient heart image factorisation
     `E_H ↠ I_H ↪ F_H`.
   - Done: the interval-independence layer now has a compiled general
     `semistable_of_target_envelope` transport theorem, obtained by intersecting the
     source and target envelopes and chaining the previously finished inclusion/subinterval
     lemmas.
   - Done: the Node 7.6 / deformed-slicing theorem layer now explicitly carries the
     faithful extra hypothesis `ε₀ < 1/8`, so the midpoint-heart rewrite can use the
     paper's target-window geometry without a fake `1/4 ⇒ 1/8` derivation.
   - Done: the faithful target-envelope transport now actually appears in the small-gap
     proof. `E` is transported to `P((a, ψ₁ + ε₀))`, `F` to `P((ψ₂ - ε₀, a + 1))`,
     the left-envelope quotient inequality `ψ₁ ≤ ψ(im_A(f))` is compiled, and the
     midpoint-heart window lemmas `K_A ∈ P((a, ψ₁ + ε₀))` and
     `φ⁻(Q_A) > ψ₂ - ε₀` are compiled.
   - Done: the small-gap proof is now fully closed. The target-side image inequality is
     discharged by a paper-faithful half-open-window move: enlarge the right target
     envelope by an explicit `δ > 0`, transport `F`-semistability to
     `P((ψ₂ - ε₀, a + 1 + δ))`, upgrade `Q_A` from the half-open window
     `((ψ₂ - ε₀, a + 1]]` to that honest interval, and then apply the compiled
     upper-inclusion semistability theorem plus `wPhaseOf` upper-inclusion independence
     to get `ψ(im_A(f)) ≤ ψ₂`.
   - Important boundary note: at the endpoint `ψ₁ = ψ₂ + 2 ε₀`, one has
     `ψ₁ - ε₀ = ψ₂ + ε₀`, so the overlap interval from the paper can degenerate.
     The closed Lean proof therefore recovers the image comparison from the kernel and
     cokernel half-open windows inside the common heart, not by prematurely inserting a
     `Fact (ψ₁ - ε₀ < ψ₂ + ε₀)`.
5. **#2 deformed slicing HN**
   - Finish the `hn_exists` field from sigma-HN plus the Phase 3 thin-interval HN recursion.
6. **#5 local finiteness**
   - Leave until #1-2 are done; the correct route goes through the constructed deformed
     slicing, not through naive subobject injection.

### Sorry #1 (small-gap hom-vanishing) — correct strategy:
1. Assume `0 < ψ₁ - ψ₂ ≤ 2 ε₀` and set
   `a := (ψ₁ + ψ₂) / 2 - 1 / 2`.
   The common abelian heart is then `A = P((a, a + 1])`.
2. Use phase confinement plus `ψ₁ - ψ₂ ≤ 2 ε₀` to place both `E` and `F` in `A`,
   then factor `f` in `A` as
   `E ↠ im_A(f) ↪ F`
   with kernel `K_A` and cokernel `Q_A`.
3. Prove the paper's exact interval statements from Lemma 3.4:
   `K_A ∈ P((a, ψ₁ + ε₀))`,
   `im_A(f) ∈ P((ψ₁ - ε₀, ψ₂ + ε₀))`,
   `Q_A ∈ P((ψ₂ - ε₀, a + 1]))`.
4. Transport `E` to the thin target envelope `P((a, ψ₁ + ε₀))` and `F` to the thin
   target envelope `P((ψ₂ - ε₀, a + 1))` using the completed Node 7.5
   interval-independence machinery.
5. Apply semistability in those two target envelopes to the heart image triangles:
   `K_A → E → im_A(f) → K_A[1]`
   and
   `im_A(f) → F → Q_A → im_A(f)[1]`.
   This gives `ψ₁ ≤ ψ(im_A(f))` from the first triangle and `ψ(im_A(f)) ≤ ψ₂`
   from the second.
   Status: closed on branch. The second inequality is obtained by enlarging the right
   target envelope by an explicit `δ > 0`, transporting `F`-semistability to that
   larger open interval, and then applying the transported triangle test to
   `im_A(f) → F → Q_A`.
6. Tighten the wrapper API to the paper's `ε₀ < 1/8`.
   This is not cosmetic: the two target windows have widths
   `ψ₁ + ε₀ - a` and `a + 1 - (ψ₂ - ε₀)`, and their thinness condition
   `width + 2 ε₀ < 1` is exactly where the `1 / 8` bound is used.
   Status update: the theorem layer around `hom_eq_zero_of_deformedPred`,
   `hom_eq_zero_of_deformedGt_deformedLe`, `deformedSlicing`,
   `deformedSlicing_compat`, `sigma_semistable_intervalProp`, and
   `bridgeland_7_1` now carries this extra hypothesis in the code.

### Sorry #2 (HN existence) — correct strategy (Bridgeland 7.7-7.9):
1. Take sigma-HN filtration of E
2. For each sigma-factor, embed in thin interval category
3. Apply quasi-abelian HN (Phase 3) in thin interval — NOT per-slice abelian HN
4. Assemble via PostnikovTower concatenation

### Sorry #3 (triangle test) — updated plan

**THE PREVIOUS STRATEGY IS WRONG.** Step 3 ("P(φ) closure under subobjects
⟹ K ∈ P(φ)") is **mathematically false**. Counterexample: on an elliptic
curve, O_E ∈ P(1/2) is a heart-subobject of a semistable F ∈ P(3/4).

The see-saw argument fails because Im(Z(K)·rot) ≤ 0 and Im(Z(Q)·rot) ≥ 0
have OPPOSITE SIGNS, so sum = 0 does NOT force both to zero.

**Current plan**:
1. The theorem statement fix is done: the hypothesis is the abelian
   `stabilityFunctionOnP` semistability in `P(φ)`.
2. The thin-interval/common-heart bridge is partially done: the proof now constructs
   the heart quotient `F_H ↠ Q_H`, the image triangle `I_H → F → Q_H`, and proves
   `I_H, Q_H ∈ P(φ)`.
3. The remaining step is the actual W-phase inequality:
   - get `W(K) = W(I_H) + W(K_err)` from the original triangle plus the heart triangles,
   - Done: `wPhaseOf(W(I_H), ψ) ≤ ψ` is now transported from abelian semistability.
   - Done: the quotient-side bound `ψ ≤ wPhaseOf(W(Q_H), ψ)` is also available.
   - Remaining: combine those with the residual-term window to force the last
     sign contradiction.
   - conclude `wPhaseOf(W(K), ψ) ≤ ψ` by the imaginary-part / see-saw argument.

### Sorry #4 (abelianHN_to_intervalProp):
Closed on the branch.

### Sorry #5 (Q(psi)-subobject finiteness) — NEEDS RETHINKING

The previous strategy ("faithful inclusion ⟹ subobject injection") is
problematic: a full subcategory inclusion does NOT preserve monomorphisms
(full-subcategory-monos are weaker than ambient-monos). So Q(ψ)-subobjects
may be MORE numerous than C-subobjects.

Correct approach likely requires: Q(ψ) is abelian (via Q's t-structure +
Lemma 5.2) with finite length (from σ's local finiteness + phase confinement).
This depends on sorrys 1-2 being resolved first.

## Dependency Graph

```
Phase 1: Strict.lean + HeartEquivalence foundations
    |
    v
Phase 2: IntervalCategory.lean two-heart theory (Lemma 4.3)
    |  COMPLETE
    |
    +---> Sorry #5 (finiteness, independent)
    +---> Sorry #3 (triangle test)
    |
    +---> Sorry #1 (small-gap hom-vanishing)
    |
    v
Phase 3: Quasi-abelian HN (Lemma 7.7)
    |
    v
Sorry #2 (HN existence) [depends on #1, #3 + Phase 3]
```

## What Does NOT Need Rewriting

- `deformedPred` definition (line 2573) — correct
- `SkewedStabilityFunction.Semistable` triangle test (line 478) — correctly encodes strict-subobject semistability
- `deformedSlicing` construction (line ~2750) — correct
- Phase confinement, sector bounds, distance estimates — all sorry-free and correct
- P_phi_abelian (line 2557) — correct, useful as auxiliary
- All 5 sorry signatures — correct, no changes needed

## Key Insight: Two Hearts with Complementary Endpoints

The two hearts have **complementary** half-open intervals:
- Left heart A♯ = P((a, a+1]) — open at a, closed at a+1
- Right heart A♭ = P([b-1, b)) — closed at b-1, open at b

This is why P((a,b)) is quasi-abelian but NOT abelian: no single heart
controls both kernels and cokernels. The left heart's cokernels can escape
P((a,b)) (phases up to a+1 > b), and the right heart's kernels can escape
(phases down to b-1 < a). But:
- Kernels in the LEFT heart stay in P((a,b)) (first_intervalProp_of_triangle)
- Cokernels in the RIGHT heart stay in P((a,b)) (third_intervalProp_of_triangle)

The `QuasiAbelian` instance uses both hearts together.
