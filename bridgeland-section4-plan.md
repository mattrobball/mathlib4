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
| 1 | #3 Triangle test | 5034 | ~220 | Phase 2 (quasi-abelian strict subobjects) |
| 2 | #4 abelianHN_to_intervalProp | 5250 | ~150 | Sorry #3 + admissibility |
| 3 | #1 Small-gap hom-vanishing | 4384 | ~150 | Phase 2 (two-heart factoring) |
| 4 | #2 HN existence | 4668 | ~350 | Phase 3 + sorrys #1, #3, #4 |
| 5 | #5 Q(psi)-subobject finiteness | 5352 | ~80 | Sorrys #1-2 resolved first |

### Phase 4 atomization

1. **#3 statement cleanup**
   - Done: `P_phi_wSemistable_is_deformedPred` now carries the actual abelian
     `stabilityFunctionOnP` semistability hypothesis in `P(φ)`.
2. **#3 triangle test via strict interval subobjects**
   - Work in the thin interval `(ψ - ε₀, ψ + ε₀)`.
   - Use Phase 2: distinguished triangle `↔` strict SES in `P((a,b))`.
   - Done: the common-heart factorization is now compiled through the heart quotient
     `F_H ↠ Q_H`, the image triangle `I_H → F → Q_H`, and the proof that
     `I_H, Q_H ∈ P(φ)`.
   - Done: the proof now also contains the explicit `K₀`/`W` identity
     `W(K) + W(K_err⟦1⟧) = W(I_H)` and the thin-interval `W`-phase window for the
     shifted residual term `K_err⟦1⟧`.
   - Done: the heart-side phase transport lemmas are now compiled on both sides:
     `wPhaseOf_le_of_mono_P_phi_semistable` for `I_H ↪ F` and
     `wPhaseOf_ge_of_epi_P_phi_semistable` for `F ↠ Q_H`.
   - Remaining: use those inequalities to place the residual kernel term on the
     correct side of `ψ`, then close the final contradiction proving
     `wPhaseOf(W(K), ψ) ≤ ψ`.
3. **#4 abelian HN bridge**
   - Use `stabilityFunctionOnP_hasHN`.
   - Send each abelian factor to `deformedPred` via #3.
   - Build the ambient Postnikov tower via admissibility / `appendFactor`.
4. **#1 small-gap hom-vanishing**
   - Reuse the common-heart factorization already outlined, now with #3/#4 available.
5. **#2 deformed slicing HN**
   - Finish the `hn_exists` field from sigma-HN plus the Phase 3 thin-interval HN recursion.
6. **#5 local finiteness**
   - Leave until #1-2 are done; the correct route goes through the constructed deformed
     slicing, not through naive subobject injection.

### Sorry #1 (small-gap hom-vanishing) — correct strategy:
1. E, F in common heart (eps0 < 1/4 ensures overlap)
2. Factor f as E ->> im(f) --> F in the heart
3. im(f) is strict subobject of F in P((a,b)) => W-phase <= psi2
4. SES ker -> E -> im gives W(E) = W(ker) + W(im)
5. E's W-semistability: W-phase of ker <= psi1
6. See-saw: psi1 <= wPhaseOf(W(im)) <= psi2, contradiction

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
1. Get W-HN in P(phi) from stabilityFunctionOnP_hasHN
2. Each factor satisfies deformedPred via sorry #3
3. Build PostnikovTower from abelian chain via admissibility
4. intervalProp from phase bounds

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
    |  Items 1-7: DONE (triangle-level containment)
    |  Items 8-10: TODO (second t-structure, Schneiders, strict SES)
    |
    +---> Sorry #5 (finiteness, independent)
    +---> Sorry #3 (triangle test)
    |         |
    |         v
    |     Sorry #4 (abelianHN_to_intervalProp)
    |
    +---> Sorry #1 (small-gap hom-vanishing)
    |
    v
Phase 3: Quasi-abelian HN (Lemma 7.7)
    |
    v
Sorry #2 (HN existence) [depends on #1, #3, #4 + Phase 3]
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
