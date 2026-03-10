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

### Slicing.lean additions (~64 lines added)
- [x] `toTStructure_bounded` — fully proved
- [x] `toTStructure_heart_iff` — fully proved
- [x] `IsLocallyFinite` upgraded to `structure` with `intervalFinite` + `phaseFinite`

**Dependencies**: Independent of each other.

## Phase 2: Two-Heart Embedding Theory (~700 lines) — PARTIALLY COMPLETE

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
8. [ ] **Quasi-abelian**: `intervalCat_quasiAbelian` — NOT YET STARTED
9. [ ] **Strict SES ↔ triangles**: `strictSES_of_distTriang` — NOT YET STARTED

Also added: `SkewedStabilityFunction` definition, `stabilityFunctionOnP` in Deformation.lean.

**Dependencies**: Phase 1.

## Phase 3: Quasi-Abelian HN (~600 lines)

### StabilityFunction.lean or new QuasiAbelianHN.lean (~400 lines)

Following Bridgeland Section 4.4, mirroring the existing `hasHN_of_finiteLength`:

1. **mdq existence** in quasi-abelian finite-length categories
   - `exists_mdq_quasiAbelian`
2. **HN filtration existence** via mdq iteration
   - `hasHN_quasiAbelian`

### Deformation.lean: Lemma 7.7 (~200 lines)

HN filtrations in thin interval categories:
- `hn_exists_in_thin_interval`

**Dependencies**: Phase 2.

## Phase 4: Fill the 5 Sorrys (~830 lines)

### Order (respecting dependencies):

| Order | Sorry | Line | Lines | Depends on |
|-------|-------|------|-------|------------|
| 1 | #5 Q(psi)-subobject finiteness | 3283 | ~80 | Phase 1 (finiteness transfer) |
| 2 | #3 Triangle test | 3168 | ~100 | Phase 2 (quasi-abelian strict subobjects) |
| 3 | #4 abelianHN_to_intervalProp | 3186 | ~150 | Sorry #3 + admissibility |
| 4 | #1 Small-gap hom-vanishing | 2669 | ~150 | Phase 2 (two-heart factoring) |
| 5 | #2 HN existence | 2908 | ~350 | Phase 3 + sorrys #1, #3, #4 |

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

### Sorry #3 (triangle test) — STRATEGY INVALIDATED

**THE PREVIOUS STRATEGY IS WRONG.** Step 3 ("P(φ) closure under subobjects
⟹ K ∈ P(φ)") is **mathematically false**. Counterexample: on an elliptic
curve, O_E ∈ P(1/2) is a heart-subobject of a semistable F ∈ P(3/4).

The see-saw argument fails because Im(Z(K)·rot) ≤ 0 and Im(Z(Q)·rot) ≥ 0
have OPPOSITE SIGNS, so sum = 0 does NOT force both to zero.

**Correct approach**: Use quasi-abelian STRICT subobjects in P((a,b)).
Strict subobjects stay in P((a,b)) by construction. Bridgeland's triangle
test follows from W-semistability in the quasi-abelian category, not from
P(φ)-closure.

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
