/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.MonomialCoefficient

/-!
# Cohomology of the twisted structure sheaf on projective space

This file proves cohomology vanishing for the twisted structure sheaf
`𝒪(d)` on projective n-space over a commutative ring `R`:

* `Hᵖ(𝒪(d)) = 0` for `p > 0` and `d > -(n+1)` (using `intShift`, covering all `d ≥ 0`
  and the range `-(n+1) < d < 0`)
* `H⁰(𝒪(d)) = 0` for `d < 0` and `n ≥ 1`

The key insight: for each Laurent exponent `a` with `∑ aᵢ = d`, the monomial
component lands in an acyclic relative simplex complex `K_T` where
`T = negSupport(a)`. When `d > -(n+1)`, `T` is always a proper subset of `univ`;
when `d < 0`, `T` is always nonempty. Together these force all components to
vanish via `K_T` acyclicity.

## Main results

* `algebraicComplex_shift_acyclic_pos`: `Hᵖ(𝒪(d)) = 0` for `p > 0` and `d ≥ 0`
* `algebraicComplex_intShift_acyclic_pos`: `Hᵖ(𝒪(d)) = 0` for `p > 0`
  and `d > -(n+1)`
* `algebraicComplex_intShift_H0_zero`: `H⁰(𝒪(d)) = 0` for `d < 0` and `n ≥ 1`

## References

* [Stacks Project, Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)
-/

noncomputable section

open MvPolynomial CategoryTheory CategoryTheory.Limits Finset

namespace AlgebraicGeometry.Proj

universe u

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

private abbrev 𝒜 (n : ℕ) (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

local instance : SetLike.GradedSMul (𝒜 n R) (𝒜 n R) :=
  SetLike.GradedMul.toGradedSMul _

/-! ### Main acyclicity theorem -/

section Acyclicity

set_option maxHeartbeats 400000 in
-- The `algebraicδ` unfolding and `monomialCoeffShift_determines_zero` verification
-- involve large term reductions.
/-- `Hᵖ(algebraicComplex(shift 𝒜 d)) = 0` for `p > 0` and `d ≥ 0`:
the higher cohomology of the twisted structure sheaf `𝒪(d)` vanishes. -/
theorem algebraicComplex_shift_acyclic_pos (d : ℤ) (hd : 0 ≤ d) (p : ℕ) :
    IsZero ((algebraicComplex n R (GradedModule.shift (𝒜 n R) d.toNat)).homology
      (p + 1)) := by
  set 𝓜 := GradedModule.shift (𝒜 n R) d.toNat
  set A := algebraicComplex n R 𝓜
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  have hAd : ∀ j, A.d j (j + 1) = AddCommGrp.ofHom (algebraicδ n R 𝓜 j) :=
    fun j => by simp [A, algebraicComplex]
  rw [HomologicalComplex.exactAt_iff' A p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro f hf
  have hg : (A.sc' p (p + 1) (p + 2)).g = A.d (p + 1) (p + 2) := rfl
  have hfi : (A.sc' p (p + 1) (p + 2)).f = A.d p (p + 1) := rfl
  have hfδ : algebraicδ n R 𝓜 (p + 1) f = 0 := by rw [hg, hAd] at hf; exact hf
  -- For each a : LaurentExp n d, component is a cocycle in K_{negSupport a}
  have hcomp_cocycle : ∀ a : LaurentExp n d,
      _root_.relSimplexδHom a.negSupport R (p + 1)
        (componentHomShift a (p + 1) f) = 0 := by
    intro a; rw [← componentShift_comm_δ a (p + 1) f, hfδ, map_zero]
  -- Key: for d ≥ 0, negSupport a ≠ univ for all a
  have hne_univ : ∀ a : LaurentExp n d, a.negSupport ≠ Finset.univ :=
    fun a => a.negSupport_ne_univ hd
  -- Collect the finite set of nonzero Laurent exponents
  set B : Set (LaurentExp n d) :=
    ⋃ T : {T : Finset (Fin (n + 1)) // T.card = (p + 1) + 1},
      {a : LaurentExp n d | ∃ _ : a.negSupport ⊆ T.1,
        monomialCoeffShift a T.1 (f T) ≠ 0}
  have hB_finite : B.Finite :=
    Set.finite_iUnion fun T => monomialCoeffShift_finite_support T.1 (f T)
  set B_fin := hB_finite.toFinset
  -- For each a, get primitive g_a in K_{negSupport a}
  have hprimitive : ∀ (a : LaurentExp n d), a ∈ B_fin →
      ∃ ga : _root_.relSimplexCochain a.negSupport R p,
        _root_.relSimplexδHom a.negSupport R p ga =
          componentHomShift a (p + 1) f := by
    intro a _
    apply _root_.relSimplexComplex_get_primitive a.negSupport R p
    · by_cases hne : a.negSupport.Nonempty
      · exact (_root_.relSimplexComplex_acyclic a.negSupport R
          hne (hne_univ a)) (p + 1)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        show (_root_.relSimplexComplex a.negSupport R).ExactAt (p + 1)
        rw [hne]; exact _root_.relSimplexComplex_empty_exactAt R p
    · exact hcomp_cocycle a
  -- Choose primitives
  let ga : (a : LaurentExp n d) → _root_.relSimplexCochain a.negSupport R p :=
    fun a => if ha : a ∈ B_fin then (hprimitive a ha).choose else 0
  have hga_spec : ∀ (a : LaurentExp n d) (ha : a ∈ B_fin),
      _root_.relSimplexδHom a.negSupport R p (ga a) =
        componentHomShift a (p + 1) f := by
    intro a ha
    show _root_.relSimplexδHom a.negSupport R p
      (if h : a ∈ B_fin then (hprimitive a h).choose else 0) = _
    rw [dif_pos ha]; exact (hprimitive a ha).choose_spec
  have hga_outside : ∀ a, a ∉ B_fin → ga a = 0 := by
    intro a ha
    show (if h : a ∈ B_fin then _ else 0) = 0
    rw [dif_neg ha]
  have hcomp_zero_outside : ∀ (a : LaurentExp n d), a ∉ B_fin →
      componentHomShift a (p + 1) f = 0 := by
    intro a ha
    ext ⟨T, hT, hns⟩
    simp only [componentHomShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
    by_contra hne
    apply ha
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨T, hT⟩, hns, hne⟩
  have hga_spec_all : ∀ a : LaurentExp n d,
      _root_.relSimplexδHom a.negSupport R p (ga a) =
        componentHomShift a (p + 1) f := by
    intro a
    by_cases ha_mem : a ∈ B_fin
    · exact hga_spec a ha_mem
    · rw [hga_outside a ha_mem, map_zero]
      exact (hcomp_zero_outside a ha_mem).symm
  -- Construct the primitive using smulMonomialElemShift
  refine ⟨fun ⟨S, hS⟩ =>
    B_fin.sum fun a =>
      if h : a.negSupport ⊆ S then
        smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h
      else 0, ?_⟩
  -- Verify δG = f using orthogonality and injectivity of monomialCoeffShift
  rw [hfi, hAd]
  show algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h
        else 0) = f
  funext ⟨T, hT⟩
  suffices h : algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h
        else 0) ⟨T, hT⟩ - f ⟨T, hT⟩ = 0 from sub_eq_zero.mp h
  apply monomialCoeffShift_determines_zero hd
  intro b hb
  show (monomialCoeffShiftHom b T) _ = 0
  rw [map_sub]
  have h_lhs : (monomialCoeffShiftHom b T) (algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h
        else 0) ⟨T, hT⟩) =
    componentHomShift b (p + 1) (algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h
        else 0)) ⟨T, hT, hb⟩ := rfl
  rw [h_lhs, componentShift_comm_δ b p]
  have h_rhs : (monomialCoeffShiftHom b T) (f ⟨T, hT⟩) =
      componentHomShift b (p + 1) f ⟨T, hT, hb⟩ := rfl
  rw [h_rhs]
  suffices hcomp_eq : componentHomShift b p
      (fun ⟨S, hS⟩ => B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h
        else 0) = ga b by
    rw [hcomp_eq]; simp [hga_spec_all b]
  ext ⟨S, hS, hb'⟩
  simp only [componentHomShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  show (monomialCoeffShiftHom b S) _ = _
  rw [map_sum]
  simp_rw [show ∀ (a : LaurentExp n d),
    (monomialCoeffShiftHom b S)
      (if h : a.negSupport ⊆ S then
        smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h
      else 0) =
    if h : a.negSupport ⊆ S then
      monomialCoeffShift b S
        (smulMonomialElemShift (R := R) d hd (ga a ⟨S, hS, h⟩) a S h)
    else 0 from fun a => by split_ifs with h <;> [rfl; exact map_zero _]]
  simp_rw [fun (a : LaurentExp n d) (h : a.negSupport ⊆ S) =>
    monomialCoeffShift_smulMonomialElemShift d hd b a S hb' h
      (ga a ⟨S, hS, h⟩)]
  by_cases hb_mem : b ∈ B_fin
  · rw [Finset.sum_eq_single b]
    · simp only [dif_pos hb', eq_self_iff_true, ↓reduceIte]
    · intro a _ hab; simp [show b ≠ a from Ne.symm hab]
    · intro habs; exact absurd hb_mem habs
  · rw [Finset.sum_eq_zero, hga_outside b hb_mem, Pi.zero_apply]
    intro a ha
    by_cases hns : a.negSupport ⊆ S
    · simp only [dif_pos hns]
      by_cases hab : b = a
      · subst hab; exact absurd ha hb_mem
      · simp [hab]
    · simp [dif_neg hns]

set_option maxHeartbeats 400000 in
-- The proof mirrors `algebraicComplex_shift_acyclic_pos` using `intShift` infrastructure,
-- extending vanishing from `d ≥ 0` to `d > -(n+1)`.
/-- `Hᵖ(algebraicComplex(intShift 𝒜 d)) = 0` for `p > 0` and `d > -(n+1)`:
the higher cohomology of the twisted structure sheaf `𝒪(d)` vanishes for all `d > -(n+1)`. -/
theorem algebraicComplex_intShift_acyclic_pos (d : ℤ)
    (hd : -(↑(n + 1) : ℤ) < d) (p : ℕ) :
    IsZero ((algebraicComplex n R (GradedModule.intShift (𝒜 n R) d)).homology
      (p + 1)) := by
  set 𝓜 := GradedModule.intShift (𝒜 n R) d
  set A := algebraicComplex n R 𝓜
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  have hAd : ∀ j, A.d j (j + 1) = AddCommGrp.ofHom (algebraicδ n R 𝓜 j) :=
    fun j => by simp [A, algebraicComplex]
  rw [HomologicalComplex.exactAt_iff' A p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro f hf
  have hg : (A.sc' p (p + 1) (p + 2)).g = A.d (p + 1) (p + 2) := rfl
  have hfi : (A.sc' p (p + 1) (p + 2)).f = A.d p (p + 1) := rfl
  have hfδ : algebraicδ n R 𝓜 (p + 1) f = 0 := by rw [hg, hAd] at hf; exact hf
  -- Component extraction: each component is a cocycle in K_{negSupport a}
  have hcomp_cocycle : ∀ a : LaurentExp n d,
      _root_.relSimplexδHom a.negSupport R (p + 1)
        (componentHomIntShift a (p + 1) f) = 0 := by
    intro a; rw [← componentIntShift_comm_δ a (p + 1) f, hfδ, map_zero]
  -- Key: for d > -(n+1), negSupport a ≠ univ for all a
  have hne_univ : ∀ a : LaurentExp n d, a.negSupport ≠ Finset.univ :=
    fun a => a.negSupport_ne_univ_of_gt hd
  -- Finite set of nonzero Laurent exponents
  set B : Set (LaurentExp n d) :=
    ⋃ T : {T : Finset (Fin (n + 1)) // T.card = (p + 1) + 1},
      {a : LaurentExp n d | ∃ _ : a.negSupport ⊆ T.1,
        monomialCoeffIntShift a T.1 (f T) ≠ 0}
  have hB_finite : B.Finite :=
    Set.finite_iUnion fun T => monomialCoeffIntShift_finite_support T.1 (f T)
  set B_fin := hB_finite.toFinset
  -- Get primitive for each a
  have hprimitive : ∀ (a : LaurentExp n d), a ∈ B_fin →
      ∃ ga : _root_.relSimplexCochain a.negSupport R p,
        _root_.relSimplexδHom a.negSupport R p ga =
          componentHomIntShift a (p + 1) f := by
    intro a _
    apply _root_.relSimplexComplex_get_primitive a.negSupport R p
    · by_cases hne : a.negSupport.Nonempty
      · exact (_root_.relSimplexComplex_acyclic a.negSupport R
          hne (hne_univ a)) (p + 1)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        show (_root_.relSimplexComplex a.negSupport R).ExactAt (p + 1)
        rw [hne]; exact _root_.relSimplexComplex_empty_exactAt R p
    · exact hcomp_cocycle a
  -- Choose primitives
  let ga : (a : LaurentExp n d) → _root_.relSimplexCochain a.negSupport R p :=
    fun a => if ha : a ∈ B_fin then (hprimitive a ha).choose else 0
  have hga_spec : ∀ (a : LaurentExp n d) (ha : a ∈ B_fin),
      _root_.relSimplexδHom a.negSupport R p (ga a) =
        componentHomIntShift a (p + 1) f := by
    intro a ha
    show _root_.relSimplexδHom a.negSupport R p
      (if h : a ∈ B_fin then (hprimitive a h).choose else 0) = _
    rw [dif_pos ha]; exact (hprimitive a ha).choose_spec
  have hga_outside : ∀ a, a ∉ B_fin → ga a = 0 := by
    intro a ha
    show (if h : a ∈ B_fin then _ else 0) = 0
    rw [dif_neg ha]
  have hcomp_zero_outside : ∀ (a : LaurentExp n d), a ∉ B_fin →
      componentHomIntShift a (p + 1) f = 0 := by
    intro a ha
    ext ⟨T, hT, hns⟩
    simp only [componentHomIntShift, AddMonoidHom.mk'_apply, Pi.zero_apply]
    by_contra hne
    apply ha
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨T, hT⟩, hns, hne⟩
  have hga_spec_all : ∀ a : LaurentExp n d,
      _root_.relSimplexδHom a.negSupport R p (ga a) =
        componentHomIntShift a (p + 1) f := by
    intro a
    by_cases ha_mem : a ∈ B_fin
    · exact hga_spec a ha_mem
    · rw [hga_outside a ha_mem, map_zero]
      exact (hcomp_zero_outside a ha_mem).symm
  -- Construct the primitive using smulMonomialElemIntShift
  refine ⟨fun ⟨S, hS⟩ =>
    B_fin.sum fun a =>
      if h : a.negSupport ⊆ S then
        smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
      else 0, ?_⟩
  -- Verify δG = f using orthogonality and injectivity
  rw [hfi, hAd]
  show algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
        else 0) = f
  funext ⟨T, hT⟩
  suffices hsub : algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
        else 0) ⟨T, hT⟩ - f ⟨T, hT⟩ = 0 from sub_eq_zero.mp hsub
  apply monomialCoeffIntShift_determines_zero
  intro b hb
  show (monomialCoeffIntShiftHom b T) _ = 0
  rw [map_sub]
  have h_lhs : (monomialCoeffIntShiftHom b T) (algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
        else 0) ⟨T, hT⟩) =
    componentHomIntShift b (p + 1) (algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
        else 0)) ⟨T, hT, hb⟩ := rfl
  rw [h_lhs, componentIntShift_comm_δ b p]
  have h_rhs : (monomialCoeffIntShiftHom b T) (f ⟨T, hT⟩) =
      componentHomIntShift b (p + 1) f ⟨T, hT, hb⟩ := rfl
  rw [h_rhs]
  suffices hcomp_eq : componentHomIntShift b p
      (fun ⟨S, hS⟩ => B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
        else 0) = ga b by
    rw [hcomp_eq]; simp [hga_spec_all b]
  ext ⟨S, hS, hb'⟩
  simp only [componentHomIntShift, AddMonoidHom.mk'_apply]
  show (monomialCoeffIntShiftHom b S) _ = _
  rw [map_sum]
  simp_rw [show ∀ (a : LaurentExp n d),
    (monomialCoeffIntShiftHom b S)
      (if h : a.negSupport ⊆ S then
        smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
      else 0) =
    if h : a.negSupport ⊆ S then
      monomialCoeffIntShift b S
        (smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h)
    else 0 from fun a => by split_ifs with h <;> [rfl; exact map_zero _]]
  simp_rw [fun (a : LaurentExp n d) (h : a.negSupport ⊆ S) =>
    monomialCoeffIntShift_smulMonomialElemIntShift a b S h hb'
      (ga a ⟨S, hS, h⟩)]
  by_cases hb_mem : b ∈ B_fin
  · rw [Finset.sum_eq_single b]
    · simp only [dif_pos hb', eq_self_iff_true, ↓reduceIte]
    · intro a _ hab; simp [show b ≠ a from Ne.symm hab]
    · intro habs; exact absurd hb_mem habs
  · rw [Finset.sum_eq_zero, hga_outside b hb_mem, Pi.zero_apply]
    intro a ha
    by_cases hns : a.negSupport ⊆ S
    · simp only [dif_pos hns]
      by_cases hab : b = a
      · subst hab; exact absurd ha hb_mem
      · simp [hab]
    · simp [dif_neg hns]

set_option maxHeartbeats 400000 in
-- H^0(O(d)) = 0 for d < 0 requires n ≥ 1 (for n = 0 the localized module is nonzero).
/-- `H⁰(algebraicComplex(intShift 𝒜 d)) = 0` for `d < 0` and `n ≥ 1`:
global sections of `𝒪(d)` vanish for negative twists on projective `n`-space. -/
theorem algebraicComplex_intShift_H0_zero (d : ℤ) (hd : d < 0) (hn : 0 < n) :
    IsZero ((algebraicComplex n R (GradedModule.intShift (𝒜 n R) d)).homology 0) := by
  set 𝓜 := GradedModule.intShift (𝒜 n R) d
  set A := algebraicComplex n R 𝓜
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' A ((ComplexShape.up ℕ).prev 0) 0 1
    rfl ((ComplexShape.up ℕ).next_eq' rfl), ShortComplex.ab_exact_iff]
  intro f hf
  have hAd : ∀ j, A.d j (j + 1) = AddCommGrp.ofHom (algebraicδ n R 𝓜 j) :=
    fun j => by simp [A, algebraicComplex]
  have hfδ : algebraicδ n R 𝓜 0 f = 0 := by
    have hg : (A.sc' ((ComplexShape.up ℕ).prev 0) 0 1).g = A.d 0 1 := rfl
    rw [hg, hAd 0] at hf; exact hf
  -- For d < 0, every Laurent exponent a has nonempty negSupport, and since
  -- |S| = 1 < n + 1 (using n ≥ 1), negSupport ⊆ S forces negSupport ≠ univ.
  -- So K_{negSupport(a)} is acyclic (nonempty proper T), hence ker(d₀) = 0.
  have hcomp_cocycle : ∀ a : LaurentExp n d,
      _root_.relSimplexδHom a.negSupport R 0
        (componentHomIntShift a 0 f) = 0 := by
    intro a; rw [← componentIntShift_comm_δ a 0 f, hfδ, map_zero]
  -- Show f = 0, then provide the trivial primitive
  suffices hf0 : f = 0 by
    exact ⟨0, by
      rw [show (A.sc' ((ComplexShape.up ℕ).prev 0) 0 1).f = 0 from
        A.shape _ _ (by simp [ComplexShape.up_Rel]), map_zero, hf0]⟩
  funext ⟨S, hS⟩
  apply monomialCoeffIntShift_determines_zero
  intro a ha
  -- negSupport(a) is nonempty (d < 0) and proper (negSupport ⊆ S, |S| = 1 < n + 1)
  have hne : a.negSupport.Nonempty := a.negSupport_nonempty_of_neg hd
  have hne' : a.negSupport ≠ Finset.univ := by
    intro heq; rw [heq] at ha
    have h1 := Finset.card_le_card ha
    rw [Finset.card_univ, Fintype.card_fin] at h1
    linarith [hS]
  have hac := _root_.relSimplexComplex_acyclic a.negSupport R hne hne'
  show componentHomIntShift a 0 f ⟨S, hS, ha⟩ = 0
  suffices hz : componentHomIntShift a 0 f = 0 from congr_fun hz ⟨S, hS, ha⟩
  set K := _root_.relSimplexComplex a.negSupport R
  have hker_le := ((K.sc 0).ab_exact_iff_ker_le_range).mp (hac 0)
  have hf_zero : (K.sc 0).f = 0 :=
    K.shape _ _ (fun h => by simp [ComplexShape.up_Rel] at h)
  have hrange_bot : (K.sc 0).f.hom.range = ⊥ := by
    have : (K.sc 0).f.hom = 0 := congr_arg AddCommGrp.Hom.hom hf_zero
    rw [this]; exact AddMonoidHom.range_zero
  have hg_mem : componentHomIntShift a 0 f ∈ (K.sc 0).g.hom.ker := by
    rw [AddMonoidHom.mem_ker]
    show K.d 0 ((ComplexShape.up ℕ).next 0) (componentHomIntShift a 0 f) = 0
    rw [(ComplexShape.up ℕ).next_eq' (show (0 : ℕ) + 1 = 1 from rfl),
      show K.d 0 1 = AddCommGrp.ofHom
        (_root_.relSimplexδHom a.negSupport R 0) from
        CochainComplex.of_d _ _ _ 0]
    exact hcomp_cocycle a
  rw [hrange_bot] at hker_le
  exact AddSubgroup.mem_bot.mp (hker_le hg_mem)

end Acyclicity

/-! ### H⁰(𝒪(d)) ≅ 𝒜_d for d ≥ 0 -/

section H0Shift

variable (d_nat : ℕ)

local instance : SetLike.GradedSMul (𝒜 n R) (GradedModule.shift (𝒜 n R) d_nat) :=
  GradedModule.shift.gradedSMul (𝒜 n R) (𝒜 n R) d_nat

/-- Embedding of degree-`d` polynomials into the shifted localized module: sends
`f ∈ 𝒜_d` to `f/1` in the degree-shifted localization at `coordProd S`. -/
def polyElemModHom (S : Finset (Fin (n + 1))) :
    ↥((𝒜 n R) d_nat) →+
    HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d_nat) (coordProd n R S) where
  toFun p := HomogeneousLocalizedModule.Away.mk (𝒜 n R)
    (GradedModule.shift (𝒜 n R) d_nat) (coordProd_mem_homogeneous n R S)
    0 p.val (by simp [GradedModule.shift])
  map_zero' := by
    apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R S))
    simp [HomogeneousLocalizedModule.Away.val_mk, HomogeneousLocalizedModule.val_zero,
      LocalizedModule.zero_mk]
  map_add' a b := by
    apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R S))
    rw [HomogeneousLocalizedModule.val_add]
    simp only [HomogeneousLocalizedModule.Away.val_mk]
    rw [LocalizedModule.mk_add_mk]
    congr 1
    · simp [pow_zero]
    · ext; simp [pow_zero]

/-- Face restriction preserves embedded polynomials: restricting `f/1` from a face
to the full simplex yields `f/1` at the full simplex. -/
theorem coordRestrict_polyElemMod {p : ℕ} {T : Finset (Fin (n + 1))}
    (hT : T.card = p + 2) (j : Fin (p + 2)) (f : ↥((𝒜 n R) d_nat)) :
    coordRestrict n R (GradedModule.shift (𝒜 n R) d_nat) T hT j
      (polyElemModHom d_nat (TopCat.eraseNth T hT j).1 f) =
    polyElemModHom d_nat T f := by
  apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R T))
  simp only [polyElemModHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coordRestrict]
  letI := GradedModule.shift.gradedSMul (𝒜 n R) (𝒜 n R) d_nat
  erw [HomogeneousLocalizedModule.awayMap_Away_mk]
  simp only [HomogeneousLocalizedModule.Away.val_mk, pow_zero, one_smul]

/-- The embedding cochain: sends each polynomial `f ∈ 𝒜_d` to the constant cochain
`S ↦ f/1` in the algebraic complex. -/
def polyEmbeddingHom (p : ℕ) :
    ↥((𝒜 n R) d_nat) →+
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R)
        (GradedModule.shift (𝒜 n R) d_nat) (coordProd n R S.1)) :=
  Pi.addMonoidHom fun ⟨S, _⟩ => polyElemModHom d_nat S

/-- The embedded polynomial cochain is a 0-cocycle: `δ₀(f/1, ..., f/1) = 0` because
the alternating sum `∑_j (-1)^j · (f/1) = f/1 - f/1 = 0`. -/
theorem polyEmbedding_cocycle (f : ↥((𝒜 n R) d_nat)) :
    algebraicδ n R (GradedModule.shift (𝒜 n R) d_nat) 0
      (polyEmbeddingHom d_nat 0 f) = 0 := by
  ext ⟨T, hT⟩
  simp only [algebraicδ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, polyEmbeddingHom,
    Pi.addMonoidHom_apply, Pi.zero_apply]
  simp_rw [coordRestrict_polyElemMod d_nat hT _ f]
  rw [Fin.sum_univ_two]
  simp [one_zsmul, neg_one_zsmul, add_neg_cancel]

/-- The polynomial embedding is injective: if `f/1 = 0` at every singleton, then `f = 0`.
Uses regularity of `coordProd S` (a product of variables) to cancel the annihilator
from the localization. -/
theorem polyEmbedding_injective (f : ↥((𝒜 n R) d_nat))
    (h : polyEmbeddingHom d_nat 0 f = 0) : f = 0 := by
  -- Extract f/1 = 0 at the singleton {0}
  have h0 : polyElemModHom d_nat ({(0 : Fin (n + 1))} : Finset _) f = 0 :=
    congr_fun h ⟨{0}, by simp⟩
  -- Get val = 0 in LocalizedModule
  have hval : (polyElemModHom d_nat ({(0 : Fin (n + 1))} : Finset _) f).val = 0 := by
    rw [h0, HomogeneousLocalizedModule.val_zero]
  simp only [polyElemModHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalizedModule.Away.val_mk] at hval
  -- hval : LocalizedModule.mk f.val ⟨coordProd^0, _⟩ = 0
  rw [← LocalizedModule.zero_mk
    (⟨coordProd n R {(0 : Fin (n + 1))} ^ 0, ⟨0, rfl⟩⟩ :
      Submonoid.powers (coordProd n R {(0 : Fin (n + 1))})),
    LocalizedModule.mk_eq] at hval
  obtain ⟨⟨_, k, rfl⟩, hu⟩ := hval
  -- hu : coordProd^k • coordProd^0 • f.val = coordProd^k • coordProd^0 • 0
  -- Simplify to coordProd^k * f.val = 0 and use regularity
  have hmul : coordProd n R {(0 : Fin (n + 1))} ^ k * (↑f : MvPolynomial _ _) = 0 := by
    simp only [Submonoid.smul_def, smul_eq_mul, smul_zero, pow_zero, one_mul] at hu
    exact hu
  have hreg : IsRegular (coordProd n R {(0 : Fin (n + 1))} ^ k) :=
    (MvPolynomial.isRegular_prod_X ({(0 : Fin (n + 1))} : Finset _)).pow k
  exact Subtype.ext (hreg.left (hmul.trans (mul_zero _).symm))

/-! #### Helper lemmas for coefficient extraction from embedded polynomials -/

/-- For a Laurent exponent with empty negSupport, the clearing power is zero. -/
private theorem clearingPow_eq_zero_of_negSupport_empty (a : LaurentExp n (↑d_nat))
    (h : a.negSupport = ∅) (S : Finset (Fin (n + 1))) :
    a.clearingPow S = 0 := by
  simp only [LaurentExp.clearingPow]
  apply (Finset.sup_eq_bot_iff _ S).mpr
  intro i _
  have hi : 0 ≤ a.1 i := (a.negSupport_empty_iff_nonneg.mp h) i
  simp [Int.toNat_eq_zero.mpr (neg_nonpos_of_nonneg hi)]

/-- For a Laurent exponent with empty negSupport, `numFinsupp` is independent of `S`. -/
private theorem numFinsupp_eq_of_negSupport_empty (a : LaurentExp n (↑d_nat))
    (h : a.negSupport = ∅) (S : Finset (Fin (n + 1))) :
    a.numFinsupp S = a.numFinsupp ∅ := by
  ext i
  simp only [LaurentExp.numFinsupp_apply, LaurentExp.numExp]
  rw [clearingPow_eq_zero_of_negSupport_empty d_nat a h S]
  simp [Nat.cast_zero, add_zero]

/-- `coordProdFinsupp S 0 = 0` as a Finsupp. -/
private theorem coordProdFinsupp_zero' (S : Finset (Fin (n + 1))) :
    coordProdFinsupp S 0 = 0 := by
  ext i
  by_cases hi : i ∈ S
  · simp [coordProdFinsupp_apply_mem hi]
  · simp [coordProdFinsupp_apply_notMem hi]

/-- `numFinsupp` for a Laurent exponent with empty negSupport has degree `d_nat`. -/
private theorem numFinsupp_degree_of_negSupport_empty (a : LaurentExp n (↑d_nat))
    (h : a.negSupport = ∅) :
    (a.numFinsupp ∅).degree = d_nat := by
  have hnn := a.negSupport_empty_iff_nonneg.mp h
  simp only [Finsupp.degree]
  rw [Finset.sum_subset (Finset.subset_univ _)
    (fun i _ hi => Finsupp.notMem_support_iff.mp hi)]
  simp only [LaurentExp.numFinsupp_apply, LaurentExp.numExp, Finset.notMem_empty,
    ↓reduceIte]
  exact_mod_cast show (↑(∑ i : Fin (n + 1), (a.1 i).toNat) : ℤ) = (↑d_nat : ℤ) from by
    simp_rw [Nat.cast_sum, Int.toNat_of_nonneg (hnn _)]
    exact_mod_cast a.2

/-- The coefficient extraction of an embedded polynomial at a Laurent exponent with
empty negSupport returns the corresponding polynomial coefficient. -/
private theorem monomialCoeffShift_polyElemMod_of_empty
    (a : LaurentExp n (↑d_nat)) (h : a.negSupport = ∅)
    (S : Finset (Fin (n + 1))) (g : ↥((𝒜 n R) d_nat)) :
    monomialCoeffShift a S (polyElemModHom d_nat S g) =
    MvPolynomial.coeff (a.numFinsupp ∅) g.val := by
  simp only [polyElemModHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  erw [monomialCoeffShift_Away_mk]
  rw [clearingPow_eq_zero_of_negSupport_empty d_nat a h S, pow_zero, one_mul,
    coordProdFinsupp_zero', add_zero,
    numFinsupp_eq_of_negSupport_empty d_nat a h S]

/-- The coefficient extraction of an embedded polynomial at a Laurent exponent with
nonempty negSupport returns zero: polynomial elements have no negative-exponent
components. -/
private theorem monomialCoeffShift_polyElemMod_of_nonempty
    (a : LaurentExp n (↑d_nat)) (h : a.negSupport.Nonempty)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S)
    (g : ↥((𝒜 n R) d_nat)) :
    monomialCoeffShift a S (polyElemModHom d_nat S g) = 0 := by
  simp only [polyElemModHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  erw [monomialCoeffShift_Away_mk]
  rw [coordProdFinsupp_zero', add_zero]
  rw [coordProd_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
  -- Show ¬(coordProdFinsupp S c ≤ numFinsupp a S) because at some i ∈ negSupport,
  -- coordProdFinsupp S c i = c > numFinsupp a S i = (a_i + c).toNat < c
  apply if_neg
  intro hle
  obtain ⟨i, hi⟩ := h
  have hiS : i ∈ S := hS hi
  have hai : a.1 i < 0 := (a.mem_negSupport_iff i).mp hi
  have hle_i := hle i
  simp only [LaurentExp.numFinsupp_apply, LaurentExp.numExp, if_pos hiS,
    coordProdFinsupp_apply_mem hiS] at hle_i
  have hnn : 0 ≤ a.1 i + ↑(a.clearingPow S) := a.clearingPow_nonneg S i hiS
  have hlt : (a.1 i + ↑(a.clearingPow S)).toNat < a.clearingPow S := by
    rw [Int.toNat_lt hnn]; linarith
  linarith

/-! #### Surjectivity and isomorphism -/

set_option maxHeartbeats 400000 in
-- The surjectivity proof constructs a polynomial from the monomial coefficient
-- extraction and verifies equality via `monomialCoeffShift_determines_zero`.
/-- Any 0-cocycle in the algebraic complex with shift `d` (for `d ≥ 0`) is the
embedding of a polynomial in `𝒜_d`. -/
theorem polyEmbedding_surj_cocycle (hd : 0 ≤ (d_nat : ℤ))
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = 0 + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R)
        (GradedModule.shift (𝒜 n R) d_nat) (coordProd n R S.1))
    (hf : algebraicδ n R (GradedModule.shift (𝒜 n R) d_nat) 0 f = 0) :
    ∃ g : ↥((𝒜 n R) d_nat), polyEmbeddingHom d_nat 0 g = f := by
  set S₀ : Finset (Fin (n + 1)) := {0}
  set hS₀ : S₀.card = 0 + 1 := by simp [S₀]
  -- Extract coefficients for each Laurent exponent a with negSupport = ∅
  -- Define r_a = monomialCoeffShift a {0} (f({0}))
  -- Construct g = ∑ monomial(numFinsupp a ∅, r_a) as an element of 𝒜_d
  set B₀ := monomialCoeffShift_finite_support (R := R) (d := ↑d_nat) S₀ (f ⟨S₀, hS₀⟩)
  set A := B₀.toFinset.filter (fun a => a.negSupport = ∅)
  -- Define the polynomial
  set gval : MvPolynomial (Fin (n + 1)) R :=
    A.sum fun a => MvPolynomial.monomial (a.numFinsupp ∅)
      (monomialCoeffShift a S₀ (f ⟨S₀, hS₀⟩))
  -- Show g is homogeneous of degree d_nat
  have hg_mem : gval ∈ 𝒜 n R d_nat := by
    apply Submodule.sum_mem
    intro a ha
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_monomial _ (numFinsupp_degree_of_negSupport_empty
      d_nat a (Finset.mem_filter.mp ha).2)
  set g : ↥((𝒜 n R) d_nat) := ⟨gval, hg_mem⟩
  refine ⟨g, ?_⟩
  -- Show polyEmbeddingHom d_nat 0 g = f at each singleton S
  funext ⟨S, hS⟩
  -- Suffices to show all monomialCoeffShift agree
  rw [← sub_eq_zero]
  apply monomialCoeffShift_determines_zero hd
  intro a ha
  show (monomialCoeffShiftHom a S) _ = 0
  rw [map_sub]
  -- f is a cocycle: componentShift a 0 f is a cocycle in K_{negSupport a}
  have hcomp_cocycle :
      _root_.relSimplexδHom a.negSupport R 0
        (componentHomShift a 0 f) = 0 := by
    rw [← componentShift_comm_δ a 0 f]
    change componentHomShift a 1
      (algebraicδ n R (GradedModule.shift (𝒜 n R) d_nat) 0 f) = 0
    rw [hf, map_zero]
  -- Two cases: negSupport a = ∅ or nonempty
  by_cases hne : a.negSupport = ∅
  · -- Case negSupport = ∅: both sides equal monomialCoeffShift a S₀ (f(S₀))
    -- LHS: monomialCoeffShift a S (polyElemModHom d_nat S g)
    --     = coeff(numFinsupp a ∅, g.val) = r_a  (by construction of g)
    have h_lhs : monomialCoeffShift a S (polyElemModHom d_nat S g) =
        monomialCoeffShift a S₀ (f ⟨S₀, hS₀⟩) := by
      rw [monomialCoeffShift_polyElemMod_of_empty d_nat a hne S g]
      simp only [g, gval, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single a]
      · simp [MvPolynomial.coeff_monomial]
      · intro b _ hba
        simp only [MvPolynomial.coeff_monomial]
        rw [if_neg]
        intro heq
        exact hba (Subtype.ext (funext fun i => by
          have hb_empty := (Finset.mem_filter.mp ‹b ∈ A›).2
          have := DFunLike.congr_fun heq i
          simp only [LaurentExp.numFinsupp_apply, LaurentExp.numExp,
            Finset.notMem_empty, ↓reduceIte] at this
          have ha_nn := (a.negSupport_empty_iff_nonneg.mp hne) i
          have hb_nn := (b.negSupport_empty_iff_nonneg.mp hb_empty) i
          rw [← Int.toNat_of_nonneg hb_nn, ← Int.toNat_of_nonneg ha_nn]
          exact_mod_cast this))
      · intro ha_notmem
        simp only [MvPolynomial.coeff_monomial, ite_eq_right_iff]
        intro
        simp only [A, Finset.mem_filter, hne, and_true] at ha_notmem
        by_contra h
        exact ha_notmem (B₀.mem_toFinset.mpr ⟨hne ▸ Finset.empty_subset _, h⟩)
    -- RHS: by K_∅ constancy, all singletons give the same value
    have h_rhs : monomialCoeffShift a S (f ⟨S, hS⟩) =
        monomialCoeffShift a S₀ (f ⟨S₀, hS₀⟩) := by
      -- Define f₀ in K_∅ with same values as componentHomShift a 0 f
      set f₀ : _root_.relSimplexCochain ∅ R 0 := fun ⟨S', ⟨hS', _⟩⟩ =>
        monomialCoeffShift a S' (f ⟨S', hS'⟩)
      -- f₀ is a 0-cocycle: coboundary factors through monomialCoeffShiftHom
      suffices hf₀_cocycle : _root_.relSimplexδHom ∅ R 0 f₀ = 0 by
        have hconst := _root_.TopCat.relSimplexCochain_empty_ker_const R f₀ hf₀_cocycle
        have hS' := congr_fun hconst ⟨S, hS, Finset.empty_subset S⟩
        have hS₀' := congr_fun hconst ⟨S₀, hS₀, Finset.empty_subset S₀⟩
        simp only [_root_.TopCat.relSimplexConstCochainHom,
          _root_.TopCat.relSimplexEvalSingleton,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hS' hS₀'
        exact hS'.trans hS₀'.symm
      ext ⟨T, ⟨hT, _⟩⟩
      simp only [Pi.zero_apply, _root_.relSimplexδHom, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, _root_.relSimplexδ_apply, f₀]
      -- Apply monomialCoeffShiftHom a T to the cocycle condition algebraicδ f = 0
      have hfT := congr_fun hf ⟨T, hT⟩
      simp only [algebraicδ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at hfT
      have hkey := congr_arg (monomialCoeffShiftHom a T) hfT
      simp only [map_sum, map_zsmul, map_zero] at hkey
      -- Face compatibility: rewrite each summand using monomialCoeffShift_coordRestrict
      have h_face : ∀ j : Fin (0 + 2),
          monomialCoeffShift a (TopCat.eraseNth T hT j).1
            (f (TopCat.eraseNth T hT j)) =
          monomialCoeffShift a T (coordRestrict n R
            (GradedModule.shift (𝒜 n R) d_nat) T hT j
            (f (TopCat.eraseNth T hT j))) :=
        fun j => (monomialCoeffShift_coordRestrict a hT j
          (hne ▸ Finset.empty_subset _) _).symm
      simp_rw [h_face]
      exact hkey
    show monomialCoeffShift a S (polyElemModHom d_nat S g) -
      monomialCoeffShift a S (f ⟨S, hS⟩) = 0
    rw [h_lhs, h_rhs, sub_self]
  · -- Case negSupport ≠ ∅: both sides are zero
    show monomialCoeffShift a S (polyElemModHom d_nat S g) -
      monomialCoeffShift a S (f ⟨S, hS⟩) = 0
    rw [monomialCoeffShift_polyElemMod_of_nonempty d_nat a
      (Finset.nonempty_iff_ne_empty.mpr hne) S ha g, zero_sub, neg_eq_zero]
    -- monomialCoeffShift a S (f(S)) = 0 by K_T acyclicity at degree 0
    have hne' : a.negSupport ≠ Finset.univ := a.negSupport_ne_univ hd
    have hac := _root_.relSimplexComplex_acyclic a.negSupport R
      (Finset.nonempty_iff_ne_empty.mpr hne) hne'
    suffices hz : componentHomShift a 0 f = 0 from
      show componentHomShift a 0 f ⟨S, hS, ha⟩ = 0 by rw [hz, Pi.zero_apply]
    set K := _root_.relSimplexComplex a.negSupport R
    have hker_le := ((K.sc 0).ab_exact_iff_ker_le_range).mp (hac 0)
    have hf_zero : (K.sc 0).f = 0 :=
      K.shape _ _ (fun h => by simp [ComplexShape.up_Rel] at h)
    have hrange_bot : (K.sc 0).f.hom.range = ⊥ := by
      have : (K.sc 0).f.hom = 0 := congr_arg AddCommGrp.Hom.hom hf_zero
      rw [this]; exact AddMonoidHom.range_zero
    have hg_mem' : componentHomShift a 0 f ∈ (K.sc 0).g.hom.ker := by
      rw [AddMonoidHom.mem_ker]
      show K.d 0 ((ComplexShape.up ℕ).next 0) (componentHomShift a 0 f) = 0
      rw [(ComplexShape.up ℕ).next_eq' (show (0 : ℕ) + 1 = 1 from rfl),
        show K.d 0 1 = AddCommGrp.ofHom
          (_root_.relSimplexδHom a.negSupport R 0) from
          CochainComplex.of_d _ _ _ 0]
      exact hcomp_cocycle
    rw [hrange_bot] at hker_le
    exact AddSubgroup.mem_bot.mp (hker_le hg_mem')

/-- `H⁰(algebraicComplex(shift 𝒜 d)) ≅ 𝒜_d` for `d ≥ 0`:
the degree-zero cohomology of the algebraic Čech complex for the `d`-th twist
on projective space is isomorphic to the degree-`d` homogeneous polynomials. -/
noncomputable def algebraicComplex_shift_H0_iso (hd : 0 ≤ (d_nat : ℤ)) :
    (algebraicComplex n R (GradedModule.shift (𝒜 n R) d_nat)).homology 0 ≅
    AddCommGrp.of ↥((𝒜 n R) d_nat) := by
  set 𝓜 := GradedModule.shift (𝒜 n R) d_nat
  set A := algebraicComplex n R 𝓜
  -- Step 1: Unwrap homology via short complex
  refine A.homologyIsoSc' _ 0 1 rfl ((ComplexShape.up ℕ).next_eq' rfl) ≪≫ ?_
  set SA := A.sc' ((ComplexShape.up ℕ).prev 0) 0 1
  refine SA.abHomologyIso ≪≫ ?_
  -- Step 2: Incoming map f = 0 (no degree -1 in ℕ-complex), so range = ⊥
  have hf : SA.f = 0 := A.shape _ _ (by simp [ComplexShape.up_Rel])
  have habToCycles_zero : SA.abToCycles = 0 := by
    ext x : 1; refine Subtype.ext ?_; change (SA.f x : SA.X₂) = 0; simp [hf]
  have hrange_bot : AddMonoidHom.range SA.abToCycles = ⊥ := by
    rw [habToCycles_zero]; exact AddMonoidHom.range_zero
  -- SA.g.hom = algebraicδ 0
  have hg_hom : SA.g.hom = algebraicδ n R 𝓜 0 := by
    show (A.d 0 1).hom = _
    have h : A.d 0 1 = AddCommGrp.ofHom (algebraicδ n R 𝓜 0) :=
      CochainComplex.of_d _ _ _ 0
    rw [h]; rfl
  -- Step 3: Build (ker g / range abToCycles) ≃+ 𝒜_d
  -- Helper: extract a polynomial from a kernel element
  have surj : ∀ x : AddMonoidHom.ker SA.g.hom,
      ∃ g : ↥((𝒜 n R) d_nat), polyEmbeddingHom d_nat 0 g = x.1 :=
    fun x => polyEmbedding_surj_cocycle d_nat hd x.1 (by rw [← hg_hom]; exact x.2)
  have kerEquiv : AddMonoidHom.ker SA.g.hom ≃+ ↥((𝒜 n R) d_nat) :=
    { toFun := fun x => (surj x).choose
      invFun := fun g => ⟨polyEmbeddingHom d_nat 0 g, by
        rw [AddMonoidHom.mem_ker, hg_hom]
        exact polyEmbedding_cocycle d_nat g⟩
      left_inv := fun x => by
        ext1; exact (surj x).choose_spec
      right_inv := fun g => by
        have h := (surj ⟨polyEmbeddingHom d_nat 0 g, by
          rw [AddMonoidHom.mem_ker, hg_hom]
          exact polyEmbedding_cocycle d_nat g⟩).choose_spec
        exact sub_eq_zero.mp (polyEmbedding_injective d_nat _
          (by rw [map_sub, h, sub_self]))
      map_add' := fun x y => by
        have hxy := (surj (x + y)).choose_spec
        have hx := (surj x).choose_spec
        have hy := (surj y).choose_spec
        exact sub_eq_zero.mp (polyEmbedding_injective d_nat _
          (by rw [map_sub, map_add, hxy, hx, hy]; simp)) }
  have totalEquiv :
      (AddMonoidHom.ker SA.g.hom ⧸ AddMonoidHom.range SA.abToCycles) ≃+
      ↥((𝒜 n R) d_nat) :=
    (QuotientAddGroup.quotientAddEquivOfEq hrange_bot).trans
      (QuotientAddGroup.quotientBot.trans kerEquiv)
  exact totalEquiv.toAddCommGrpIso

end H0Shift

end AlgebraicGeometry.Proj
