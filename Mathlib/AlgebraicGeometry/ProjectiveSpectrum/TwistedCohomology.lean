/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.MonomialCoefficient

/-!
# Cohomology of the twisted structure sheaf on projective space

This file proves the higher cohomology vanishing for the twisted structure sheaf
`𝒪(d)` on projective n-space over a commutative ring `R`, for `d ≥ 0`:
  `Hᵖ(algebraicComplex, 𝒪(d)) = 0` for `p > 0`

The key simplification for `d ≥ 0`: no Laurent exponent `a` with `∑ aᵢ = d ≥ 0`
can have all entries negative, so `negSupport a ≠ univ` always holds. This means
every monomial component lands in an acyclic `K_T`, eliminating the need for the
extraction/embedding splitting used in the `d = 0` proof.

## Main results

* `algebraicComplex_shift_acyclic_pos`: `Hᵖ(𝒪(d)) = 0` for `p > 0` and `d ≥ 0`

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

end Acyclicity

end AlgebraicGeometry.Proj
