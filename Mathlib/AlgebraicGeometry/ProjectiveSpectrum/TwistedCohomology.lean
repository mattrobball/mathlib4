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
-- The `algebraicδ` unfolding and `determines_zero` verification involve large term reductions.
/-- Generic acyclicity: `Hᵖ(algebraicComplex 𝓜) = 0` for `p > 0`, given:
- `smulME r a S hS` constructs `r · monomialElem a` in `Away 𝓜 S`
- `orthog` gives orthogonality: `monomialCoeff a' (smulME r a S hS) = if a'=a then r else 0`
- `det_zero` gives injectivity: all coefficients zero implies element is zero
- `hne_univ` ensures negSupport is always a proper subset of `univ`. -/
private theorem algebraicComplex_acyclic_pos_aux
    {𝓜 : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R)}
    [SetLike.GradedSMul (𝒜 n R) 𝓜] {d : ℤ} (p : ℕ)
    (smulME : R → (a : LaurentExp n d) → (S : Finset (Fin (n + 1))) →
      a.negSupport ⊆ S →
      HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S))
    (orthog : ∀ (a b : LaurentExp n d) (S : Finset (Fin (n + 1)))
      (hS : a.negSupport ⊆ S) (_ : b.negSupport ⊆ S) (r : R),
      monomialCoeff b S (smulME r a S hS) = if b = a then r else 0)
    (det_zero : ∀ (S : Finset (Fin (n + 1)))
      (x : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S)),
      (∀ (a : LaurentExp n d) (_ : a.negSupport ⊆ S),
        monomialCoeff a S x = 0) → x = 0)
    (hne_univ : ∀ a : LaurentExp n d, a.negSupport ≠ Finset.univ) :
    IsZero ((algebraicComplex n R 𝓜).homology (p + 1)) := by
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
        (componentHom a (p + 1) f) = 0 := by
    intro a; rw [← component_comm_δ a (p + 1) f, hfδ, map_zero]
  -- Collect the finite set of nonzero Laurent exponents
  set B : Set (LaurentExp n d) :=
    ⋃ T : {T : Finset (Fin (n + 1)) // T.card = (p + 1) + 1},
      {a : LaurentExp n d | ∃ _ : a.negSupport ⊆ T.1,
        monomialCoeff a T.1 (f T) ≠ 0}
  have hB_finite : B.Finite :=
    Set.finite_iUnion fun T => monomialCoeff_finite_support T.1 (f T)
  set B_fin := hB_finite.toFinset
  -- For each a, get primitive g_a in K_{negSupport a}
  have hprimitive : ∀ (a : LaurentExp n d), a ∈ B_fin →
      ∃ ga : _root_.relSimplexCochain a.negSupport R p,
        _root_.relSimplexδHom a.negSupport R p ga =
          componentHom a (p + 1) f := by
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
        componentHom a (p + 1) f := by
    intro a ha
    show _root_.relSimplexδHom a.negSupport R p
      (if h : a ∈ B_fin then (hprimitive a h).choose else 0) = _
    rw [dif_pos ha]; exact (hprimitive a ha).choose_spec
  have hga_outside : ∀ a, a ∉ B_fin → ga a = 0 := by
    intro a ha
    show (if h : a ∈ B_fin then _ else 0) = 0
    rw [dif_neg ha]
  have hcomp_zero_outside : ∀ (a : LaurentExp n d), a ∉ B_fin →
      componentHom a (p + 1) f = 0 := by
    intro a ha
    ext ⟨T, hT, hns⟩
    simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
    by_contra hne
    apply ha
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨T, hT⟩, hns, hne⟩
  have hga_spec_all : ∀ a : LaurentExp n d,
      _root_.relSimplexδHom a.negSupport R p (ga a) =
        componentHom a (p + 1) f := by
    intro a
    by_cases ha_mem : a ∈ B_fin
    · exact hga_spec a ha_mem
    · rw [hga_outside a ha_mem, map_zero]
      exact (hcomp_zero_outside a ha_mem).symm
  -- Construct the primitive
  refine ⟨fun ⟨S, hS⟩ =>
    B_fin.sum fun a =>
      if h : a.negSupport ⊆ S then smulME (ga a ⟨S, hS, h⟩) a S h
      else 0, ?_⟩
  -- Verify δG = f using orthogonality and injectivity of monomialCoeff
  rw [hfi, hAd]
  show algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then smulME (ga a ⟨S, hS, h⟩) a S h
        else 0) = f
  funext ⟨T, hT⟩
  suffices hsub : algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then smulME (ga a ⟨S, hS, h⟩) a S h
        else 0) ⟨T, hT⟩ - f ⟨T, hT⟩ = 0 from sub_eq_zero.mp hsub
  apply det_zero
  intro b hb
  show (monomialCoeffHom b T) _ = 0
  rw [map_sub]
  have h_lhs : (monomialCoeffHom b T) (algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then smulME (ga a ⟨S, hS, h⟩) a S h
        else 0) ⟨T, hT⟩) =
    componentHom b (p + 1) (algebraicδ n R 𝓜 p (fun ⟨S, hS⟩ =>
      B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then smulME (ga a ⟨S, hS, h⟩) a S h
        else 0)) ⟨T, hT, hb⟩ := rfl
  rw [h_lhs, component_comm_δ b p]
  have h_rhs : (monomialCoeffHom b T) (f ⟨T, hT⟩) =
      componentHom b (p + 1) f ⟨T, hT, hb⟩ := rfl
  rw [h_rhs]
  suffices hcomp_eq : componentHom b p
      (fun ⟨S, hS⟩ => B_fin.sum fun a =>
        if h : a.negSupport ⊆ S then smulME (ga a ⟨S, hS, h⟩) a S h
        else 0) = ga b by
    rw [hcomp_eq]; simp [hga_spec_all b]
  ext ⟨S, hS, hb'⟩
  simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  show (monomialCoeffHom b S) _ = _
  rw [map_sum]
  simp_rw [show ∀ (a : LaurentExp n d),
    (monomialCoeffHom b S)
      (if h : a.negSupport ⊆ S then smulME (ga a ⟨S, hS, h⟩) a S h
      else 0) =
    if h : a.negSupport ⊆ S then
      monomialCoeff b S (smulME (ga a ⟨S, hS, h⟩) a S h)
    else 0 from fun a => by split_ifs with h <;> [rfl; exact map_zero _]]
  simp_rw [fun (a : LaurentExp n d) (h : a.negSupport ⊆ S) =>
    orthog a b S h hb' (ga a ⟨S, hS, h⟩)]
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

/-- `Hᵖ(algebraicComplex(shift 𝒜 d)) = 0` for `p > 0` and `d ≥ 0`:
the higher cohomology of the twisted structure sheaf `𝒪(d)` vanishes. -/
theorem algebraicComplex_shift_acyclic_pos (d : ℤ) (hd : 0 ≤ d) (p : ℕ) :
    IsZero ((algebraicComplex n R (GradedModule.shift (𝒜 n R) d.toNat)).homology
      (p + 1)) :=
  algebraicComplex_acyclic_pos_aux p
    (fun r a S hS => smulMonomialElemShift (R := R) d hd r a S hS)
    (fun a b S hS hS' r => monomialCoeffShift_smulMonomialElemShift d hd b a S hS' hS r)
    (fun S x h => monomialCoeffShift_determines_zero hd S x h)
    (fun a => a.negSupport_ne_univ hd)

/-- `Hᵖ(algebraicComplex(intShift 𝒜 d)) = 0` for `p > 0` and `d > -(n+1)`:
the higher cohomology of the twisted structure sheaf `𝒪(d)` vanishes for all `d > -(n+1)`. -/
theorem algebraicComplex_intShift_acyclic_pos (d : ℤ)
    (hd : -(↑(n + 1) : ℤ) < d) (p : ℕ) :
    IsZero ((algebraicComplex n R (GradedModule.intShift (𝒜 n R) d)).homology
      (p + 1)) :=
  algebraicComplex_acyclic_pos_aux p
    (fun r a S hS => smulMonomialElemIntShift (R := R) r a S hS)
    (fun a b S hS hS' r => monomialCoeffIntShift_smulMonomialElemIntShift a b S hS hS' r)
    (fun S x h => monomialCoeffIntShift_determines_zero S x h)
    (fun a => a.negSupport_ne_univ_of_gt hd)

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
        (componentHom a 0 f) = 0 := by
    intro a; rw [← component_comm_δ a 0 f, hfδ, map_zero]
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
  show componentHom a 0 f ⟨S, hS, ha⟩ = 0
  suffices hz : componentHom a 0 f = 0 from congr_fun hz ⟨S, hS, ha⟩
  set K := _root_.relSimplexComplex a.negSupport R
  have hker_le := ((K.sc 0).ab_exact_iff_ker_le_range).mp (hac 0)
  have hf_zero : (K.sc 0).f = 0 :=
    K.shape _ _ (fun h => by simp [ComplexShape.up_Rel] at h)
  have hrange_bot : (K.sc 0).f.hom.range = ⊥ := by
    have : (K.sc 0).f.hom = 0 := congr_arg AddCommGrp.Hom.hom hf_zero
    rw [this]; exact AddMonoidHom.range_zero
  have hg_mem : componentHom a 0 f ∈ (K.sc 0).g.hom.ker := by
    rw [AddMonoidHom.mem_ker]
    show K.d 0 ((ComplexShape.up ℕ).next 0) (componentHom a 0 f) = 0
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
    monomialCoeff a S (polyElemModHom d_nat S g) =
    MvPolynomial.coeff (a.numFinsupp ∅) g.val := by
  simp only [polyElemModHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  erw [monomialCoeff_Away_mk]
  rw [clearingPow_eq_zero_of_negSupport_empty d_nat a h S, pow_zero, one_mul,
    coordProdFinsupp_zero, add_zero,
    numFinsupp_eq_of_negSupport_empty d_nat a h S]

/-- The coefficient extraction of an embedded polynomial at a Laurent exponent with
nonempty negSupport returns zero: polynomial elements have no negative-exponent
components. -/
private theorem monomialCoeffShift_polyElemMod_of_nonempty
    (a : LaurentExp n (↑d_nat)) (h : a.negSupport.Nonempty)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S)
    (g : ↥((𝒜 n R) d_nat)) :
    monomialCoeff a S (polyElemModHom d_nat S g) = 0 := by
  simp only [polyElemModHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  erw [monomialCoeff_Away_mk]
  rw [coordProdFinsupp_zero, add_zero]
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
  -- Define r_a = monomialCoeff a {0} (f({0}))
  -- Construct g = ∑ monomial(numFinsupp a ∅, r_a) as an element of 𝒜_d
  set B₀ := monomialCoeff_finite_support (R := R) (d := ↑d_nat) S₀ (f ⟨S₀, hS₀⟩)
  set A := B₀.toFinset.filter (fun a => a.negSupport = ∅)
  -- Define the polynomial
  set gval : MvPolynomial (Fin (n + 1)) R :=
    A.sum fun a => MvPolynomial.monomial (a.numFinsupp ∅)
      (monomialCoeff a S₀ (f ⟨S₀, hS₀⟩))
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
  -- Suffices to show all monomialCoeff agree
  rw [← sub_eq_zero]
  apply monomialCoeffShift_determines_zero hd
  intro a ha
  show (monomialCoeffHom a S) _ = 0
  rw [map_sub]
  -- f is a cocycle: componentShift a 0 f is a cocycle in K_{negSupport a}
  have hcomp_cocycle :
      _root_.relSimplexδHom a.negSupport R 0
        (componentHom a 0 f) = 0 := by
    rw [← component_comm_δ a 0 f]
    change componentHom a 1
      (algebraicδ n R (GradedModule.shift (𝒜 n R) d_nat) 0 f) = 0
    rw [hf, map_zero]
  -- Two cases: negSupport a = ∅ or nonempty
  by_cases hne : a.negSupport = ∅
  · -- Case negSupport = ∅: both sides equal monomialCoeff a S₀ (f(S₀))
    -- LHS: monomialCoeff a S (polyElemModHom d_nat S g)
    --     = coeff(numFinsupp a ∅, g.val) = r_a  (by construction of g)
    have h_lhs : monomialCoeff a S (polyElemModHom d_nat S g) =
        monomialCoeff a S₀ (f ⟨S₀, hS₀⟩) := by
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
    have h_rhs : monomialCoeff a S (f ⟨S, hS⟩) =
        monomialCoeff a S₀ (f ⟨S₀, hS₀⟩) := by
      -- Define f₀ in K_∅ with same values as componentHom a 0 f
      set f₀ : _root_.relSimplexCochain ∅ R 0 := fun ⟨S', ⟨hS', _⟩⟩ =>
        monomialCoeff a S' (f ⟨S', hS'⟩)
      -- f₀ is a 0-cocycle: coboundary factors through monomialCoeffHom
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
      -- Apply monomialCoeffHom a T to the cocycle condition algebraicδ f = 0
      have hfT := congr_fun hf ⟨T, hT⟩
      simp only [algebraicδ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at hfT
      have hkey := congr_arg (monomialCoeffHom a T) hfT
      simp only [map_sum, map_zsmul, map_zero] at hkey
      -- Face compatibility: rewrite each summand using monomialCoeff_coordRestrict
      have h_face : ∀ j : Fin (0 + 2),
          monomialCoeff a (TopCat.eraseNth T hT j).1
            (f (TopCat.eraseNth T hT j)) =
          monomialCoeff a T (coordRestrict n R
            (GradedModule.shift (𝒜 n R) d_nat) T hT j
            (f (TopCat.eraseNth T hT j))) :=
        fun j => (monomialCoeff_coordRestrict a hT j
          (hne ▸ Finset.empty_subset _) _).symm
      simp_rw [h_face]
      exact hkey
    show monomialCoeff a S (polyElemModHom d_nat S g) -
      monomialCoeff a S (f ⟨S, hS⟩) = 0
    rw [h_lhs, h_rhs, sub_self]
  · -- Case negSupport ≠ ∅: both sides are zero
    show monomialCoeff a S (polyElemModHom d_nat S g) -
      monomialCoeff a S (f ⟨S, hS⟩) = 0
    rw [monomialCoeffShift_polyElemMod_of_nonempty d_nat a
      (Finset.nonempty_iff_ne_empty.mpr hne) S ha g, zero_sub, neg_eq_zero]
    -- monomialCoeff a S (f(S)) = 0 by K_T acyclicity at degree 0
    have hne' : a.negSupport ≠ Finset.univ := a.negSupport_ne_univ hd
    have hac := _root_.relSimplexComplex_acyclic a.negSupport R
      (Finset.nonempty_iff_ne_empty.mpr hne) hne'
    suffices hz : componentHom a 0 f = 0 from
      show componentHom a 0 f ⟨S, hS, ha⟩ = 0 by rw [hz, Pi.zero_apply]
    set K := _root_.relSimplexComplex a.negSupport R
    have hker_le := ((K.sc 0).ab_exact_iff_ker_le_range).mp (hac 0)
    have hf_zero : (K.sc 0).f = 0 :=
      K.shape _ _ (fun h => by simp [ComplexShape.up_Rel] at h)
    have hrange_bot : (K.sc 0).f.hom.range = ⊥ := by
      have : (K.sc 0).f.hom = 0 := congr_arg AddCommGrp.Hom.hom hf_zero
      rw [this]; exact AddMonoidHom.range_zero
    have hg_mem' : componentHom a 0 f ∈ (K.sc 0).g.hom.ker := by
      rw [AddMonoidHom.mem_ker]
      show K.d 0 ((ComplexShape.up ℕ).next 0) (componentHom a 0 f) = 0
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

/-! ### H^n(𝒪(d)) ≅ 𝒜_m for d ≤ -(n+1), m = -d-(n+1) -/

section HnNegTwist

/-! #### Dual Finsupp bijection

For `d ≤ -(n+1)`, set `m = (-d - (n+1)).toNat`. The all-negative Laurent exponents
(those with `negSupport = univ`) biject with degree-`m` monomials via `aᵢ ↦ -aᵢ - 1`.
-/

/-- Map an all-negative Laurent exponent to a polynomial `Finsupp`: `aᵢ ↦ (-aᵢ - 1)`. -/
private def dualFinsupp (d : ℤ) (a : LaurentExp n d) (_h : a.negSupport = Finset.univ) :
    Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.invFun (fun i => (-a.1 i - 1).toNat)

private theorem dualFinsupp_apply (d : ℤ) (a : LaurentExp n d)
    (h : a.negSupport = Finset.univ) (i : Fin (n + 1)) :
    dualFinsupp d a h i = (-a.1 i - 1).toNat := by
  simp [dualFinsupp]

private theorem dualFinsupp_apply_int (d : ℤ) (a : LaurentExp n d)
    (h : a.negSupport = Finset.univ) (i : Fin (n + 1)) :
    (dualFinsupp d a h i : ℤ) = -a.1 i - 1 := by
  rw [dualFinsupp_apply]
  exact Int.toNat_of_nonneg (by
    have := (a.mem_negSupport_iff i).mp (h ▸ Finset.mem_univ i); omega)

private theorem dualFinsupp_degree (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ))
    (a : LaurentExp n d) (h : a.negSupport = Finset.univ) :
    (dualFinsupp d a h).degree = (-d - ↑(n + 1)).toNat := by
  simp only [Finsupp.degree]
  rw [Finset.sum_subset (Finset.subset_univ _)
    (fun i _ hi => Finsupp.notMem_support_iff.mp hi)]
  suffices h_int : (∑ i, (dualFinsupp d a h i : ℤ)) =
      ((-d - ↑(n + 1)).toNat : ℤ) by exact_mod_cast h_int
  simp_rw [dualFinsupp_apply_int d a h]
  rw [Int.toNat_of_nonneg (by omega)]
  simp_rw [show ∀ i : Fin (n + 1), -a.1 i - 1 = -a.1 i + (-1) from fun _ => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp [a.2, Fintype.card_fin]; ring

/-- Map a polynomial `Finsupp` of degree `m` to an all-negative Laurent exponent:
`bᵢ ↦ -(bᵢ : ℤ) - 1`. -/
private def inverseDualExp (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ))
    (b : Fin (n + 1) →₀ ℕ) (hb : b.degree = (-d - ↑(n + 1)).toNat) :
    LaurentExp n d :=
  ⟨fun i => -(b i : ℤ) - 1, by
    simp only [Finsupp.degree] at hb
    have hb' : ∑ i : Fin (n + 1), b i = (-d - ↑(n + 1)).toNat := by
      rwa [Finset.sum_subset (Finset.subset_univ _)
        (fun i _ hi => Finsupp.notMem_support_iff.mp hi)] at hb
    have hb_int : (∑ i, (b i : ℤ)) = -d - ↑(n + 1) := by
      zify at hb'; rwa [Int.toNat_of_nonneg (by omega)] at hb'
    simp_rw [show ∀ i : Fin (n + 1), -(b i : ℤ) - 1 = -(b i : ℤ) + (-1) from
      fun _ => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp [hb_int, Fintype.card_fin]; ring⟩

private theorem inverseDualExp_apply (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ))
    (b : Fin (n + 1) →₀ ℕ) (hb : b.degree = (-d - ↑(n + 1)).toNat)
    (i : Fin (n + 1)) :
    (inverseDualExp d hd b hb).1 i = -(b i : ℤ) - 1 := rfl

private theorem inverseDualExp_negSupport (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ))
    (b : Fin (n + 1) →₀ ℕ) (hb : b.degree = (-d - ↑(n + 1)).toNat) :
    (inverseDualExp d hd b hb).negSupport = Finset.univ := by
  ext i; simp [LaurentExp.mem_negSupport_iff, inverseDualExp_apply]; omega

private theorem dualFinsupp_inverseDualExp (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ))
    (b : Fin (n + 1) →₀ ℕ) (hb : b.degree = (-d - ↑(n + 1)).toNat) :
    dualFinsupp d (inverseDualExp d hd b hb)
      (inverseDualExp_negSupport d hd b hb) = b := by
  ext i; rw [dualFinsupp_apply, inverseDualExp_apply]; omega

private theorem inverseDualExp_dualFinsupp (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ))
    (a : LaurentExp n d) (h : a.negSupport = Finset.univ) :
    inverseDualExp d hd (dualFinsupp d a h) (dualFinsupp_degree d hd a h) = a := by
  refine Subtype.ext (funext fun i => ?_)
  rw [inverseDualExp_apply, dualFinsupp_apply_int]; ring

private theorem dualFinsupp_injective (d : ℤ) (_hd : d ≤ -(↑(n + 1) : ℤ))
    (a a' : LaurentExp n d)
    (h : a.negSupport = Finset.univ) (h' : a'.negSupport = Finset.univ)
    (heq : dualFinsupp d a h = dualFinsupp d a' h') : a = a' := by
  refine Subtype.ext (funext fun i => ?_)
  have hi : dualFinsupp d a h i = dualFinsupp d a' h' i := DFunLike.congr_fun heq i
  rw [dualFinsupp_apply, dualFinsupp_apply] at hi
  have ha := (a.mem_negSupport_iff i).mp (h ▸ Finset.mem_univ i)
  have ha' := (a'.mem_negSupport_iff i).mp (h' ▸ Finset.mem_univ i)
  omega

/-! #### Helper lemmas for cast -/

private lemma algebraicComplex_XIsoOfEq_eval
    {𝓜 : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R)} [SetLike.GradedSMul (𝒜 n R) 𝓜]
    {p k : ℕ} (hk : p + 1 = k)
    (x : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1 + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S.1))
    (S : Finset (Fin (n + 1))) (hS : S.card = k + 1) (hS' : S.card = p + 1 + 1) :
    ((algebraicComplex n R 𝓜).XIsoOfEq hk).hom.hom x ⟨S, hS⟩ = x ⟨S, hS'⟩ := by
  subst hk; rfl

private lemma relSimplexCochain_cast_eval (T : Finset (Fin (n + 1)))
    {p k : ℕ} (hk : p + 1 = k)
    (f : _root_.relSimplexCochain T R k)
    (S : Finset (Fin (n + 1))) (hS : S.card = p + 1 + 1 ∧ T ⊆ S)
    (hS' : S.card = k + 1 ∧ T ⊆ S) :
    (Eq.mp (congr_arg (_root_.relSimplexCochain T R) hk.symm) f) ⟨S, hS⟩ =
    f ⟨S, hS'⟩ := by
  subst hk; rfl

/-! #### All-negative polynomial extraction -/

/-- Extract the "all-negative polynomial" from a localized module element:
for each all-negative Laurent exponent `a` (with `negSupport = univ`), collect its
monomial coefficient as a term `monomial(dualFinsupp(a), coeff_a(x))`.
The result is a homogeneous polynomial of degree `m = (-d-(n+1)).toNat`. -/
private noncomputable def allNegPoly (d : ℤ) (_hd : d ≤ -(↑(n + 1) : ℤ))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.intShift (𝒜 n R) d) (coordProd n R Finset.univ)) :
    MvPolynomial (Fin (n + 1)) R :=
  (monomialCoeff_finite_support (d := d) Finset.univ x).toFinset.sum fun a =>
    if h : a.negSupport = Finset.univ then
      MvPolynomial.monomial (dualFinsupp d a h)
        (monomialCoeff a Finset.univ x)
    else 0

private theorem allNegPoly_mem (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.intShift (𝒜 n R) d) (coordProd n R Finset.univ)) :
    allNegPoly d hd x ∈ (𝒜 n R) ((-d - ↑(n + 1)).toNat) := by
  apply Submodule.sum_mem; intro a _
  split_ifs with h
  · rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_monomial _ (dualFinsupp_degree d hd a h)
  · exact zero_mem _

set_option maxHeartbeats 800000 in
-- The proof assembles a quotient equivalence from monomial coefficient extraction,
-- requiring extensive unfolding of the algebraic complex and localization machinery.
/-- `Hⁿ(𝒪(d)) ≅ 𝒜_m` for `d ≤ -(n+1)` with `m = -d-(n+1)`: the top cohomology of the
twisted structure sheaf on projective `n`-space is the graded component of degree `m`. -/
noncomputable def algebraicComplex_intShift_Hn_iso_general
    (d : ℤ) (hd : d ≤ -(↑(n + 1) : ℤ)) :
    (algebraicComplex n R (GradedModule.intShift (𝒜 n R) d)).homology n ≅
    AddCommGrp.of ↥((𝒜 n R) ((-d - ↑(n + 1)).toNat)) := by
  set m := (-d - ↑(n + 1)).toNat with hm_def
  set 𝓜 := GradedModule.intShift (𝒜 n R) d
  set A := algebraicComplex n R 𝓜
  have hd_neg : d < 0 := by omega
  have huniv : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  -- Step 1: Unwrap homology via short complex
  refine A.homologyIsoSc' _ n (n + 1) rfl ((ComplexShape.up ℕ).next_eq' rfl) ≪≫ ?_
  set SA := A.sc' ((ComplexShape.up ℕ).prev n) n (n + 1)
  refine SA.abHomologyIso ≪≫ ?_
  -- Step 2: SA.g = 0 (no (n+2)-element subsets of Fin(n+1))
  have hg : SA.g = 0 := by
    apply IsZero.eq_of_tgt
    show IsZero (A.X (n + 1))
    have hempty : IsEmpty {S : Finset (Fin (n + 1)) // S.card = n + 1 + 1} :=
      ⟨fun ⟨S, hS⟩ => absurd (Finset.card_le_univ S) (by rw [Fintype.card_fin]; omega)⟩
    exact @AddCommGrp.isZero_of_subsingleton _
      ⟨fun f g => funext fun x => hempty.elim x⟩
  have hg_hom : SA.g.hom = 0 := congr_arg AddCommGrp.Hom.hom hg
  have hker_mem : ∀ f, f ∈ SA.g.hom.ker :=
    fun f => by rw [AddMonoidHom.mem_ker, hg_hom, AddMonoidHom.zero_apply]
  have hAd : ∀ j, A.d j (j + 1) = AddCommGrp.ofHom (algebraicδ n R 𝓜 j) :=
    fun j => by simp [A, algebraicComplex]
  -- All Laurent exponents have nonempty negSupport (d < 0)
  have hnonempty : ∀ a : LaurentExp n d, a.negSupport.Nonempty :=
    fun a => a.negSupport_nonempty_of_neg hd_neg
  -- Step 3: Define extraction map ext_map : ker(g) →+ 𝒜_m
  set ext_map : SA.g.hom.ker →+ ↥((𝒜 n R) m) := {
    toFun := fun ⟨f, _⟩ =>
      ⟨allNegPoly d hd (f ⟨Finset.univ, huniv⟩),
       allNegPoly_mem d hd (f ⟨Finset.univ, huniv⟩)⟩
    map_zero' := by
      refine Subtype.ext ?_; show allNegPoly d hd 0 = 0
      simp only [allNegPoly]
      apply Finset.sum_eq_zero; intro a _
      split_ifs with h
      · have h0 : monomialCoeff (𝓜 := 𝓜) a Finset.univ 0 = 0 :=
          (monomialCoeffHom (𝓜 := 𝓜) a Finset.univ).map_zero
        rw [h0, MvPolynomial.monomial_zero]
      · rfl
    map_add' := fun ⟨f, _⟩ ⟨g, _⟩ => by
      refine Subtype.ext ?_
      show allNegPoly d hd ((f + g) ⟨Finset.univ, huniv⟩) =
        allNegPoly d hd (f ⟨Finset.univ, huniv⟩) +
        allNegPoly d hd (g ⟨Finset.univ, huniv⟩)
      rw [Pi.add_apply]; simp only [allNegPoly]
      -- Terms vanish outside finite support
      have hvan : ∀ (y : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜
          (coordProd n R Finset.univ)) (a : LaurentExp n d),
          a ∉ (monomialCoeff_finite_support (d := d) Finset.univ y).toFinset →
          (if h : a.negSupport = Finset.univ then MvPolynomial.monomial
            (dualFinsupp d a h) (monomialCoeff a Finset.univ y)
          else (0 : MvPolynomial (Fin (n + 1)) R)) = 0 := by
        intro y a ha; split_ifs with h
        · have : monomialCoeff (𝓜 := 𝓜) a Finset.univ y = 0 := by
            by_contra hne
            exact ha ((monomialCoeff_finite_support (d := d) Finset.univ y).mem_toFinset.mpr
              ⟨Finset.subset_univ _, hne⟩)
          rw [this, MvPolynomial.monomial_zero]
        · rfl
      -- Extend all sums to a common finite set
      set U := (monomialCoeff_finite_support (d := d) Finset.univ
            (f ⟨_, huniv⟩ + g ⟨_, huniv⟩)).toFinset ∪
          ((monomialCoeff_finite_support (d := d) Finset.univ (f ⟨_, huniv⟩)).toFinset ∪
            (monomialCoeff_finite_support (d := d) Finset.univ (g ⟨_, huniv⟩)).toFinset)
      rw [Finset.sum_subset Finset.subset_union_left (fun a _ ha => hvan _ a ha),
        Finset.sum_subset (Finset.subset_union_left.trans Finset.subset_union_right)
          (fun a _ ha => hvan _ a ha),
        Finset.sum_subset (Finset.subset_union_right.trans Finset.subset_union_right)
          (fun a _ ha => hvan _ a ha),
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by
        split_ifs with h
        · have := (monomialCoeffHom (𝓜 := 𝓜) a Finset.univ).map_add
            (f ⟨_, huniv⟩) (g ⟨_, huniv⟩)
          simp only [monomialCoeffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
          rw [this, map_add]
        · simp }
  -- Helper: convert weight-1 homogeneity to Finsupp.degree
  have hdeg_of_coeff : ∀ (q : MvPolynomial (Fin (n + 1)) R),
      q.IsHomogeneous m → ∀ (b : Fin (n + 1) →₀ ℕ),
      MvPolynomial.coeff b q ≠ 0 → b.degree = m := fun q hq b hne =>
    (congr_fun Finsupp.degree_eq_weight_one b).trans (hq hne)
  -- Step 4: Extraction is surjective
  have h_surj : Function.Surjective ext_map := by
    intro ⟨p, hp⟩
    simp only [MvPolynomial.mem_homogeneousSubmodule] at hp
    have hsd := hdeg_of_coeff p hp
    -- Construct preimage: ∑ smulMonomialElemIntShift over p.support at univ
    set fval : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R Finset.univ) :=
      p.support.attach.sum fun ⟨b, hb⟩ =>
        smulMonomialElemIntShift (R := R) (MvPolynomial.coeff b p)
          (inverseDualExp d hd b (hsd b (Finsupp.mem_support_iff.mp hb))) Finset.univ
          (by rw [inverseDualExp_negSupport])
    -- Lift to a function on all S with card = n+1
    refine ⟨⟨fun ⟨S, hS⟩ => if heq : S = Finset.univ then heq ▸ fval else 0,
      hker_mem _⟩, Subtype.ext ?_⟩
    -- Evaluate at univ (dite reduces since univ = univ)
    show allNegPoly d hd (dite (Finset.univ = Finset.univ) (fun heq => heq ▸ fval)
      (fun _ => 0)) = p
    simp only [dite_true]
    -- Need: allNegPoly d hd fval = p
    -- Compute monomialCoeff of fval via orthogonality
    have hmcoeff : ∀ (a : LaurentExp n d) (h : a.negSupport = Finset.univ),
        monomialCoeff (𝓜 := 𝓜) a Finset.univ fval =
        MvPolynomial.coeff (dualFinsupp d a h) p := by
      intro a ha
      show monomialCoeff (𝓜 := 𝓜) a Finset.univ fval = _
      -- Distribute monomialCoeff over the sum and apply orthogonality
      have hsum : monomialCoeff (𝓜 := 𝓜) a Finset.univ fval =
          ∑ x ∈ p.support.attach, (if a = inverseDualExp d hd x.1
            (hsd x.1 (Finsupp.mem_support_iff.mp x.2))
          then MvPolynomial.coeff x.1 p else 0) := by
        change (monomialCoeffHom (𝓜 := 𝓜) a Finset.univ) fval = _
        rw [map_sum]; refine Finset.sum_congr rfl fun ⟨b', hb'⟩ _ => ?_
        simp only [monomialCoeffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        exact monomialCoeffIntShift_smulMonomialElemIntShift _ a Finset.univ _
          (Finset.subset_univ _) _
      rw [hsum]; clear hsum
      -- Key lemma: from heq : a = inverseDualExp b', derive dualFinsupp a = b'
      have hdual_eq : ∀ (b' : Fin (n + 1) →₀ ℕ) (hb' : b'.degree = m),
          a = inverseDualExp d hd b' hb' → dualFinsupp d a ha = b' := fun b' _ heq => by
        ext i; rw [dualFinsupp_apply]
        have := congr_fun (Subtype.ext_iff.mp heq) i
        rw [inverseDualExp_apply] at this; omega
      -- Now: ∑ ⟨b',hb'⟩, (if a = inverseDualExp b' then coeff b' p else 0) = coeff(dual a)(p)
      by_cases hmem : dualFinsupp d a ha ∈ p.support
      · rw [Finset.sum_eq_single ⟨dualFinsupp d a ha, hmem⟩ ?_ ?_]
        · exact if_pos (inverseDualExp_dualFinsupp d hd a ha).symm
        · intro ⟨b', hb'⟩ _ hne; apply if_neg; intro heq
          exact hne (Subtype.ext (hdual_eq b' _ heq).symm)
        · intro habs; exact absurd (Finset.mem_attach _ _) habs
      · rw [Finset.sum_eq_zero, MvPolynomial.notMem_support_iff.mp hmem]
        intro ⟨b', hb'⟩ _; apply if_neg; intro heq
        exact hmem (by rw [hdual_eq b' _ heq]; exact hb')
    -- Now show allNegPoly d hd fval = p
    rw [← MvPolynomial.support_sum_monomial_coeff p]
    simp only [allNegPoly]; ext b
    simp only [MvPolynomial.coeff_sum, apply_dite (MvPolynomial.coeff b),
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
    by_cases hb_deg : b.degree = m
    · -- Both sides equal MvPolynomial.coeff b p
      -- Helper: dualFinsupp a h₁ = b implies a = inverseDualExp b
      have hinv : ∀ (a : LaurentExp n d) (h₁ : a.negSupport = Finset.univ),
          dualFinsupp d a h₁ = b → a = inverseDualExp d hd b hb_deg := by
        intro a h₁ h₂; refine Subtype.ext (funext fun i => ?_)
        rw [inverseDualExp_apply]
        have := DFunLike.congr_fun h₂ i; rw [dualFinsupp_apply] at this
        have ha := (a.mem_negSupport_iff i).mp (h₁ ▸ Finset.mem_univ i); omega
      set a₀ := inverseDualExp d hd b hb_deg
      have ha₀_ns := inverseDualExp_negSupport d hd b hb_deg
      -- RHS: simplify to coeff b p
      conv_rhs => rw [Finset.sum_ite_eq']
      -- LHS: use Finset.sum_eq_single or sum_eq_zero based on a₀ membership
      by_cases hmem₀ : a₀ ∈
          (monomialCoeff_finite_support (d := d) Finset.univ fval).toFinset
      · -- a₀ ∈ S: LHS = monomialCoeff a₀ fval = coeff b p, RHS = coeff b p
        have key := hmcoeff (inverseDualExp d hd b hb_deg)
          (inverseDualExp_negSupport d hd b hb_deg)
        rw [dualFinsupp_inverseDualExp] at key
        -- key : monomialCoeff a₀ univ fval = coeff b p
        have hcoeff_ne : MvPolynomial.coeff b p ≠ 0 := by
          rw [← key]
          exact ((monomialCoeff_finite_support (d := d) Finset.univ fval).mem_toFinset.mp
            hmem₀).2
        rw [if_pos (MvPolynomial.mem_support_iff.mpr hcoeff_ne)]
        rw [Finset.sum_eq_single a₀ ?_ ?_]
        · rw [dif_pos ha₀_ns, if_pos (dualFinsupp_inverseDualExp d hd b hb_deg)]
          exact key
        · intro a _ hne; by_cases h₁ : a.negSupport = Finset.univ
          · rw [dif_pos h₁]; apply if_neg; intro h₂; exact hne (hinv a h₁ h₂)
          · rw [dif_neg h₁]
        · intro habs; exact absurd hmem₀ habs
      · -- a₀ ∉ S: LHS = 0, coeff b p = 0
        have key := hmcoeff (inverseDualExp d hd b hb_deg)
          (inverseDualExp_negSupport d hd b hb_deg)
        rw [dualFinsupp_inverseDualExp] at key
        -- key : monomialCoeff a₀ univ fval = coeff b p
        have hcoeff_zero : MvPolynomial.coeff b p = 0 := by
          by_contra h
          exact hmem₀ ((monomialCoeff_finite_support (d := d)
            Finset.univ fval).mem_toFinset.mpr
            ⟨Finset.subset_univ _, by rw [key]; exact h⟩)
        rw [if_neg (MvPolynomial.notMem_support_iff.mpr hcoeff_zero)]
        exact Finset.sum_eq_zero fun a _ => by
          by_cases h₁ : a.negSupport = Finset.univ
          · rw [dif_pos h₁]; apply if_neg; intro h₂
            exact hmem₀ (by rw [show a₀ = a from (hinv a h₁ h₂).symm]; assumption)
          · rw [dif_neg h₁]
    · -- Both sides are 0 (degree mismatch / homogeneity)
      rw [Finset.sum_eq_zero (fun v hv => if_neg (fun heq => by
          subst heq; exact hb_deg (hsd v (Finsupp.mem_support_iff.mp hv))))]
      exact Finset.sum_eq_zero fun a _ => by
        by_cases h₁ : a.negSupport = Finset.univ
        · rw [dif_pos h₁]; apply if_neg
          intro h₂; exact hb_deg (by subst h₂; exact dualFinsupp_degree d hd a h₁)
        · simp [dif_neg h₁]
  -- Step 5: ker(ext_map) = range(abToCycles)
  -- Helper: extract coefficient of dualFinsupp(a) from allNegPoly
  have hallneg_of_zero : ∀ (x : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜
      (coordProd n R Finset.univ)),
      allNegPoly d hd x = 0 → ∀ (a : LaurentExp n d) (_ : a.negSupport = Finset.univ),
      monomialCoeff (𝓜 := 𝓜) a Finset.univ x = 0 := by
    intro x hx a ha
    have : MvPolynomial.coeff (dualFinsupp d a ha) (allNegPoly d hd x) = 0 := by
      rw [hx, MvPolynomial.coeff_zero]
    simp only [allNegPoly, MvPolynomial.coeff_sum, apply_dite (MvPolynomial.coeff _),
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at this
    rwa [Finset.sum_eq_single a (fun a' _ hne => by
        by_cases h₁ : a'.negSupport = Finset.univ
        · rw [dif_pos h₁, if_neg]; intro heq
          exact hne (dualFinsupp_injective d hd a' a h₁ ha heq)
        · rw [dif_neg h₁])
      (fun habs => by
        rw [dif_pos ha, if_pos rfl]; by_contra hne
        exact habs ((monomialCoeff_finite_support (d := d) Finset.univ x).mem_toFinset.mpr
          ⟨Finset.subset_univ _, hne⟩)),
      dif_pos ha, if_pos rfl] at this
  have h_ker_eq : ext_map.ker = SA.abToCycles.range := by
    ext ⟨f, hf_ker⟩
    constructor
    · -- ker ⊆ range: ext_map(f) = 0 implies f = SA.f(G)
      intro hext
      rw [AddMonoidHom.mem_ker] at hext
      have hext' : allNegPoly d hd (f ⟨Finset.univ, huniv⟩) = 0 :=
        Subtype.ext_iff.mp hext
      have hallneg := hallneg_of_zero _ hext'
      -- The only face of size n+1 is univ
      have hallneg_T : ∀ (a : LaurentExp n d) (_ : a.negSupport = Finset.univ)
          (T : Finset (Fin (n + 1))) (hT : T.card = n + 1) (_ : a.negSupport ⊆ T),
          monomialCoeff (𝓜 := 𝓜) a T (f ⟨T, hT⟩) = 0 := by
        intro a ha T hT _
        have : T = Finset.univ := by
          rw [← Finset.card_eq_iff_eq_univ]; simpa using hT
        subst this; exact hallneg a ha
      -- Cocycle condition: algebraicδ n f = 0 (target type is empty)
      have hfδ : algebraicδ n R 𝓜 n f = 0 := by
        funext ⟨S, hS⟩
        exact absurd (Finset.card_le_univ S) (by rw [Fintype.card_fin]; omega)
      have hcomp_cocycle : ∀ a : LaurentExp n d,
          _root_.relSimplexδHom a.negSupport R n (componentHom a n f) = 0 := by
        intro a; rw [← component_comm_δ a n f, hfδ, map_zero]
      -- Finite set of nonzero exponents
      set B : Set (LaurentExp n d) :=
        ⋃ T : {T : Finset (Fin (n + 1)) // T.card = n + 1},
          {a : LaurentExp n d | ∃ _ : a.negSupport ⊆ T.1,
            monomialCoeff (𝓜 := 𝓜) a T.1 (f T) ≠ 0}
      have hB_finite : B.Finite :=
        Set.finite_iUnion fun T => monomialCoeff_finite_support T.1 (f T)
      set B_fin := hB_finite.toFinset
      have hne_univ_B : ∀ a ∈ B_fin, a.negSupport ≠ Finset.univ := by
        intro a ha habs
        rw [Set.Finite.mem_toFinset] at ha
        obtain ⟨⟨T, hT⟩, hns, hne⟩ := Set.mem_iUnion.mp ha
        exact hne (hallneg_T a habs T hT hns)
      by_cases hn0 : n = 0
      · -- n = 0: f = 0 since all exponents have negSupport = univ
        subst hn0
        have hf_zero : f = 0 := by
          funext ⟨T, hT⟩
          have : T = Finset.univ := by
            rw [← Finset.card_eq_iff_eq_univ]; simpa using hT
          subst this
          apply monomialCoeffIntShift_determines_zero
          intro a ha
          exact hallneg a (by
            rw [← Finset.card_eq_iff_eq_univ]
            have h1 := Finset.card_le_univ a.negSupport
            have h2 := (hnonempty a).card_pos
            simp only [Fintype.card_fin] at h1 ⊢; omega)
        rw [AddMonoidHom.mem_range]
        exact ⟨0, Subtype.ext (by simp [SA, ShortComplex.abToCycles, hf_zero])⟩
      · -- n ≥ 1: obtain k with n = k + 1 for definitional (k+1)-1+1 = k+1
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have hprev : (ComplexShape.up ℕ).prev (k + 1) = k :=
          ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel k (k + 1) by
            simp [ComplexShape.up_Rel])
        -- Get primitives
        have hprimitive : ∀ (a : LaurentExp (k + 1) d), a ∈ B_fin →
            ∃ ga : _root_.relSimplexCochain a.negSupport R k,
              _root_.relSimplexδHom a.negSupport R k ga =
                componentHom a (k + 1) f := by
          intro a ha_mem
          exact _root_.relSimplexComplex_get_primitive a.negSupport R k
            ((_root_.relSimplexComplex_acyclic a.negSupport R
              (hnonempty a) (hne_univ_B a ha_mem)) (k + 1))
            (componentHom a (k + 1) f)
            (hcomp_cocycle a)
        let ga : (a : LaurentExp (k + 1) d) →
            _root_.relSimplexCochain a.negSupport R k :=
          fun a => if ha : a ∈ B_fin then (hprimitive a ha).choose else 0
        have hga_spec : ∀ (a : LaurentExp (k + 1) d) (ha : a ∈ B_fin),
            _root_.relSimplexδHom a.negSupport R k (ga a) =
              componentHom a (k + 1) f := by
          intro a ha
          show _root_.relSimplexδHom a.negSupport R k
            (if h : a ∈ B_fin then (hprimitive a h).choose else 0) = _
          rw [dif_pos ha]; exact (hprimitive a ha).choose_spec
        have hga_outside : ∀ a, a ∉ B_fin → ga a = 0 := fun a ha => dif_neg ha
        have hcomp_zero_outside : ∀ (a : LaurentExp (k + 1) d), a ∉ B_fin →
            componentHom a (k + 1) f = 0 := by
          intro a ha; ext ⟨T, hT, hns⟩
          simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
          by_contra hne; apply ha; rw [Set.Finite.mem_toFinset]
          exact Set.mem_iUnion.mpr ⟨⟨T, hT⟩, hns, hne⟩
        have hga_spec_all : ∀ a : LaurentExp (k + 1) d,
            _root_.relSimplexδHom a.negSupport R k (ga a) =
              componentHom a (k + 1) f := by
          intro a; by_cases ha_mem : a ∈ B_fin
          · exact hga_spec a ha_mem
          · rw [hga_outside a ha_mem, map_zero, hcomp_zero_outside a ha_mem]
        -- Construct the primitive G at degree k
        set G : ∀ S : {S : Finset (Fin (k + 2)) // S.card = k + 1},
            HomogeneousLocalizedModule.Away (𝒜 (k + 1) R) 𝓜
              (coordProd (k + 1) R S.1) :=
          fun ⟨S, hS⟩ => B_fin.sum fun a =>
            if h : a.negSupport ⊆ S then
              smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
            else 0
        -- Verify algebraicδ k G = f
        have hδG : algebraicδ (k + 1) R 𝓜 k G = f := by
          funext ⟨T, hT⟩
          suffices hsub : algebraicδ (k + 1) R 𝓜 k G ⟨T, hT⟩ - f ⟨T, hT⟩ = 0 from
            sub_eq_zero.mp hsub
          apply monomialCoeffIntShift_determines_zero
          intro b hb
          show (monomialCoeffHom (𝓜 := 𝓜) b T) _ = 0
          rw [map_sub]
          have h_lhs : (monomialCoeffHom (𝓜 := 𝓜) b T)
              (algebraicδ (k + 1) R 𝓜 k G ⟨T, hT⟩) =
              componentHom b (k + 1) (algebraicδ (k + 1) R 𝓜 k G)
                ⟨T, hT, hb⟩ := rfl
          rw [h_lhs, component_comm_δ b k]
          have h_rhs : (monomialCoeffHom (𝓜 := 𝓜) b T) (f ⟨T, hT⟩) =
              componentHom b (k + 1) f ⟨T, hT, hb⟩ := rfl
          rw [h_rhs]
          suffices hcomp_eq : componentHom (𝓜 := 𝓜) b k G = ga b by
            rw [hcomp_eq]; simp [hga_spec_all b]
          ext ⟨S, hS, hb'⟩
          simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          show (monomialCoeffHom (𝓜 := 𝓜) b S) _ = _
          rw [map_sum]
          simp_rw [show ∀ (a : LaurentExp (k + 1) d),
              (monomialCoeffHom (𝓜 := 𝓜) b S)
                (if h : a.negSupport ⊆ S then
                  smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h
                else 0) =
              if h : a.negSupport ⊆ S then
                monomialCoeff b S
                  (smulMonomialElemIntShift (R := R) (ga a ⟨S, hS, h⟩) a S h)
              else 0 from
            fun a => by split_ifs with h <;> [rfl; exact map_zero _]]
          simp_rw [fun (a : LaurentExp (k + 1) d) (h : a.negSupport ⊆ S) =>
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
        -- Transport G to SA.X₁ via XIsoOfEq and prove SA.abToCycles maps to f
        rw [AddMonoidHom.mem_range]
        set G_cast := (A.XIsoOfEq hprev).inv.hom G
        refine ⟨G_cast, Subtype.ext ?_⟩
        show SA.f.hom G_cast = f
        have hSAf_G : SA.f.hom G_cast = (A.d k (k + 1)).hom G := by
          have hsaf : SA.f.hom =
              ((A.XIsoOfEq hprev).hom ≫ A.d k (k + 1)).hom := by
            show (A.d ((ComplexShape.up ℕ).prev (k + 1)) (k + 1)).hom = _
            exact congr_arg AddCommGrp.Hom.hom
              (HomologicalComplex.XIsoOfEq_hom_comp_d A hprev (k + 1)).symm
          rw [hsaf]
          change (A.d k (k + 1)).hom
            ((A.XIsoOfEq hprev).hom.hom ((A.XIsoOfEq hprev).inv.hom G)) = _
          congr 1
          exact DFunLike.congr_fun
            (congr_arg AddCommGrp.Hom.hom
              (Iso.inv_hom_id (A.XIsoOfEq hprev))) G
        rw [hSAf_G, show (A.d k (k + 1)).hom = algebraicδ (k + 1) R 𝓜 k from
          congr_arg AddCommGrp.Hom.hom (hAd k)]
        exact hδG
    · -- range ⊆ ker: f ∈ range(abToCycles) implies ext_map(f) = 0
      intro hrange
      rw [AddMonoidHom.mem_range] at hrange
      obtain ⟨g_prev, hgp⟩ := hrange
      rw [AddMonoidHom.mem_ker,
        show (⟨f, hf_ker⟩ : SA.g.hom.ker) = SA.abToCycles g_prev from hgp.symm]
      show (⟨allNegPoly d hd ((SA.abToCycles g_prev).1 ⟨_, huniv⟩),
        allNegPoly_mem d hd _⟩ : ↥((𝒜 n R) m)) = 0
      refine Subtype.ext ?_
      show allNegPoly d hd (SA.f.hom g_prev ⟨_, huniv⟩) = 0
      -- Show all terms vanish
      simp only [allNegPoly]
      apply Finset.sum_eq_zero; intro a _
      split_ifs with ha
      · suffices hmz : monomialCoeff (𝓜 := 𝓜) a Finset.univ
            (SA.f.hom g_prev ⟨_, huniv⟩) = 0 by
          rw [hmz, MvPolynomial.monomial_zero]
        by_cases hn0 : n = 0
        · subst hn0
          have hfz : SA.f.hom g_prev ⟨_, huniv⟩ = 0 := by
            have : SA.f = 0 :=
              A.shape _ _ (fun h => by simp [ComplexShape.up_Rel] at h)
            rw [show SA.f.hom = 0 from congr_arg AddCommGrp.Hom.hom this,
              AddMonoidHom.zero_apply, Pi.zero_apply]
          rw [hfz]; exact (monomialCoeffHom (𝓜 := 𝓜) a Finset.univ).map_zero
        · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
          have hprev : (ComplexShape.up ℕ).prev (k' + 1) = k' :=
            ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel k' (k' + 1) by
              simp [ComplexShape.up_Rel])
          set g_cast := (A.XIsoOfEq hprev).hom.hom g_prev
          have hSAf_eval : SA.f.hom g_prev ⟨_, huniv⟩ =
              algebraicδ (k' + 1) R 𝓜 k' g_cast ⟨Finset.univ, huniv⟩ := by
            have h1 := DFunLike.congr_fun (congr_arg AddCommGrp.Hom.hom
              (HomologicalComplex.XIsoOfEq_hom_comp_d A hprev (k' + 1)).symm)
              g_prev
            rw [show SA.f.hom g_prev ⟨_, huniv⟩ =
              ((A.XIsoOfEq hprev).hom ≫ A.d k' (k' + 1)).hom g_prev
                ⟨Finset.univ, huniv⟩ from congr_fun h1 ⟨_, huniv⟩]
            change (A.d k' (k' + 1)).hom g_cast ⟨Finset.univ, huniv⟩ = _
            exact congr_fun (DFunLike.congr_fun
              (congr_arg AddCommGrp.Hom.hom (hAd k')) g_cast) ⟨_, huniv⟩
          rw [hSAf_eval]
          show componentHom a (k' + 1) (algebraicδ (k' + 1) R 𝓜 k' g_cast)
            ⟨Finset.univ, huniv, by rw [ha]⟩ = 0
          rw [component_comm_δ a k' g_cast]
          have hempty : IsEmpty {S : Finset (Fin (k' + 2)) //
              S.card = k' + 1 ∧ a.negSupport ⊆ S} := by
            rw [ha]; constructor; intro ⟨S, hS, hunivS⟩
            exact absurd (Finset.card_le_card hunivS)
              (by rw [Finset.card_univ, Fintype.card_fin]; omega)
          rw [show componentHom (𝓜 := 𝓜) a k' g_cast = 0 from
            funext fun x => hempty.elim x, map_zero, Pi.zero_apply]
      · rfl
  -- Step 6: Build quotient equivalence
  exact ((QuotientAddGroup.quotientAddEquivOfEq h_ker_eq.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ext_map h_surj)).toAddCommGrpIso

/-- `Hⁿ(𝒪(-(n+1))) ≅ R`: special case of the general theorem when `d = -(n+1)`,
giving `m = 0` and `𝒜₀ ≅ R` via the constant embedding. -/
noncomputable def algebraicComplex_intShift_Hn_iso :
    (algebraicComplex n R (GradedModule.intShift (𝒜 n R)
      (-(↑(n + 1) : ℤ)))).homology n ≅ AddCommGrp.of R := by
  have hm : (-(-(↑(n + 1) : ℤ)) - ↑(n + 1)).toNat = 0 := by omega
  exact algebraicComplex_intShift_Hn_iso_general (-(↑(n + 1) : ℤ)) le_rfl ≪≫
    (hm ▸ ({ toFun := fun ⟨p, hp⟩ => MvPolynomial.constantCoeff p
             invFun := fun r => ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
             left_inv := fun ⟨p, hp⟩ => by
               simp only [MvPolynomial.mem_homogeneousSubmodule] at hp
               have htd : p.totalDegree = 0 := Nat.le_zero.mp hp.totalDegree_le
               have heq : p = MvPolynomial.C (MvPolynomial.constantCoeff p) := by
                 rw [MvPolynomial.constantCoeff_eq]
                 exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
               exact Subtype.ext heq.symm
             right_inv := fun r => by simp
             map_add' := fun _ _ => map_add _ _ _ } : ↥((𝒜 n R) 0) ≃+ R
           ).toAddCommGrpIso)

end HnNegTwist

end AlgebraicGeometry.Proj
