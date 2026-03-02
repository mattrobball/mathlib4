/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheafCohomology

/-!
# Acyclicity of the structure sheaf on projective space

This file proves the higher cohomology vanishing for the structure sheaf on
projective n-space over a commutative ring `R`:
  `Hᵖ(algebraicComplex, 𝒪) = 0` for `p > 0`

The proof strategy reduces to kernel acyclicity via the splitting
`embeddingChainMap ≫ extractionChainMap = 𝟙`, then decomposes cocycles
by Laurent exponent using monomial coefficient extraction.

## Main results

* `algebraicComplex_acyclic_pos`: `Hᵖ = 0` for `p > 0`

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

/-! ### R-linearity of monomial coefficient extraction -/

section RLinearity

/-- `monomialCoeff` is R-linear with respect to the constant ring embedding:
multiplying by `C(r)/1` scales the extracted coefficient by `r`. -/
theorem monomialCoeff_constRingElemHom_mul (a : LaurentExp n)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S)
    (r : R) (x : HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) :
    monomialCoeff a S hS (constRingElemHom S r * x) =
    r * monomialCoeff a S hS x := by
  unfold monomialCoeff
  rw [HomogeneousLocalization.val_mul]
  refine Localization.induction_on (HomogeneousLocalization.val x) fun ⟨p, s⟩ => ?_
  -- Unfold constRingElemHom and apply mk_mul, but NOT liftOn_mk yet
  simp only [constRingElemHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  -- Simplify denominator: ⟨coordProd^0, ⟨0, rfl⟩⟩ * s = s in the submonoid
  have hden : (⟨(coordProd n R S) ^ 0, ⟨0, rfl⟩⟩ :
      Submonoid.powers (coordProd n R S)) * s = s :=
    Subtype.ext (by simp [Submonoid.coe_mul])
  rw [hden, Localization.liftOn_mk, Localization.liftOn_mk]
  -- Now both sides use s.2.choose
  set cp := a.clearingPow S
  rw [show (coordProd n R S) ^ cp * (MvPolynomial.C r * p) =
    MvPolynomial.C r * ((coordProd n R S) ^ cp * p) from by ring]
  rw [MvPolynomial.coeff_C_mul]

/-- Combined R-linearity and orthogonality: extracting the `a'`-coefficient from
`C(r)/1 * monomialElem(a)` gives `r` when `a' = a` and `0` otherwise. -/
theorem monomialCoeff_constRingElemHom_mul_monomialElem (a a' : LaurentExp n)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S)
    (r : R) :
    monomialCoeff a' S hS' (constRingElemHom S r * monomialElem (R := R) a S hS) =
    if a' = a then r else 0 := by
  rw [monomialCoeff_constRingElemHom_mul a' S hS' r]
  split_ifs with h
  · subst h; rw [monomialCoeff_monomialElem_self, mul_one]
  · rw [monomialCoeff_monomialElem_ne hS' hS h, mul_zero]

end RLinearity

/-! ### Finite support of monomial coefficients -/

section FiniteSupport

/-- For any element of the ring localization, only finitely many Laurent exponents
have nonzero monomial coefficients. -/
theorem monomialCoeff_finite_support (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) :
    {a : LaurentExp n | ∃ hS : a.negSupport ⊆ S,
      monomialCoeff a S hS x ≠ 0}.Finite := by
  revert x; refine Quotient.ind fun q => ?_
  set N := q.den_mem.choose
  set num := (q.num : MvPolynomial (Fin (n + 1)) R)
  let φ : LaurentExp n → Fin (n + 1) →₀ ℕ := fun a =>
    a.numFinsupp S + coordProdFinsupp S N - coordProdFinsupp S (a.clearingPow S)
  have hφ_spec : ∀ a (hns : a.negSupport ⊆ S),
      monomialCoeff a S hns ⟦q⟧ ≠ 0 →
      coordProdFinsupp S (a.clearingPow S) ≤
        a.numFinsupp S + coordProdFinsupp S N ∧
      monomialCoeff a S hns ⟦q⟧ = MvPolynomial.coeff (φ a) num := by
    intro a hns hne
    have hraw : monomialCoeff a S hns ⟦q⟧ =
        MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S N)
          ((coordProd n R S) ^ a.clearingPow S * num) := by
      show (HomogeneousLocalization.val ⟦q⟧).liftOn _ _ = _
      rw [show HomogeneousLocalization.val (⟦q⟧ :
          HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) =
        Localization.mk (↑q.num) ⟨↑q.den, q.den_mem⟩ from rfl,
        Localization.liftOn_mk]
    rw [coordProd_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at hraw
    split_ifs at hraw with h
    · exact ⟨h, by rw [hraw, one_mul]⟩
    · exact (hne hraw).elim
  -- φ maps nonzero set into support(num)
  have hφ_mem : ∀ a ∈ {a | ∃ hns : a.negSupport ⊆ S,
      monomialCoeff a S hns ⟦q⟧ ≠ 0}, φ a ∈ num.support := by
    intro a ⟨hns, hne⟩
    rw [MvPolynomial.mem_support_iff]
    rwa [← (hφ_spec a hns hne).2]
  -- φ is injective on nonzero set
  have hφ_inj : Set.InjOn φ
      {a | ∃ hns : a.negSupport ⊆ S, monomialCoeff a S hns ⟦q⟧ ≠ 0} := by
    intro a ⟨ha_ns, ha_ne⟩ a' ⟨ha'_ns, ha'_ne⟩ hφeq
    refine Subtype.ext (funext fun i => ?_)
    have hφi : (a.numFinsupp S + coordProdFinsupp S N -
        coordProdFinsupp S (a.clearingPow S)) i =
      (a'.numFinsupp S + coordProdFinsupp S N -
        coordProdFinsupp S (a'.clearingPow S)) i :=
      DFunLike.congr_fun hφeq i
    simp only [Finsupp.tsub_apply, Finsupp.add_apply,
      LaurentExp.numFinsupp_apply] at hφi
    by_cases hiS : i ∈ S
    · have hi_a : a.clearingPow S ≤ a.numExp S i + N := by
        have := (hφ_spec a ha_ns ha_ne).1 i
        simp only [Finsupp.add_apply, LaurentExp.numFinsupp_apply,
          coordProdFinsupp_apply_mem hiS] at this
        exact this
      have hi_a' : a'.clearingPow S ≤ a'.numExp S i + N := by
        have := (hφ_spec a' ha'_ns ha'_ne).1 i
        simp only [Finsupp.add_apply, LaurentExp.numFinsupp_apply,
          coordProdFinsupp_apply_mem hiS] at this
        exact this
      simp only [coordProdFinsupp_apply_mem hiS] at hφi
      have hnn_a := a.clearingPow_nonneg S i hiS
      have hnn_a' := a'.clearingPow_nonneg S i hiS
      have hna : (a.numExp S i : ℤ) = a.1 i + ↑(a.clearingPow S) := by
        unfold LaurentExp.numExp; rw [if_pos hiS]; exact Int.toNat_of_nonneg hnn_a
      have hna' : (a'.numExp S i : ℤ) = a'.1 i + ↑(a'.clearingPow S) := by
        unfold LaurentExp.numExp; rw [if_pos hiS]; exact Int.toNat_of_nonneg hnn_a'
      zify [hi_a, hi_a'] at hφi
      linarith
    · simp only [coordProdFinsupp_apply_notMem hiS, add_zero, Nat.sub_zero] at hφi
      have hpos_a : 0 ≤ a.1 i := by
        by_contra h; push_neg at h
        exact hiS (ha_ns ((LaurentExp.mem_negSupport_iff a i).mpr h))
      have hpos_a' : 0 ≤ a'.1 i := by
        by_contra h; push_neg at h
        exact hiS (ha'_ns ((LaurentExp.mem_negSupport_iff a' i).mpr h))
      have hna : a.numExp S i = (a.1 i).toNat := by
        unfold LaurentExp.numExp; exact if_neg hiS
      have hna' : a'.numExp S i = (a'.1 i).toNat := by
        unfold LaurentExp.numExp; exact if_neg hiS
      rw [hna, hna'] at hφi
      omega
  -- Conclude
  exact Set.Finite.of_finite_image
    ((num.support.finite_toSet).subset (Set.image_subset_iff.mpr
      (fun a ha => Finset.mem_coe.mpr (hφ_mem a ha))))
    hφ_inj

/-- Module version of finite support. -/
theorem monomialCoeffMod_finite_support (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S)) :
    {a : LaurentExp n | ∃ hS : a.negSupport ⊆ S,
      monomialCoeffMod a S hS x ≠ 0}.Finite :=
  monomialCoeff_finite_support S ((awayRingModuleEquiv (𝒜 n R)).symm x)

end FiniteSupport

/-! ### Kernel cocycle vanishing -/

section KernelVanishing

/-- A `(p+1)`-cocycle in the algebraic complex with zero extraction is a coboundary.
The proof decomposes by Laurent exponent, uses K_T acyclicity for each component,
and reconstructs a primitive via the finite monomial sum. -/
theorem algebraicCocycle_primitive_of_extraction_zero_pos (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = (p + 1) + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1))
    (hcocycle : algebraicδ n R (𝒜 n R) (p + 1) f = 0)
    (hextract : extractionHom (p + 1) f = 0) :
    ∃ G : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
        HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1),
      algebraicδ n R (𝒜 n R) p G = f := by
  have hcomp_cocycle : ∀ a : LaurentExp n,
      _root_.relSimplexδHom a.negSupport R (p + 1)
        (componentHom a (p + 1) f) = 0 := by
    intro a; rw [← component_comm_δ a (p + 1) f, hcocycle, map_zero]
  have hcomp_zero : componentHom (0 : LaurentExp n) (p + 1) f = 0 := by
    ext ⟨S, hS, hns⟩
    rw [componentHom_zero_apply (p + 1) f hS hns, Pi.zero_apply]
    exact congr_fun hextract ⟨S, hS, Finset.empty_subset S⟩
  set A : Set (LaurentExp n) :=
    ⋃ T : {T : Finset (Fin (n + 1)) // T.card = (p + 1) + 1},
      {a : LaurentExp n | ∃ hS : a.negSupport ⊆ T.1,
        monomialCoeffMod a T.1 hS (f T) ≠ 0}
  have hA_finite : A.Finite :=
    Set.finite_iUnion fun T => monomialCoeffMod_finite_support T.1 (f T)
  set A_fin := hA_finite.toFinset
  have hcomp_zero_outside : ∀ (a : LaurentExp n), a ∉ A_fin →
      componentHom a (p + 1) f = 0 := by
    intro a ha
    ext ⟨T, hT, hns⟩
    simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
    by_contra hne
    apply ha
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨T, hT⟩, hns, hne⟩
  have hprimitive : ∀ (a : LaurentExp n), a ≠ 0 → a ∈ A_fin →
      ∃ ga : _root_.relSimplexCochain a.negSupport R p,
        _root_.relSimplexδHom a.negSupport R p ga =
          componentHom a (p + 1) f := by
    intro a ha _
    have hne : a.negSupport.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty, ne_eq, LaurentExp.negSupport_empty_iff]
    have hne' : a.negSupport ≠ Finset.univ := a.negSupport_ne_univ
    set K := _root_.relSimplexComplex a.negSupport R
    have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom
        (_root_.relSimplexδHom a.negSupport R j) :=
      fun j => by simp [K, _root_.relSimplexComplex]
    have hexact := (_root_.relSimplexComplex_acyclic a.negSupport R hne hne') (p + 1)
    rw [HomologicalComplex.exactAt_iff' K p (p + 1) (p + 2)
      (by simp) (by simp), ShortComplex.ab_exact_iff] at hexact
    have hker : (K.sc' p (p + 1) (p + 2)).g.hom
        (componentHom a (p + 1) f) = 0 := by
      show K.d (p + 1) (p + 2) (componentHom a (p + 1) f) = 0
      rw [hKd]; exact hcomp_cocycle a
    obtain ⟨ga, hga⟩ := hexact _ hker
    exact ⟨ga, by rwa [show (K.sc' p (p + 1) (p + 2)).f =
      K.d p (p + 1) from rfl, hKd] at hga⟩
  let ga : (a : LaurentExp n) → _root_.relSimplexCochain a.negSupport R p :=
    fun a => if ha : a ≠ 0 ∧ a ∈ A_fin then (hprimitive a ha.1 ha.2).choose else 0
  have hga_spec : ∀ (a : LaurentExp n) (ha1 : a ≠ 0) (ha2 : a ∈ A_fin),
      _root_.relSimplexδHom a.negSupport R p (ga a) =
        componentHom a (p + 1) f := by
    intro a ha1 ha2
    change _root_.relSimplexδHom a.negSupport R p
      (if ha : a ≠ 0 ∧ a ∈ A_fin then (hprimitive a ha.1 ha.2).choose else 0) = _
    split_ifs with h
    · exact (hprimitive a h.1 h.2).choose_spec
    · exact absurd ⟨ha1, ha2⟩ h
  have hga_zero : ga 0 = 0 := by
    change (if ha : (0 : LaurentExp n) ≠ 0 ∧ _ then _ else 0) = 0
    split_ifs with h
    · exact absurd rfl h.1
    · rfl
  have hga_outside : ∀ a, a ∉ A_fin → ga a = 0 := by
    intro a ha
    change (if h : a ≠ 0 ∧ a ∈ A_fin then _ else 0) = 0
    split_ifs with h
    · exact absurd h.2 ha
    · rfl
  have hga_spec_all : ∀ a : LaurentExp n,
      _root_.relSimplexδHom a.negSupport R p (ga a) =
        componentHom a (p + 1) f := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0; rw [hga_zero, map_zero]; exact hcomp_zero.symm
    · by_cases ha_mem : a ∈ A_fin
      · exact hga_spec a ha0 ha_mem
      · rw [hga_outside a ha_mem, map_zero]
        exact (hcomp_zero_outside a ha_mem).symm
  refine ⟨fun ⟨S, hS⟩ =>
    A_fin.sum fun a =>
      if h : a.negSupport ⊆ S then
        (awayRingModuleEquiv (𝒜 n R))
          (constRingElemHom S (ga a ⟨S, hS, h⟩) *
          monomialElem (R := R) a S h)
      else 0, ?_⟩
  funext ⟨T, hT⟩
  suffices h : algebraicδ n R (𝒜 n R) p (fun ⟨S, hS⟩ =>
      A_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          (awayRingModuleEquiv (𝒜 n R))
            (constRingElemHom S (ga a ⟨S, hS, h⟩) *
            monomialElem (R := R) a S h)
        else 0) ⟨T, hT⟩ - f ⟨T, hT⟩ = 0 from sub_eq_zero.mp h
  apply monomialCoeffMod_determines_zero
  intro b hb
  rw [map_sub]
  have h_lhs : monomialCoeffMod b T hb (algebraicδ n R (𝒜 n R) p (fun ⟨S, hS⟩ =>
      A_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          (awayRingModuleEquiv (𝒜 n R))
            (constRingElemHom S (ga a ⟨S, hS, h⟩) *
            monomialElem (R := R) a S h)
        else 0) ⟨T, hT⟩) =
      componentHom b (p + 1) (algebraicδ n R (𝒜 n R) p (fun ⟨S, hS⟩ =>
        A_fin.sum fun a =>
          if h : a.negSupport ⊆ S then
            (awayRingModuleEquiv (𝒜 n R))
              (constRingElemHom S (ga a ⟨S, hS, h⟩) *
              monomialElem (R := R) a S h)
          else 0)) ⟨T, hT, hb⟩ := rfl
  rw [h_lhs, component_comm_δ b p]
  have h_rhs : monomialCoeffMod b T hb (f ⟨T, hT⟩) =
      componentHom b (p + 1) f ⟨T, hT, hb⟩ := rfl
  rw [h_rhs]
  suffices hcomp_eq : componentHom b p
      (fun ⟨S, hS⟩ => A_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          (awayRingModuleEquiv (𝒜 n R))
            (constRingElemHom S (ga a ⟨S, hS, h⟩) *
            monomialElem (R := R) a S h)
        else 0) = ga b by
    rw [hcomp_eq]; simp [hga_spec_all b]
  ext ⟨S, hS, hb'⟩
  simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [map_sum]
  simp_rw [show ∀ (a : LaurentExp n),
    monomialCoeffMod b S hb'
      (if h : a.negSupport ⊆ S then
        (awayRingModuleEquiv (𝒜 n R))
          (constRingElemHom S (ga a ⟨S, hS, h⟩) *
          monomialElem (R := R) a S h)
      else 0) =
    if h : a.negSupport ⊆ S then
      monomialCoeff b S hb'
        (constRingElemHom S (ga a ⟨S, hS, h⟩) *
        monomialElem (R := R) a S h)
    else 0 from fun a => by split_ifs with h <;> [rfl; exact map_zero _]]
  simp_rw [fun (a : LaurentExp n) (h : a.negSupport ⊆ S) =>
    monomialCoeff_constRingElemHom_mul_monomialElem a b S h hb'
      (ga a ⟨S, hS, h⟩)]
  by_cases hb_mem : b ∈ A_fin
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

end KernelVanishing

/-! ### Main acyclicity theorem -/

section Acyclicity

/-- `Hᵖ(algebraicComplex) = 0` for `p > 0`: the higher cohomology of the
structure sheaf on projective n-space vanishes. -/
theorem algebraicComplex_acyclic_pos (p : ℕ) :
    IsZero ((algebraicComplex n R (𝒜 n R)).homology (p + 1)) := by
  set A := algebraicComplex n R (𝒜 n R)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  have hAd : ∀ j, A.d j (j + 1) = AddCommGrp.ofHom
      (algebraicδ n R (𝒜 n R) j) :=
    fun j => by simp [A, algebraicComplex]
  rw [HomologicalComplex.exactAt_iff' A p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro f hf
  have hg : (A.sc' p (p + 1) (p + 2)).g = A.d (p + 1) (p + 2) := rfl
  have hfi : (A.sc' p (p + 1) (p + 2)).f = A.d p (p + 1) := rfl
  -- f is a (p+1)-cocycle
  have hfδ : algebraicδ n R (𝒜 n R) (p + 1) f = 0 := by rw [hg, hAd] at hf; exact hf
  -- extractionHom(p+1)(f) is a (p+1)-cochain in K_∅ that is a cocycle
  have hext_cocycle : _root_.relSimplexδHom (∅ : Finset (Fin (n + 1))) R (p + 1)
      (extractionHom (p + 1) f) = 0 := by
    have h := extraction_comm_δ (p + 1) f
    rw [hfδ, map_zero] at h; exact h.symm
  -- K_∅ exact at (p+1): get primitive e with δ_p(e) = extraction(f)
  have ⟨e, he⟩ : ∃ e : _root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R p,
      _root_.relSimplexδHom ∅ R p e = extractionHom (p + 1) f := by
    set K := _root_.relSimplexComplex (∅ : Finset (Fin (n + 1))) R
    have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom
        (_root_.relSimplexδHom ∅ R j) :=
      fun j => by simp [K, _root_.relSimplexComplex]
    have hexact := _root_.relSimplexComplex_empty_exactAt (n := n) R p
    rw [HomologicalComplex.exactAt_iff' K p (p + 1) (p + 2)
      (by simp) (by simp), ShortComplex.ab_exact_iff] at hexact
    have hker : (K.sc' p (p + 1) (p + 2)).g.hom
        (extractionHom (p + 1) f) = 0 := by
      show K.d (p + 1) (p + 2) (extractionHom (p + 1) f) = 0
      rw [hKd]; exact hext_cocycle
    obtain ⟨e, he⟩ := hexact _ hker
    exact ⟨e, by rwa [show (K.sc' p (p + 1) (p + 2)).f =
      K.d p (p + 1) from rfl, hKd] at he⟩
  -- d²=0: algebraicδ (p+1) ∘ algebraicδ p = 0
  have hdd : ∀ x, algebraicδ n R (𝒜 n R) (p + 1)
      (algebraicδ n R (𝒜 n R) p x) = 0 := by
    intro x
    have h1 := AddCommGrp.comp_apply
      (AddCommGrp.ofHom (algebraicδ n R (𝒜 n R) p))
      (AddCommGrp.ofHom (algebraicδ n R (𝒜 n R) (p + 1))) x
    rw [algebraicδ_comp_algebraicδ] at h1
    simpa using h1.symm
  -- Eta-expand f to concrete Pi type to avoid HSub synthesis issues
  let fc : ∀ S : {S : Finset (Fin (n + 1)) // S.card = (p + 1) + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1) :=
    fun S => f S
  -- f' = fc - δ_p(embedding_p(e))
  let emb_e := algebraicδ n R (𝒜 n R) p (embeddingHom p e)
  let f' := fc - emb_e
  have hf'_cocycle : algebraicδ n R (𝒜 n R) (p + 1) f' = 0 := by
    show algebraicδ n R (𝒜 n R) (p + 1) (fc - emb_e) = 0
    rw [map_sub, show algebraicδ n R (𝒜 n R) (p + 1) fc = 0 from hfδ,
      zero_sub, neg_eq_zero]; exact hdd _
  have hf'_extract : extractionHom (p + 1) f' = 0 := by
    show extractionHom (p + 1) (fc - emb_e) = 0
    rw [map_sub,
      show extractionHom (p + 1) emb_e =
        _root_.relSimplexδHom ∅ R p (extractionHom p (embeddingHom p e)) from
          extraction_comm_δ p (embeddingHom p e),
      extraction_embedding_eq p e, he, sub_self]
  -- Apply kernel vanishing
  obtain ⟨G', hG'⟩ := algebraicCocycle_primitive_of_extraction_zero_pos p f'
    hf'_cocycle hf'_extract
  -- f = δ_p(embedding_p(e) + G')
  exact ⟨embeddingHom p e + G', by
    rw [hfi, hAd]
    show algebraicδ n R (𝒜 n R) p (embeddingHom p e + G') = f
    rw [map_add, show algebraicδ n R (𝒜 n R) p (embeddingHom p e) = emb_e from rfl, hG']
    show emb_e + (fc - emb_e) = f
    simp [show fc = f from rfl]⟩

end Acyclicity

end AlgebraicGeometry.Proj
