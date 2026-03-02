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
  simp only [constRingElemHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul, Localization.liftOn_mk]
  dsimp only [Prod.fst, Prod.snd]
  set nf := a.numFinsupp S
  set cp := a.clearingPow S
  set Ns := s.2.choose
  set M := (⟨(coordProd n R S) ^ 0, ⟨0, rfl⟩⟩ * s :
    Submonoid.powers (coordProd n R S)).2.choose
  have hpow_eq : (coordProd n R S) ^ M = (coordProd n R S) ^ Ns := by
    have hM := (⟨(coordProd n R S) ^ 0, ⟨0, rfl⟩⟩ * s :
      Submonoid.powers (coordProd n R S)).2.choose_spec
    simp only [Submonoid.coe_mul, pow_zero, one_mul] at hM
    rw [hM, s.2.choose_spec]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S nf hpow_eq
    ((coordProd n R S) ^ cp * (MvPolynomial.C r * p))]
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
have nonzero monomial coefficients. The proof follows `monomialCoeff_determines_zero`:
for each `a` with nonzero coefficient, construct `m ∈ support(q.num)` with
`a = toLaurent(m)`, giving an injection into a finite set. -/
theorem monomialCoeff_finite_support (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) :
    {a : LaurentExp n | ∃ hS : a.negSupport ⊆ S,
      monomialCoeff a S hS x ≠ 0}.Finite := by
  revert x; refine Quotient.ind fun q => ?_
  set N := q.den_mem.choose with hN_def
  set num := (q.num : MvPolynomial (Fin (n + 1)) R) with hnum_def
  -- If num = 0, then x = 0 and all coefficients vanish.
  by_cases hnum_zero : num = 0
  · convert Set.finite_empty
    ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro hns
    have hx_zero : (⟦q⟧ : HomogeneousLocalization.Away (𝒜 n R)
        (coordProd n R S)) = 0 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_zero]
      show HomogeneousLocalization.NumDenSameDeg.embedding _ _ q = 0
      simp only [HomogeneousLocalization.NumDenSameDeg.embedding, hnum_def,
        hnum_zero, Localization.mk_zero]
    rw [hx_zero]
    show monomialCoeff a S hns 0 = 0
    unfold monomialCoeff
    rw [HomogeneousLocalization.val_zero]
    change (0 : Localization (Submonoid.powers (coordProd n R S))).liftOn _ _ = 0
    rw [show (0 : Localization (Submonoid.powers (coordProd n R S))) =
      Localization.mk 0 1 from (Localization.mk_zero 1).symm, Localization.liftOn_mk]
    simp [mul_zero, MvPolynomial.coeff_zero]
  -- num ≠ 0: inject into support(num) which is finite
  apply Set.Finite.subset (num.support.finite_toSet)
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  obtain ⟨hns, hne⟩ := ha
  set cp := a.clearingPow S
  have hindex : a.numFinsupp S + coordProdFinsupp S N =
      coordProdFinsupp S cp + Finsupp.equivFunOnFinite.symm (fun i =>
        if i ∈ S then a.numExp S i + N - cp else a.numExp S i) := by
    ext i; by_cases hiS : i ∈ S
    · simp only [Finsupp.coe_add, Pi.add_apply, LaurentExp.numFinsupp_apply,
        coordProdFinsupp_apply_mem hiS, Finsupp.equivFunOnFinite_symm_apply_toFun,
        if_pos hiS]
      have hnn := a.clearingPow_nonneg S i hiS
      omega
    · simp only [Finsupp.coe_add, Pi.add_apply, LaurentExp.numFinsupp_apply,
        coordProdFinsupp_apply_notMem hiS, Finsupp.equivFunOnFinite_symm_apply_toFun,
        if_neg hiS, add_zero, zero_add]
  set m := Finsupp.equivFunOnFinite.symm (fun i =>
    if i ∈ S then a.numExp S i + N - cp else a.numExp S i) with hm_def
  have hcoeff : monomialCoeff a S hns ⟦q⟧ = MvPolynomial.coeff m num := by
    show (HomogeneousLocalization.val ⟦q⟧).liftOn _ _ = _
    rw [show HomogeneousLocalization.val (⟦q⟧ :
        HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) =
      Localization.mk (↑q.num) ⟨↑q.den, q.den_mem⟩ from rfl,
      Localization.liftOn_mk, hindex]
    exact coeff_coordProd_pow_mul S _ m _
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  exact hcoeff ▸ hne

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
  -- For each Laurent exponent a, componentHom a (p+1) f is a cocycle in K_{negSupport(a)}
  have hcomp_cocycle : ∀ a : LaurentExp n,
      _root_.relSimplexδHom a.negSupport R (p + 1)
        (componentHom a (p + 1) f) = 0 := by
    intro a; rw [← component_comm_δ a (p + 1) f, hcocycle, map_zero]
  -- For a = 0, componentHom 0 f = 0
  have hcomp_zero : componentHom (0 : LaurentExp n) (p + 1) f = 0 := by
    ext ⟨S, hS, hns⟩
    rw [componentHom_zero_apply (p + 1) f hS hns, Pi.zero_apply]
    exact congr_fun hextract ⟨S, hS, Finset.empty_subset S⟩
  -- Collect the finite set of all Laurent exponents with nonzero component
  set A : Set (LaurentExp n) :=
    ⋃ T : {T : Finset (Fin (n + 1)) // T.card = (p + 1) + 1},
      {a : LaurentExp n | ∃ hS : a.negSupport ⊆ T.1,
        monomialCoeffMod a T.1 hS (f T) ≠ 0}
  have hA_finite : A.Finite := Set.Finite.biUnion (Set.finite_range _)
    (fun ⟨T, hT⟩ _ => monomialCoeffMod_finite_support T.1 (f ⟨T, hT⟩))
  set A_fin := hA_finite.toFinset
  -- Key: if a ∉ A_fin then componentHom a (p+1) f = 0
  have hcomp_zero_outside : ∀ (a : LaurentExp n), a ∉ A_fin →
      componentHom a (p + 1) f = 0 := by
    intro a ha
    ext ⟨T, hT, hns⟩
    simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
    by_contra hne
    exact ha (Set.Finite.mem_toFinset.mpr
      (Set.mem_iUnion.mpr ⟨⟨T, hT⟩, hns, hne⟩))
  -- For a ≠ 0 AND a ∈ A_fin, K_{negSupport(a)} is exact, giving primitives
  have hprimitive : ∀ (a : LaurentExp n), a ≠ 0 → a ∈ A_fin →
      ∃ ga : _root_.relSimplexCochain a.negSupport R (p + 1),
        _root_.relSimplexδHom a.negSupport R (p + 1) ga =
          componentHom a (p + 1) f := by
    intro a ha _
    have hne : a.negSupport.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty, ne_eq, LaurentExp.negSupport_empty_iff]
    have hne' : a.negSupport ≠ Finset.univ := a.negSupport_ne_univ
    set K := _root_.relSimplexComplex a.negSupport R
    have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom
        (_root_.relSimplexδHom a.negSupport R j) :=
      fun j => by simp [K, _root_.relSimplexComplex]
    have hexact := (_root_.relSimplexComplex_acyclic a.negSupport R hne hne') (p + 2)
    rw [HomologicalComplex.exactAt_iff' K (p + 1) (p + 2) (p + 3)
      (by simp) (by simp), ShortComplex.ab_exact_iff] at hexact
    have hker : (K.sc' (p + 1) (p + 2) (p + 3)).g.hom
        (componentHom a (p + 1) f) = 0 := by
      show K.d (p + 2) (p + 3) (componentHom a (p + 1) f) = 0
      rw [hKd]; exact hcomp_cocycle a
    obtain ⟨ga, hga⟩ := hexact _ hker
    exact ⟨ga, by rwa [show (K.sc' (p + 1) (p + 2) (p + 3)).f =
      K.d (p + 1) (p + 2) from rfl, hKd] at hga⟩
  -- Choose primitives: 0 for a = 0 or a ∉ A_fin; chosen primitive otherwise
  let ga : (a : LaurentExp n) → _root_.relSimplexCochain a.negSupport R (p + 1) :=
    fun a => if ha : a ≠ 0 ∧ a ∈ A_fin then (hprimitive a ha.1 ha.2).choose else 0
  have hga_spec : ∀ (a : LaurentExp n) (ha1 : a ≠ 0) (ha2 : a ∈ A_fin),
      _root_.relSimplexδHom a.negSupport R (p + 1) (ga a) =
        componentHom a (p + 1) f := by
    intro a ha1 ha2
    simp only [ga, dif_pos ⟨ha1, ha2⟩]
    exact (hprimitive a ha1 ha2).choose_spec
  -- ga 0 = 0
  have hga_zero : ga 0 = 0 := by
    simp only [ga, show ¬((0 : LaurentExp n) ≠ 0 ∧ (0 : LaurentExp n) ∈ A_fin) from
      fun h => h.1 rfl, dif_neg (not_false)]
  -- ga a = 0 when a ∉ A_fin
  have hga_outside : ∀ a, a ∉ A_fin → ga a = 0 := by
    intro a ha
    simp only [ga, show ¬(a ≠ 0 ∧ a ∈ A_fin) from fun h => ha h.2, dif_neg (not_false)]
  -- Key: δ(ga a) = componentHom a (p+1) f for ALL a
  have hga_spec_all : ∀ a : LaurentExp n,
      _root_.relSimplexδHom a.negSupport R (p + 1) (ga a) =
        componentHom a (p + 1) f := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0; rw [hga_zero, map_zero]; exact hcomp_zero.symm
    · by_cases ha_mem : a ∈ A_fin
      · exact hga_spec a ha0 ha_mem
      · rw [hga_outside a ha_mem, map_zero]
        exact (hcomp_zero_outside a ha_mem).symm
  -- Define the primitive G using the finite monomial sum
  refine ⟨fun ⟨S, hS⟩ =>
    A_fin.sum fun a =>
      if h : a.negSupport ⊆ S then
        (awayRingModuleEquiv (𝒜 n R))
          (constRingElemHom S (ga a ⟨S, hS, h⟩) *
          monomialElem (R := R) a S h)
      else 0, ?_⟩
  -- Verify δG = f by showing all monomial coefficients agree
  funext ⟨T, hT⟩
  apply monomialCoeffMod_determines_zero
  intro b hb
  -- Show: monomialCoeffMod b T hb (δG(T) - f(T)) = 0
  rw [show monomialCoeffMod b T.1 hb ((algebraicδ n R (𝒜 n R) p _ ⟨T, hT⟩) -
    f ⟨T, hT⟩) =
    monomialCoeffMod b T.1 hb (algebraicδ n R (𝒜 n R) p _ ⟨T, hT⟩) -
    monomialCoeffMod b T.1 hb (f ⟨T, hT⟩) from map_sub _ _ _]
  suffices h : monomialCoeffMod b T.1 hb (algebraicδ n R (𝒜 n R) p _ ⟨T, hT⟩) =
      monomialCoeffMod b T.1 hb (f ⟨T, hT⟩) from by rw [h, sub_self]
  -- LHS = componentHom b (p+1) (δG) at ⟨T, hT, hb⟩
  -- = (relSimplexδ (componentHom b p G)) ⟨T, hT, hb⟩ (by component_comm_δ)
  have h_lhs : monomialCoeffMod b T.1 hb (algebraicδ n R (𝒜 n R) p _ ⟨T, hT⟩) =
      componentHom b (p + 1) (algebraicδ n R (𝒜 n R) p _) ⟨T, hT, hb⟩ := rfl
  rw [h_lhs, component_comm_δ b p]
  change _root_.relSimplexδHom b.negSupport R p
      (componentHom b p _) ⟨T, hT, hb⟩ =
    componentHom b (p + 1) f ⟨T, hT, hb⟩
  -- Suffices: componentHom b p G = ga b, then use hga_spec_all
  suffices hcomp_eq : componentHom b p
      (fun ⟨S, hS⟩ => A_fin.sum fun a =>
        if h : a.negSupport ⊆ S then
          (awayRingModuleEquiv (𝒜 n R))
            (constRingElemHom S (ga a ⟨S, hS, h⟩) *
            monomialElem (R := R) a S h)
        else 0) = ga b by
    rw [hcomp_eq]
    exact congr_fun (hga_spec_all b) ⟨T, hT, hb⟩
  -- Prove componentHom b p G = ga b pointwise
  ext ⟨S, hS, hb'⟩
  simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [map_sum]
  -- Each term: by orthogonality
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
  -- Sum of (if h then (if b = a then ga a S else 0) else 0) over A_fin
  by_cases hb_mem : b ∈ A_fin
  · -- b ∈ A_fin: single nonzero term at a = b
    rw [Finset.sum_eq_single b]
    · simp only [dif_pos hb', eq_self_iff_true, ↓reduceIte]
    · intro a _ hab; simp [show b ≠ a from Ne.symm hab]
    · intro habs; exact absurd hb_mem habs
  · -- b ∉ A_fin: ga b = 0, and sum is 0 since b ∉ A_fin
    rw [Finset.sum_eq_zero, hga_outside b hb_mem, Pi.zero_apply]
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
  -- f is a (p+1)-cocycle: algebraicδ (p+1) f = 0
  have hf' : algebraicδ n R (𝒜 n R) (p + 1) f = 0 := by rw [hg, hAd] at hf; exact hf
  -- extractionHom(f) is a cocycle in K_∅
  have hext_cocycle : _root_.relSimplexδHom (∅ : Finset (Fin (n + 1))) R (p + 1)
      (extractionHom (p + 1) f) = 0 := by
    rw [← extraction_comm_δ (p + 1) f, hf', map_zero]
  -- K_∅ is exact at degree p+2, so extractionHom(f) is a coboundary
  have ⟨e, he⟩ : ∃ e : _root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R (p + 1),
      _root_.relSimplexδHom ∅ R (p + 1) e = extractionHom (p + 1) f := by
    set K := _root_.relSimplexComplex (∅ : Finset (Fin (n + 1))) R
    have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom
        (_root_.relSimplexδHom ∅ R j) :=
      fun j => by simp [K, _root_.relSimplexComplex]
    have hexact := _root_.relSimplexComplex_empty_exactAt (n := n) R (p + 1)
    rw [HomologicalComplex.exactAt_iff' K (p + 1) (p + 2) (p + 3)
      (by simp) (by simp), ShortComplex.ab_exact_iff] at hexact
    have hker : (K.sc' (p + 1) (p + 2) (p + 3)).g.hom
        (extractionHom (p + 1) f) = 0 := by
      show K.d (p + 2) (p + 3) (extractionHom (p + 1) f) = 0
      rw [hKd]; exact hext_cocycle
    obtain ⟨e, he⟩ := hexact _ hker
    exact ⟨e, by rwa [show (K.sc' (p + 1) (p + 2) (p + 3)).f =
      K.d (p + 1) (p + 2) from rfl, hKd] at he⟩
  -- Set f' = f - δ(embedding(e)), verify f' is a cocycle with zero extraction
  set f' := f - algebraicδ n R (𝒜 n R) p (embeddingHom p e)
  have hf'_cocycle : algebraicδ n R (𝒜 n R) (p + 1) f' = 0 := by
    simp only [f', map_sub, hf']
    rw [show algebraicδ n R (𝒜 n R) (p + 1)
        (algebraicδ n R (𝒜 n R) p (embeddingHom p e)) = 0 from by
      have := algebraicδ_comp_algebraicδ n R (𝒜 n R) p
      rw [show (AddCommGrp.ofHom (algebraicδ n R (𝒜 n R) p) ≫
        AddCommGrp.ofHom (algebraicδ n R (𝒜 n R) (p + 1))) =
        AddCommGrp.ofHom ((algebraicδ n R (𝒜 n R) (p + 1)).comp
          (algebraicδ n R (𝒜 n R) p)) from rfl] at this
      exact congr_fun (congr_arg AddMonoidHom.toFun
        (AddCommGrp.ofHom_injective this)) (embeddingHom p e)]
    simp
  have hf'_extract : extractionHom (p + 1) f' = 0 := by
    simp only [f', map_sub]
    rw [show extractionHom (p + 1) (algebraicδ n R (𝒜 n R) p (embeddingHom p e)) =
      _root_.relSimplexδHom ∅ R p (extractionHom p (embeddingHom p e)) from
        extraction_comm_δ p (embeddingHom p e)]
    rw [extraction_embedding_eq p e, he, sub_self]
  -- Apply kernel vanishing to f'
  obtain ⟨G', hG'⟩ := algebraicCocycle_primitive_of_extraction_zero_pos p f'
    hf'_cocycle hf'_extract
  -- f = δ(embedding(e) + G')
  refine ⟨embeddingHom p e + G', ?_⟩
  rw [hfi, hAd]
  show algebraicδ n R (𝒜 n R) p (embeddingHom p e + G') = f
  rw [map_add, hG']; simp [f']

end Acyclicity

end AlgebraicGeometry.Proj
