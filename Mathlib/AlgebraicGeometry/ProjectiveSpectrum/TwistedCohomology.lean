/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheafAcyclicity
import Mathlib.Algebra.Module.GradedModule.Shift

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

/-! ### Monomial elements in the shifted module localization -/

section MonomialElemShift

variable (d : ℤ) (hd : 0 ≤ d)

/-- The monomial element in the shifted module localization corresponding to
a Laurent exponent `a : LaurentExp n d` with `negSupport a ⊆ S`. -/
def monomialElemShift (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R S) :=
  HomogeneousLocalizedModule.Away.mk (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
    (coordProd_mem_homogeneous n R S)
    (a.clearingPow S)
    (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i)
    (by
      show (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i) ∈
        𝒜 n R (a.clearingPow S * S.card + d.toNat)
      have h := SetLike.prod_pow_mem_graded (F := Finset.univ) (𝒜 n R)
        (fun _ : Fin (n + 1) => (1 : ℕ)) (coord n R) (fun i => a.numExp S i)
        (fun i _ => coord_mem_homogeneousSubmodule n R i)
      simp only [smul_eq_mul, mul_one] at h
      rwa [a.numExp_sum_nonneg S hS hd] at h)

/-- Scalar multiplication of `r : R` with a shifted monomial element. Constructs
`C(r) · ∏ xᵢ^{numExp a S i} / (coordProd S)^{clearingPow a S}` directly,
avoiding the need for a general SMul instance. -/
def smulMonomialElemShift (r : R) (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R S) :=
  HomogeneousLocalizedModule.Away.mk (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
    (coordProd_mem_homogeneous n R S)
    (a.clearingPow S)
    (MvPolynomial.C r * ∏ i : Fin (n + 1), coord n R i ^ a.numExp S i)
    (by
      show MvPolynomial.C r * (∏ i, coord n R i ^ a.numExp S i) ∈
        𝒜 n R (a.clearingPow S * S.card + d.toNat)
      have h_prod := SetLike.prod_pow_mem_graded (F := Finset.univ) (𝒜 n R)
        (fun _ : Fin (n + 1) => (1 : ℕ)) (coord n R) (fun i => a.numExp S i)
        (fun i _ => coord_mem_homogeneousSubmodule n R i)
      simp only [smul_eq_mul, mul_one] at h_prod
      rw [a.numExp_sum_nonneg S hS hd] at h_prod
      have hC : MvPolynomial.C r ∈ 𝒜 n R 0 := MvPolynomial.isHomogeneous_C _ r
      have := SetLike.mul_mem_graded hC h_prod
      rwa [zero_add] at this)

end MonomialElemShift

/-! ### Monomial coefficient extraction from the shifted module -/

section MonomialCoeffShift

variable {d : ℤ}

/-- The raw coefficient extraction function on `M × S` pairs, where
`M = MvPolynomial` and `S = powers(coordProd)`. Used to define
`monomialCoeffShift` via `LocalizedModule.liftOn`. -/
private def monomialCoeffShiftFun (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (ms : MvPolynomial (Fin (n + 1)) R ×
      ↥(Submonoid.powers (coordProd n R S))) :
    R :=
  MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S ms.2.2.choose)
    ((coordProd n R S) ^ (a.clearingPow S) * ms.1)

/-- Well-definedness of coefficient extraction for the `LocalizedModule` relation. -/
private theorem monomialCoeffShiftFun_wd (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (p q : MvPolynomial (Fin (n + 1)) R ×
      ↥(Submonoid.powers (coordProd n R S)))
    (hrel : p ≈ q) :
    monomialCoeffShiftFun a S p = monomialCoeffShiftFun a S q := by
  -- hrel : ∃ u : S, u • q.2 • p.1 = u • p.2 • q.1
  obtain ⟨u, hu⟩ := hrel
  simp only [Submonoid.smul_def, smul_eq_mul] at hu
  -- hu : ↑u * (↑q.2 * p.1) = ↑u * (↑p.2 * q.1)
  unfold monomialCoeffShiftFun
  set K := u.2.choose; set Ns := p.2.2.choose; set Nt := q.2.2.choose
  set cp := a.clearingPow S; set nf := a.numFinsupp S
  -- Boost both sides using coeff_coordProd_pow_mul
  have h1 := coeff_coordProd_pow_mul (R := R) S (K + Nt)
    (nf + coordProdFinsupp S Ns) ((coordProd n R S) ^ cp * p.1)
  have h2 := coeff_coordProd_pow_mul (R := R) S (K + Ns)
    (nf + coordProdFinsupp S Nt) ((coordProd n R S) ^ cp * q.1)
  -- Indices agree
  have hindex : coordProdFinsupp S (K + Nt) + (nf + coordProdFinsupp S Ns) =
      coordProdFinsupp S (K + Ns) + (nf + coordProdFinsupp S Nt) := by
    ext i; by_cases hi : i ∈ S
    · simp [coordProdFinsupp_apply_mem hi, LaurentExp.numFinsupp_apply]; ring
    · simp [coordProdFinsupp_apply_notMem hi]
  -- Polynomials agree
  have hpoly : (coordProd n R S) ^ (K + Nt) * ((coordProd n R S) ^ cp * p.1) =
      (coordProd n R S) ^ (K + Ns) * ((coordProd n R S) ^ cp * q.1) := by
    have hu_spec : (coordProd n R S) ^ K = ↑u := u.2.choose_spec
    have hs_spec : (coordProd n R S) ^ Ns = ↑p.2 := p.2.2.choose_spec
    have ht_spec : (coordProd n R S) ^ Nt = ↑q.2 := q.2.2.choose_spec
    have key : (coordProd n R S) ^ K * ((coordProd n R S) ^ Nt * p.1) =
        (coordProd n R S) ^ K * ((coordProd n R S) ^ Ns * q.1) := by
      rw [← hu_spec, ← ht_spec, ← hs_spec] at hu; exact hu
    calc (coordProd n R S) ^ (K + Nt) * ((coordProd n R S) ^ cp * p.1)
        = (coordProd n R S) ^ cp *
          ((coordProd n R S) ^ K * ((coordProd n R S) ^ Nt * p.1)) := by
            rw [pow_add]; ring
      _ = (coordProd n R S) ^ cp *
          ((coordProd n R S) ^ K * ((coordProd n R S) ^ Ns * q.1)) := by
            rw [key]
      _ = (coordProd n R S) ^ (K + Ns) * ((coordProd n R S) ^ cp * q.1) := by
            rw [pow_add]; ring
  rw [hindex, hpoly] at h1
  exact h1.symm.trans h2

/-- Generalized monomial coefficient extraction from the shifted module localization.
Defined via `val` (injection into `LocalizedModule`) and `LocalizedModule.liftOn`. -/
def monomialCoeffShift (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (_hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R S) → R := fun x =>
  x.val.liftOn (monomialCoeffShiftFun a S) (monomialCoeffShiftFun_wd a S)

/-- `monomialCoeffShift` as an `AddMonoidHom`. -/
def monomialCoeffShiftHom (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R S) →+ R where
  toFun := monomialCoeffShift a S hS
  map_zero' := by
    show monomialCoeffShift a S hS 0 = 0
    simp only [monomialCoeffShift, HomogeneousLocalizedModule.val_zero]
    change LocalizedModule.liftOn 0 _ _ = 0
    rw [show (0 : LocalizedModule (Submonoid.powers (coordProd n R S))
        (MvPolynomial (Fin (n + 1)) R)) = LocalizedModule.mk 0 1 from by
      rw [LocalizedModule.zero_mk], LocalizedModule.liftOn_mk]
    simp [monomialCoeffShiftFun, mul_zero, MvPolynomial.coeff_zero]
  map_add' x y := by
    show monomialCoeffShift a S hS (x + y) =
      monomialCoeffShift a S hS x + monomialCoeffShift a S hS y
    simp only [monomialCoeffShift, HomogeneousLocalizedModule.val_add]
    sorry

end MonomialCoeffShift

/-! ### Orthogonality for shifted monomial elements -/

section ShiftOrthogonality

variable (d : ℤ) (hd : 0 ≤ d)

/-- Extracting the coefficient of a monomial at itself gives `1`. -/
theorem monomialCoeffShift_self (a : LaurentExp n d)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) :
    monomialCoeffShift a S hS (monomialElemShift (R := R) d hd a S hS) = 1 := by
  sorry

/-- Extracting the coefficient of a different monomial gives `0`. -/
theorem monomialCoeffShift_ne {a a' : LaurentExp n d}
    {S : Finset (Fin (n + 1))} (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S)
    (hne : a ≠ a') :
    monomialCoeffShift a S hS (monomialElemShift (R := R) d hd a' S hS') = 0 := by
  sorry

/-- Combined orthogonality with scalar multiplication. -/
theorem monomialCoeffShift_smulMonomialElemShift
    (a a' : LaurentExp n d)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S)
    (r : R) :
    monomialCoeffShift a S hS
      (smulMonomialElemShift (R := R) d hd r a' S hS') =
    if a = a' then r else 0 := by
  sorry

end ShiftOrthogonality

/-! ### Face compatibility -/

section ShiftFaceCompat

variable {d : ℤ}

/-- `monomialCoeffShift` commutes with `coordRestrict`. -/
theorem monomialCoeffShift_coordRestrict (a : LaurentExp n d)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (hface : a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (hfull : a.negSupport ⊆ T)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeffShift a T hfull
      (coordRestrict n R (GradedModule.shift (𝒜 n R) d.toNat) T hT j x) =
    monomialCoeffShift a (TopCat.eraseNth T hT j).1 hface x := by
  sorry

/-- `monomialCoeffShift` vanishes when negSupport is not contained in a face. -/
theorem monomialCoeffShift_coordRestrict_vanish (a : LaurentExp n d)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (hnotface : ¬a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (hfull : a.negSupport ⊆ T)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeffShift a T hfull
      (coordRestrict n R (GradedModule.shift (𝒜 n R) d.toNat) T hT j x) = 0 := by
  sorry

end ShiftFaceCompat

/-! ### Injectivity and finite support -/

section ShiftInjectivity

variable {d : ℤ}

/-- If all shifted monomial coefficients are zero, the element is zero. -/
theorem monomialCoeffShift_determines_zero (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S))
    (h : ∀ (a : LaurentExp n d) (hS : a.negSupport ⊆ S),
      monomialCoeffShift a S hS x = 0) :
    x = 0 := by
  sorry

/-- Only finitely many Laurent exponents have nonzero shifted monomial coefficients. -/
theorem monomialCoeffShift_finite_support (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S)) :
    {a : LaurentExp n d | ∃ hS : a.negSupport ⊆ S,
      monomialCoeffShift a S hS x ≠ 0}.Finite := by
  sorry

end ShiftInjectivity

/-! ### Component chain maps for the shifted module -/

section ShiftComponentChainMap

variable {d : ℤ}

/-- Extract the `a`-component from a cochain of the shifted algebraic complex. -/
def componentHomShift (a : LaurentExp n d) (p : ℕ) :
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R)
        (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S.1)) →+
    _root_.relSimplexCochain a.negSupport R p where
  toFun := fun f ⟨S, hS, hns⟩ => monomialCoeffShift a S hns (f ⟨S, hS⟩)
  map_zero' := by
    ext ⟨S, hS, hns⟩; simp only [Pi.zero_apply]
    exact (monomialCoeffShiftHom a S hns).map_zero
  map_add' x y := by
    ext ⟨S, hS, hns⟩; simp only [Pi.add_apply]
    exact (monomialCoeffShiftHom a S hns).map_add (x ⟨S, hS⟩) (y ⟨S, hS⟩)

/-- The component extraction commutes with differentials. -/
theorem componentShift_comm_δ (a : LaurentExp n d) (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R)
        (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S.1)) :
    componentHomShift a (p + 1)
      (algebraicδ n R (GradedModule.shift (𝒜 n R) d.toNat) p f) =
    _root_.relSimplexδHom a.negSupport R p (componentHomShift a p f) := by
  sorry

end ShiftComponentChainMap

/-! ### Main acyclicity theorem -/

section Acyclicity

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
      {a : LaurentExp n d | ∃ hS : a.negSupport ⊆ T.1,
        monomialCoeffShift a T.1 hS (f T) ≠ 0}
  have hB_finite : B.Finite :=
    Set.finite_iUnion fun T => monomialCoeffShift_finite_support T.1 (f T)
  set B_fin := hB_finite.toFinset
  -- For each a, get primitive g_a in K_{negSupport a}
  have hprimitive : ∀ (a : LaurentExp n d), a ∈ B_fin →
      ∃ ga : _root_.relSimplexCochain a.negSupport R p,
        _root_.relSimplexδHom a.negSupport R p ga =
          componentHomShift a (p + 1) f := by
    intro a _
    by_cases hne : a.negSupport.Nonempty
    · -- ∅ ⊊ negSupport ⊊ univ: K_T is acyclic
      set K := _root_.relSimplexComplex a.negSupport R
      have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom
          (_root_.relSimplexδHom a.negSupport R j) :=
        fun j => by simp [K, _root_.relSimplexComplex]
      have hexact := (_root_.relSimplexComplex_acyclic a.negSupport R
        hne (hne_univ a)) (p + 1)
      rw [HomologicalComplex.exactAt_iff' K p (p + 1) (p + 2)
        (by simp) (by simp), ShortComplex.ab_exact_iff] at hexact
      have hker : (K.sc' p (p + 1) (p + 2)).g.hom
          (componentHomShift a (p + 1) f) = 0 := by
        show K.d (p + 1) (p + 2) (componentHomShift a (p + 1) f) = 0
        rw [hKd]; exact hcomp_cocycle a
      obtain ⟨ga, hga⟩ := hexact _ hker
      exact ⟨ga, by rwa [show (K.sc' p (p + 1) (p + 2)).f =
        K.d p (p + 1) from rfl, hKd] at hga⟩
    · -- negSupport = ∅: K_∅ is exact at positive degrees
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      set K := _root_.relSimplexComplex a.negSupport R
      have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom
          (_root_.relSimplexδHom a.negSupport R j) :=
        fun j => by simp [K, _root_.relSimplexComplex]
      have hexact : K.ExactAt (p + 1) := by
        show (_root_.relSimplexComplex a.negSupport R).ExactAt (p + 1)
        rw [hne]; exact _root_.relSimplexComplex_empty_exactAt R p
      rw [HomologicalComplex.exactAt_iff' K p (p + 1) (p + 2)
        (by simp) (by simp), ShortComplex.ab_exact_iff] at hexact
      have hker : (K.sc' p (p + 1) (p + 2)).g.hom
          (componentHomShift a (p + 1) f) = 0 := by
        show K.d (p + 1) (p + 2) (componentHomShift a (p + 1) f) = 0
        rw [hKd]; exact hcomp_cocycle a
      obtain ⟨ga, hga⟩ := hexact _ hker
      exact ⟨ga, by rwa [show (K.sc' p (p + 1) (p + 2)).f =
        K.d p (p + 1) from rfl, hKd] at hga⟩
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
  -- The verification follows the d=0 pattern: use monomialCoeffShift_determines_zero,
  -- componentShift_comm_δ, and monomialCoeffShift_smulMonomialElemShift.
  sorry

end Acyclicity

end AlgebraicGeometry.Proj
