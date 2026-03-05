/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.MonomialDecomposition
public import Mathlib.Algebra.Module.GradedModule.Shift

/-!
# Monomial coefficient extraction for graded module localizations

This file provides infrastructure for extracting monomial coefficients from elements of
`HomogeneousLocalizedModule.Away 𝒜 𝓜`, parametric in the graded module `𝓜`. This
generalizes the degree-0 coefficient extraction in `MonomialDecomposition.lean` to
arbitrary graded modules (including `GradedModule.shift 𝒜 d.toNat` and
`GradedModule.intShift 𝒜 d`).

The key definitions and results are:

* `monomialCoeff` — coefficient extraction, generic over `𝓜`
* `monomialCoeffHom` — `monomialCoeff` as an `AddMonoidHom`
* `monomialCoeff_coordRestrict` / `_vanish` — face compatibility (generic)
* `monomialCoeff_finite_support` — finiteness of nonzero coefficients (generic)
* `componentHom` / `component_comm_δ` — component extraction as a chain map (generic)
* `monomialElemShift` / `smulMonomialElemShift` — monomial elements for `shift` (d ≥ 0)
* `monomialCoeffShift_self` / `_ne` — orthogonality for `shift`
* `monomialCoeffShift_determines_zero` — injectivity for `shift`
* `monomialElemIntShift` / `smulMonomialElemIntShift` — monomial elements for `intShift`
* `monomialCoeffIntShift_self` / `_ne` — orthogonality for `intShift`
* `monomialCoeffIntShift_determines_zero` — injectivity for `intShift`

When `d = 0`, `GradedModule.shift 𝒜 0 = 𝒜` definitionally (since `shift` is an
`abbrev` and `Nat.add_zero` is definitional), so these specialize to the degree-0 case.

## References

* [Stacks Project, Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MvPolynomial CategoryTheory CategoryTheory.Limits Finset

namespace AlgebraicGeometry.Proj

universe u

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading


local instance : SetLike.GradedSMul (𝒜 n R) (𝒜 n R) :=
  SetLike.GradedMul.toGradedSMul _

/-! ### Polynomial coefficient shifting lemma -/

/-- Generalized version of `coeff_coordProdFinsupp_eq_of_pow_eq`: if
`(coordProd S)^m = (coordProd S)^N`, then extracting at index
`idx + coordProdFinsupp S m` from any polynomial `y` equals extracting at
`idx + coordProdFinsupp S N`. -/
theorem coeff_shift_coordProdFinsupp_eq_of_pow_eq (S : Finset (Fin (n + 1)))
    (idx : Fin (n + 1) →₀ ℕ) {m N : ℕ}
    (h : (coordProd n R S) ^ m = (coordProd n R S) ^ N)
    (y : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.coeff (idx + coordProdFinsupp S m) y =
    MvPolynomial.coeff (idx + coordProdFinsupp S N) y := by
  have h1 := coeff_coordProd_pow_mul (R := R) S N (idx + coordProdFinsupp S m) y
  have h2 := coeff_coordProd_pow_mul (R := R) S m (idx + coordProdFinsupp S N) y
  have hindex : coordProdFinsupp S N + (idx + coordProdFinsupp S m) =
      coordProdFinsupp S m + (idx + coordProdFinsupp S N) := by
    ext i; by_cases hi : i ∈ S
    · simp [coordProdFinsupp_apply_mem hi]; ring
    · simp [coordProdFinsupp_apply_notMem hi]
  rw [hindex, ← h] at h1
  exact h1.symm.trans h2

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

section MonomialCoeff

variable {d : ℤ} {𝓜 : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R)}
  [SetLike.GradedSMul (𝒜 n R) 𝓜]

/-- The raw coefficient extraction function on `M × S` pairs, where
`M = MvPolynomial` and `S = powers(coordProd)`. Used to define
`monomialCoeff` via `LocalizedModule.liftOn`. -/
def monomialCoeffShiftFun (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (ms : MvPolynomial (Fin (n + 1)) R ×
      ↥(Submonoid.powers (coordProd n R S))) :
    R :=
  MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S ms.2.2.choose)
    ((coordProd n R S) ^ (a.clearingPow S) * ms.1)

/-- Well-definedness of coefficient extraction for the `LocalizedModule` relation. -/
theorem monomialCoeffShiftFun_wd (a : LaurentExp n d)
    (S : Finset (Fin (n + 1)))
    (p q : MvPolynomial (Fin (n + 1)) R ×
      ↥(Submonoid.powers (coordProd n R S)))
    (hrel : p ≈ q) :
    monomialCoeffShiftFun a S p = monomialCoeffShiftFun a S q := by
  obtain ⟨u, hu⟩ := hrel
  simp only [Submonoid.smul_def, smul_eq_mul] at hu
  unfold monomialCoeffShiftFun
  set K := u.2.choose; set Ns := p.2.2.choose; set Nt := q.2.2.choose
  set cp := a.clearingPow S; set nf := a.numFinsupp S
  have h1 := coeff_coordProd_pow_mul (R := R) S (K + Nt)
    (nf + coordProdFinsupp S Ns) ((coordProd n R S) ^ cp * p.1)
  have h2 := coeff_coordProd_pow_mul (R := R) S (K + Ns)
    (nf + coordProdFinsupp S Nt) ((coordProd n R S) ^ cp * q.1)
  have hindex : coordProdFinsupp S (K + Nt) + (nf + coordProdFinsupp S Ns) =
      coordProdFinsupp S (K + Ns) + (nf + coordProdFinsupp S Nt) := by
    ext i; by_cases hi : i ∈ S
    · simp [coordProdFinsupp_apply_mem hi, LaurentExp.numFinsupp_apply]; ring
    · simp [coordProdFinsupp_apply_notMem hi]
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

/-- Generalized monomial coefficient extraction from a graded module localization.
Defined via `val` (injection into `LocalizedModule`) and `LocalizedModule.liftOn`.
Generic in the graded module `𝓜`. -/
def monomialCoeff (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S)) : R :=
  x.val.liftOn (monomialCoeffShiftFun a S) (monomialCoeffShiftFun_wd a S)

omit [SetLike.GradedSMul (𝒜 n R) 𝓜] in
/-- Explicit computation of `monomialCoeff` on an `Away.mk` element:
extracts the coefficient of `numFinsupp a S + coordProdFinsupp S deg` from the
product `coordProd^(clearingPow) * numerator`. -/
theorem monomialCoeff_Away_mk (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (deg : ℕ) (num : MvPolynomial (Fin (n + 1)) R)
    (hnum : num ∈ 𝓜 (deg • S.card)) :
    monomialCoeff a S (HomogeneousLocalizedModule.Away.mk (𝒜 n R)
        𝓜 (coordProd_mem_homogeneous n R S) deg num hnum) =
    MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S deg)
      ((coordProd n R S) ^ a.clearingPow S * num) := by
  simp only [monomialCoeff, HomogeneousLocalizedModule.Away.val_mk,
    LocalizedModule.liftOn_mk, monomialCoeffShiftFun]
  exact coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S (a.numFinsupp S)
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _) _

/-- `monomialCoeff` as an `AddMonoidHom`. -/
def monomialCoeffHom (a : LaurentExp n d) (S : Finset (Fin (n + 1))) :
    HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S) →+ R where
  toFun := monomialCoeff a S
  map_zero' := by
    show monomialCoeff a S 0 = 0
    simp only [monomialCoeff, HomogeneousLocalizedModule.val_zero]
    rw [show (0 : LocalizedModule (Submonoid.powers (coordProd n R S))
        (MvPolynomial (Fin (n + 1)) R)) = LocalizedModule.mk 0 1 from by
      rw [LocalizedModule.zero_mk], LocalizedModule.liftOn_mk]
    simp [monomialCoeffShiftFun, mul_zero, MvPolynomial.coeff_zero]
  map_add' x y := by
    show monomialCoeff a S (x + y) =
      monomialCoeff a S x + monomialCoeff a S y
    simp only [monomialCoeff, HomogeneousLocalizedModule.val_add]
    refine LocalizedModule.induction_on₂ (fun m1 m2 s1 s2 => ?_) x.val y.val
    rw [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk,
      LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk]
    simp only [monomialCoeffShiftFun, Prod.fst, Prod.snd]
    set nf := a.numFinsupp S
    set cp := (coordProd n R S) ^ a.clearingPow S
    set Ns := s1.2.choose; set Nt := s2.2.choose; set Nst := (s1 * s2).2.choose
    simp only [Submonoid.smul_def, smul_eq_mul]
    rw [mul_add, MvPolynomial.coeff_add]
    have hs_spec : (coordProd n R S) ^ Ns = ↑s1 := s1.2.choose_spec
    have ht_spec : (coordProd n R S) ^ Nt = ↑s2 := s2.2.choose_spec
    have hst_spec : (coordProd n R S) ^ Nst = ↑(s1 * s2) := (s1 * s2).2.choose_spec
    have hpow : (coordProd n R S) ^ Nst = (coordProd n R S) ^ (Ns + Nt) := by
      rw [hst_spec, Submonoid.coe_mul, ← hs_spec, ← ht_spec, ← pow_add]
    rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S nf hpow (cp * (↑s2 * m1)),
      coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S nf hpow (cp * (↑s1 * m2))]
    rw [show (↑s2 : MvPolynomial _ R) = (coordProd n R S) ^ Nt from ht_spec.symm,
      show (↑s1 : MvPolynomial _ R) = (coordProd n R S) ^ Ns from hs_spec.symm]
    have hindex : ∀ a' b : ℕ,
        nf + coordProdFinsupp S (a' + b) =
        coordProdFinsupp S a' + (nf + coordProdFinsupp S b) := by
      intro a' b; ext i; by_cases hi : i ∈ S
      · simp [coordProdFinsupp_apply_mem hi]; ring
      · simp [coordProdFinsupp_apply_notMem hi]
    have h1 : MvPolynomial.coeff (nf + coordProdFinsupp S (Ns + Nt))
        (cp * ((coordProd n R S) ^ Ns * m2)) =
      MvPolynomial.coeff (nf + coordProdFinsupp S Nt) (cp * m2) := by
      rw [hindex Ns Nt, show cp * ((coordProd n R S) ^ Ns * m2) =
          (coordProd n R S) ^ Ns * (cp * m2) from by ring]
      exact coeff_coordProd_pow_mul _ _ _ _
    have h2 : MvPolynomial.coeff (nf + coordProdFinsupp S (Ns + Nt))
        (cp * ((coordProd n R S) ^ Nt * m1)) =
      MvPolynomial.coeff (nf + coordProdFinsupp S Ns) (cp * m1) := by
      rw [show Ns + Nt = Nt + Ns from by omega, hindex Nt Ns,
        show cp * ((coordProd n R S) ^ Nt * m1) =
          (coordProd n R S) ^ Nt * (cp * m1) from by ring]
      exact coeff_coordProd_pow_mul _ _ _ _
    rw [h1, h2, add_comm]

end MonomialCoeff

/-! ### Orthogonality for shifted monomial elements -/

section ShiftOrthogonality

variable (d : ℤ) (hd : 0 ≤ d)

/-- Extracting the coefficient of a monomial at itself gives `1`. -/
theorem monomialCoeffShift_self (a : LaurentExp n d)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) :
    monomialCoeff a S (monomialElemShift (R := R) d hd a S hS) = 1 := by
  simp only [monomialCoeff, monomialElemShift,
    HomogeneousLocalizedModule.Away.val_mk,
    LocalizedModule.liftOn_mk, monomialCoeffShiftFun]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S (a.numFinsupp S)
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _),
    prod_coord_pow_eq_monomial, coordProd_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
  exact if_pos (add_comm _ _)

/-- Extracting the coefficient of a different monomial gives `0`. -/
theorem monomialCoeffShift_ne {a a' : LaurentExp n d}
    {S : Finset (Fin (n + 1))} (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S)
    (hne : a ≠ a') :
    monomialCoeff a S (monomialElemShift (R := R) d hd a' S hS') = 0 := by
  simp only [monomialCoeff, monomialElemShift,
    HomogeneousLocalizedModule.Away.val_mk,
    LocalizedModule.liftOn_mk, monomialCoeffShiftFun]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S (a.numFinsupp S)
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _),
    prod_coord_pow_eq_monomial, coordProd_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
  refine if_neg fun h => hne ?_
  refine Subtype.ext (funext fun i => ?_)
  have hi : (coordProdFinsupp S (a.clearingPow S)) i + a'.numExp S i =
      a.numExp S i + (coordProdFinsupp S (a'.clearingPow S)) i :=
    DFunLike.congr_fun h i
  by_cases hiS : i ∈ S
  · simp only [coordProdFinsupp_apply_mem hiS] at hi
    have hnn := a.clearingPow_nonneg S i hiS
    have hnn' := a'.clearingPow_nonneg S i hiS
    have h1 := congr_arg ((↑) : ℕ → ℤ) hi
    simp only [Nat.cast_add, LaurentExp.numExp, if_pos hiS] at h1
    rw [Int.toNat_of_nonneg hnn, Int.toNat_of_nonneg hnn'] at h1
    linarith
  · simp only [coordProdFinsupp_apply_notMem hiS, add_zero, zero_add] at hi
    have ha : 0 ≤ a.1 i := (a.not_mem_negSupport_iff i).mp (fun hm => hiS (hS hm))
    have ha' : 0 ≤ a'.1 i :=
      (a'.not_mem_negSupport_iff i).mp (fun hm => hiS (hS' hm))
    have h1 := congr_arg ((↑) : ℕ → ℤ) hi
    simp only [LaurentExp.numExp, if_neg hiS] at h1
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg ha'] at h1
    linarith

/-- Combined orthogonality with scalar multiplication. -/
theorem monomialCoeffShift_smulMonomialElemShift
    (a a' : LaurentExp n d)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S)
    (r : R) :
    monomialCoeff a S
      (smulMonomialElemShift (R := R) d hd r a' S hS') =
    if a = a' then r else 0 := by
  simp only [monomialCoeff, smulMonomialElemShift,
    HomogeneousLocalizedModule.Away.val_mk,
    LocalizedModule.liftOn_mk, monomialCoeffShiftFun]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S (a.numFinsupp S)
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _)]
  rw [show (coordProd n R S) ^ a.clearingPow S *
      (MvPolynomial.C r * ∏ i, coord n R i ^ a'.numExp S i) =
    MvPolynomial.C r * ((coordProd n R S) ^ a.clearingPow S *
      ∏ i, coord n R i ^ a'.numExp S i) from by ring,
    MvPolynomial.coeff_C_mul, prod_coord_pow_eq_monomial, coordProd_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
  by_cases h : a = a'
  · subst h
    rw [if_pos rfl]
    simp only [LaurentExp.numFinsupp]
    rw [if_pos (add_comm _ _), mul_one]
  · rw [if_neg h]
    rw [if_neg, mul_zero]
    intro heq
    exact h (by
      refine Subtype.ext (funext fun i => ?_)
      have hi : (coordProdFinsupp S (a.clearingPow S)) i + a'.numExp S i =
          a.numExp S i + (coordProdFinsupp S (a'.clearingPow S)) i :=
        DFunLike.congr_fun heq i
      by_cases hiS : i ∈ S
      · simp only [coordProdFinsupp_apply_mem hiS] at hi
        have hnn := a.clearingPow_nonneg S i hiS
        have hnn' := a'.clearingPow_nonneg S i hiS
        have h1 := congr_arg ((↑) : ℕ → ℤ) hi
        simp only [Nat.cast_add, LaurentExp.numExp, if_pos hiS] at h1
        rw [Int.toNat_of_nonneg hnn, Int.toNat_of_nonneg hnn'] at h1
        linarith
      · simp only [coordProdFinsupp_apply_notMem hiS, add_zero, zero_add] at hi
        have ha : 0 ≤ a.1 i := (a.not_mem_negSupport_iff i).mp (fun hm => hiS (hS hm))
        have ha' : 0 ≤ a'.1 i :=
          (a'.not_mem_negSupport_iff i).mp (fun hm => hiS (hS' hm))
        have h1 := congr_arg ((↑) : ℕ → ℤ) hi
        simp only [LaurentExp.numExp, if_neg hiS] at h1
        rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg ha'] at h1
        linarith)

end ShiftOrthogonality

/-! ### Face compatibility -/

section FaceCompat

variable {d : ℤ} {𝓜 : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R)}
  [SetLike.GradedSMul (𝒜 n R) 𝓜]

/-- `monomialCoeff` commutes with `coordRestrict`. -/
theorem monomialCoeff_coordRestrict (a : LaurentExp n d)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (hface : a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeff a T
      (coordRestrict n R 𝓜 T hT j x) =
    monomialCoeff a (TopCat.eraseNth T hT j).1 x := by
  revert hface x
  set j_elem := TopCat.nthElem T hT j
  set face := (TopCat.eraseNth T hT j).1
  intro hface x
  refine Quotient.inductionOn x fun q => ?_
  set N := q.den_mem.choose
  have hj_nn : 0 ≤ a.1 j_elem := by
    rw [← a.not_mem_negSupport_iff]
    exact fun hmem => absurd (hface hmem) (Finset.notMem_erase j_elem T)
  have hk_notmem : j_elem ∉ face := Finset.notMem_erase _ T
  have hT_eq : T = insert j_elem face :=
    (Finset.insert_erase (TopCat.nthElem_mem T hT j)).symm
  have hcp_eq : a.clearingPow face = a.clearingPow T :=
    a.clearingPow_erase (TopCat.nthElem_mem T hT j) hj_nn
  set cp := a.clearingPow T
  -- RHS: unfold to polynomial coefficient
  have hRHS : monomialCoeff a face ⟦q⟧ =
      MvPolynomial.coeff (a.numFinsupp face + coordProdFinsupp face N)
        ((coordProd n R face) ^ cp *
          (q.num : MvPolynomial (Fin (n + 1)) R)) := by
    simp only [monomialCoeff, HomogeneousLocalizedModule.val_mk,
      LocalizedModule.liftOn_mk, monomialCoeffShiftFun]
    rw [← hcp_eq]
  rw [hRHS]; clear hRHS
  -- LHS: unfold coordRestrict and monomialCoeff
  simp only [monomialCoeff, coordRestrict]
  rw [HomogeneousLocalizedModule.val_awayMap_mk]
  rw [LocalizedModule.liftOn_mk]
  simp only [monomialCoeffShiftFun, Prod.fst, Prod.snd, Submonoid.smul_def, smul_eq_mul]
  -- Step 1: Polynomial shifting identity
  have poly_shift :
      MvPolynomial.coeff
        (Finsupp.single j_elem (cp + N) + (a.numFinsupp face + coordProdFinsupp face N))
        ((coord n R j_elem) ^ (cp + N) *
          ((coordProd n R face) ^ cp *
            (q.num : MvPolynomial (Fin (n + 1)) R))) =
      MvPolynomial.coeff (a.numFinsupp face + coordProdFinsupp face N)
        ((coordProd n R face) ^ cp *
          (q.num : MvPolynomial (Fin (n + 1)) R)) := by
    rw [coord, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_monomial_mul, one_mul]
  -- Step 2: Index identity
  have hindex :
      a.numFinsupp T + coordProdFinsupp T N =
      Finsupp.single j_elem (cp + N) +
        (a.numFinsupp face + coordProdFinsupp face N) := by
    ext i; by_cases hij : i = j_elem
    · subst hij
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        LaurentExp.numFinsupp_apply]
      rw [coordProdFinsupp_apply_mem (hT_eq ▸ Finset.mem_insert_self _ _),
        coordProdFinsupp_apply_notMem hk_notmem, add_zero]
      have h_ne := a.numExp_erase_add (TopCat.nthElem_mem T hT j) hj_nn
      change a.numExp face j_elem + cp = a.numExp T j_elem at h_ne
      omega
    · simp only [Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_of_ne (Ne.symm hij), LaurentExp.numFinsupp_apply, zero_add]
      have hi_face_iff : i ∈ face ↔ i ∈ T := by
        constructor
        · exact fun h => (Finset.erase_subset _ _) h
        · intro hiT; exact Finset.mem_erase.mpr ⟨hij, hiT⟩
      by_cases hiT : i ∈ T
      · rw [coordProdFinsupp_apply_mem hiT,
          coordProdFinsupp_apply_mem (hi_face_iff.mpr hiT)]
        have := a.numExp_erase_of_ne (TopCat.nthElem_mem T hT j) hj_nn hij
        change a.numExp face i = a.numExp T i at this
        grind
      · rw [coordProdFinsupp_apply_notMem hiT,
          coordProdFinsupp_apply_notMem (fun h => hiT (hi_face_iff.mp h))]
        have : a.numExp face i = a.numExp T i := by
          simp only [LaurentExp.numExp, if_neg (fun h => hiT (hi_face_iff.mp h)),
            if_neg hiT]
        grind
  -- Step 3: Polynomial identity
  have hpoly :
      (coordProd n R T) ^ cp * (coord n R j_elem) ^ N =
      (coord n R j_elem) ^ (cp + N) * (coordProd n R face) ^ cp := by
    have h1 : coordProd n R T = coordProd n R face * coord n R j_elem :=
      coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j)
    rw [h1, mul_pow, mul_assoc, ← pow_add]; ring
  -- Combine
  trans MvPolynomial.coeff
    (Finsupp.single j_elem (cp + N) + (a.numFinsupp face + coordProdFinsupp face N))
    ((coord n R j_elem) ^ (cp + N) *
      ((coordProd n R face) ^ cp *
        (q.num : MvPolynomial (Fin (n + 1)) R)))
  · -- Normalize the choose index via coeff_shift_coordProdFinsupp_eq_of_pow_eq
    have hpoly_ext : (coordProd n R T) ^ cp * ((coord n R j_elem) ^ N *
        (q.num : MvPolynomial (Fin (n + 1)) R)) =
      (coord n R j_elem) ^ (cp + N) * ((coordProd n R face) ^ cp *
        (q.num : MvPolynomial (Fin (n + 1)) R)) := by
      rw [← mul_assoc, hpoly, mul_assoc]
    rw [hpoly_ext, ← hindex]
    apply coeff_shift_coordProdFinsupp_eq_of_pow_eq
    have hpow_eq : (coordProd n R T) ^ N =
        (q.den : MvPolynomial (Fin (n + 1)) R) *
          (coord n R j_elem) ^ N := by
      have h1 : coordProd n R T = coordProd n R face * coord n R j_elem :=
        coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j)
      have h2 : (coordProd n R face) ^ N =
          (q.den : MvPolynomial (Fin (n + 1)) R) := q.den_mem.choose_spec
      simp only [h1, mul_pow, h2]
    exact (Exists.choose_spec (p := fun m =>
      (coordProd n R T) ^ m = ↑(q.den : MvPolynomial (Fin (n + 1)) R) *
        (coord n R j_elem) ^ N) _).trans hpow_eq.symm
  · exact poly_shift

/-- `monomialCoeff` vanishes when negSupport is not contained in a face. -/
theorem monomialCoeff_coordRestrict_vanish (a : LaurentExp n d)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (hnotface : ¬a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (hfull : a.negSupport ⊆ T)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeff a T
      (coordRestrict n R 𝓜 T hT j x) = 0 := by
  refine Quotient.inductionOn x fun q => ?_
  set j_elem := TopCat.nthElem T hT j
  set N := q.den_mem.choose
  set cp := a.clearingPow T
  have hj_neg : a.1 j_elem < 0 := by
    by_contra h
    push_neg at h
    exact hnotface ((a.negSupport_subset_eraseNth_iff hT j hfull).mpr h)
  have hj_mem : j_elem ∈ T := TopCat.nthElem_mem T hT j
  -- Unfold LHS
  simp only [monomialCoeff, coordRestrict]
  rw [HomogeneousLocalizedModule.val_awayMap_mk]
  rw [LocalizedModule.liftOn_mk]
  simp only [monomialCoeffShiftFun, Prod.fst, Prod.snd, Submonoid.smul_def, smul_eq_mul]
  -- Normalize the choose index
  trans MvPolynomial.coeff
    (a.numFinsupp T + coordProdFinsupp T N)
    ((coordProd n R T) ^ cp * ((coord n R j_elem) ^ N *
      (q.num : MvPolynomial (Fin (n + 1)) R)))
  · apply coeff_shift_coordProdFinsupp_eq_of_pow_eq
    have hpow_eq : (coordProd n R T) ^ N =
        (q.den : MvPolynomial (Fin (n + 1)) R) *
          (coord n R j_elem) ^ N := by
      have h1 : coordProd n R T =
          coordProd n R (TopCat.eraseNth T hT j).1 * coord n R j_elem :=
        coordProd_eq_erase_mul n R T hj_mem
      have h2 : (coordProd n R (TopCat.eraseNth T hT j).1) ^ N =
          (q.den : MvPolynomial (Fin (n + 1)) R) := q.den_mem.choose_spec
      simp only [h1, mul_pow, h2]
    exact (Exists.choose_spec (p := fun m =>
      (coordProd n R T) ^ m = ↑(q.den : MvPolynomial (Fin (n + 1)) R) *
        (coord n R j_elem) ^ N) _).trans hpow_eq.symm
  · -- The coefficient vanishes: monomial exponent exceeds extraction index at j_elem
    have h1 : coordProd n R T =
        coordProd n R (TopCat.eraseNth T hT j).1 * coord n R j_elem :=
      coordProd_eq_erase_mul n R T hj_mem
    rw [h1, mul_pow]
    have hpow_rearrange :
        (coordProd n R (TopCat.eraseNth T hT j).1) ^ cp *
          (coord n R j_elem) ^ cp *
          ((coord n R j_elem) ^ N *
            (q.num : MvPolynomial (Fin (n + 1)) R)) =
        (coord n R j_elem) ^ (cp + N) *
          ((coordProd n R (TopCat.eraseNth T hT j).1) ^ cp *
            (q.num : MvPolynomial (Fin (n + 1)) R)) := by ring
    rw [hpow_rearrange, coord, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_monomial_mul']
    refine if_neg fun hle => ?_
    have := hle j_elem
    simp only [Finsupp.single_eq_same, Finsupp.coe_add, Pi.add_apply,
      LaurentExp.numFinsupp_apply, LaurentExp.numExp, if_pos hj_mem,
      coordProdFinsupp_apply_mem hj_mem] at this
    have hnn := a.clearingPow_nonneg T j_elem hj_mem
    omega

end FaceCompat

/-! ### Injectivity and finite support -/

section Injectivity

variable {d : ℤ}

/-- If all shifted monomial coefficients are zero, the element is zero. -/
theorem monomialCoeffShift_determines_zero (hd : 0 ≤ d) (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S))
    (h : ∀ (a : LaurentExp n d) (_ : a.negSupport ⊆ S),
      monomialCoeff a S x = 0) :
    x = 0 := by
  revert h; refine Quotient.inductionOn x fun q h => ?_
  suffices hnum : (q.num : MvPolynomial (Fin (n + 1)) R) = 0 by
    apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R S))
    simp only [HomogeneousLocalizedModule.val_zero]
    change LocalizedModule.mk (q.num : MvPolynomial (Fin (n + 1)) R)
      ⟨(q.den : MvPolynomial (Fin (n + 1)) R), q.den_mem⟩ = 0
    rw [hnum, LocalizedModule.zero_mk]
  by_contra hne
  have hsup : (↑q.num : MvPolynomial (Fin (n + 1)) R).support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, ne_eq, MvPolynomial.support_eq_empty]
  obtain ⟨m, hm⟩ := hsup
  set N := q.den_mem.choose
  have hN_spec : (coordProd n R S) ^ N = (↑q.den : MvPolynomial _ R) :=
    q.den_mem.choose_spec
  -- q.deg = N * S.card
  have hdeg : q.deg = N * S.card := by
    by_cases hden : (↑q.den : MvPolynomial (Fin (n + 1)) R) = 0
    · exfalso; apply hne
      suffices Subsingleton R from Subsingleton.elim _ _
      rw [← not_nontrivial_iff_subsingleton]; intro
      exact absurd hden (by
        rw [← hN_spec, coordProd_pow_eq_monomial]
        exact (MvPolynomial.monomial_eq_zero.not.mpr one_ne_zero))
    · have hsup' : (↑q.den : MvPolynomial (Fin (n + 1)) R).support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro heq; exact hden (MvPolynomial.support_eq_empty.mp heq)
      obtain ⟨m', hm'⟩ := hsup'
      have hden_hom : (↑q.den : MvPolynomial (Fin (n + 1)) R).IsHomogeneous q.deg :=
        q.den.2
      have hcoord_hom : ((coordProd n R S) ^ N : MvPolynomial _ R).IsHomogeneous
          (N * S.card) := by rw [mul_comm]; exact (coordProd_mem_homogeneous n R S).pow N
      have h1 := hden_hom (Finsupp.mem_support_iff.mp hm')
      have h2 := (hN_spec ▸ hcoord_hom) (Finsupp.mem_support_iff.mp hm')
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at h1 h2
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1 h2; omega
  -- ∑ m_i = N * S.card + d.toNat (numerator is homogeneous of degree q.deg + d.toNat)
  have hm_deg : (∑ i, m i : ℕ) = N * S.card + d.toNat := by
    have hnum_hom : (↑q.num : MvPolynomial (Fin (n + 1)) R).IsHomogeneous
        (q.deg + d.toNat) := q.num.2
    have := hnum_hom (Finsupp.mem_support_iff.mp hm)
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), hdeg] at this
  -- Construct the Laurent exponent from m and N
  have hm_intsum : (∑ i, (m i : ℤ) : ℤ) = (↑N : ℤ) * ↑S.card + ↑d.toNat := by
    have h' := congr_arg (Nat.cast (R := ℤ)) hm_deg; push_cast at h'; exact h'
  set a : LaurentExp n d :=
    ⟨fun i => if i ∈ S then (↑(m i) : ℤ) - ↑N else ↑(m i), by
      simp_rw [show ∀ i, (if i ∈ S then (↑(m i) : ℤ) - ↑N else ↑(m i)) =
        ↑(m i) + if i ∈ S then -(↑N : ℤ) else 0 from fun i => by split_ifs <;> omega]
      rw [Finset.sum_add_distrib]
      have : ∑ i : Fin (n + 1), (if i ∈ S then -(↑N : ℤ) else 0) =
          -(↑N : ℤ) * ↑S.card := by
        simp_rw [show ∀ i : Fin (n + 1), (if i ∈ S then -(↑N : ℤ) else 0) =
          -(↑N : ℤ) * if i ∈ S then 1 else 0 from fun i => by split_ifs <;> omega]
        rw [← Finset.mul_sum]
        simp [Finset.sum_boole, Nat.card_eq_fintype_card]
      rw [Int.toNat_of_nonneg hd] at hm_intsum
      linarith [hm_intsum]⟩ with ha_def
  -- negSupport a ⊆ S
  have hns : a.negSupport ⊆ S := by
    intro i hi; rw [LaurentExp.mem_negSupport_iff] at hi
    by_contra hiS; simp [ha_def, hiS] at hi; omega
  -- Index identity
  have hindex : a.numFinsupp S + coordProdFinsupp S N =
      coordProdFinsupp S (a.clearingPow S) + m := by
    ext i; by_cases hiS : i ∈ S
    · simp only [Finsupp.coe_add, Pi.add_apply, LaurentExp.numFinsupp_apply,
        LaurentExp.numExp, if_pos hiS, coordProdFinsupp_apply_mem hiS]
      have hnn := a.clearingPow_nonneg S i hiS
      have : a.val i = (↑(m i) : ℤ) - ↑N := by simp [ha_def, hiS]
      rw [this] at hnn ⊢; omega
    · simp only [Finsupp.coe_add, Pi.add_apply, LaurentExp.numFinsupp_apply,
        LaurentExp.numExp, if_neg hiS, coordProdFinsupp_apply_notMem hiS]
      have : a.val i = ↑(m i) := by simp [ha_def, hiS]
      rw [this, Int.toNat_natCast]; omega
  -- Coefficient computation
  have hcoeff : monomialCoeff a S ⟦q⟧ =
      MvPolynomial.coeff m (↑q.num : MvPolynomial _ R) := by
    show (HomogeneousLocalizedModule.mk q).val.liftOn
      (monomialCoeffShiftFun a S) (monomialCoeffShiftFun_wd a S) = _
    rw [HomogeneousLocalizedModule.val_mk, LocalizedModule.liftOn_mk,
      show monomialCoeffShiftFun a S ((q.num : MvPolynomial _ R),
        ⟨(q.den : MvPolynomial _ R), q.den_mem⟩) =
        MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S N)
        ((coordProd n R S) ^ a.clearingPow S * (q.num : MvPolynomial _ R)) from rfl,
      hindex]
    exact coeff_coordProd_pow_mul S _ m _
  exact absurd (hcoeff.symm.trans (h a hns)) (Finsupp.mem_support_iff.mp hm)

end Injectivity

/-! ### Finite support -/

section FiniteSupport

variable {d : ℤ} {𝓜 : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R)}
  [SetLike.GradedSMul (𝒜 n R) 𝓜]

omit [SetLike.GradedSMul (𝒜 n R) 𝓜] in
/-- Only finitely many Laurent exponents have nonzero monomial coefficients. -/
theorem monomialCoeff_finite_support (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S)) :
    {a : LaurentExp n d | ∃ _ : a.negSupport ⊆ S,
      monomialCoeff a S x ≠ 0}.Finite := by
  revert x; refine Quotient.ind fun q => ?_
  set N := q.den_mem.choose
  set num := (q.num : MvPolynomial (Fin (n + 1)) R)
  let φ : LaurentExp n d → Fin (n + 1) →₀ ℕ := fun a =>
    a.numFinsupp S + coordProdFinsupp S N - coordProdFinsupp S (a.clearingPow S)
  have hφ_spec : ∀ a (_ : a.negSupport ⊆ S),
      monomialCoeff a S ⟦q⟧ ≠ 0 →
      coordProdFinsupp S (a.clearingPow S) ≤
        a.numFinsupp S + coordProdFinsupp S N ∧
      monomialCoeff a S ⟦q⟧ = MvPolynomial.coeff (φ a) num := by
    intro a _hns hne
    have hraw : monomialCoeff a S ⟦q⟧ =
        MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S N)
          ((coordProd n R S) ^ a.clearingPow S * num) := by
      show (HomogeneousLocalizedModule.mk q).val.liftOn
        (monomialCoeffShiftFun a S) (monomialCoeffShiftFun_wd a S) = _
      rw [HomogeneousLocalizedModule.val_mk, LocalizedModule.liftOn_mk]
      rfl
    rw [coordProd_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at hraw
    split_ifs at hraw with h
    · exact ⟨h, by rw [hraw, one_mul]⟩
    · exact (hne hraw).elim
  -- φ maps nonzero set into support(num)
  have hφ_mem : ∀ a ∈ {a | ∃ _ : a.negSupport ⊆ S,
      monomialCoeff a S ⟦q⟧ ≠ 0}, φ a ∈ num.support := by
    intro a ⟨hns, hne⟩
    rw [MvPolynomial.mem_support_iff]
    rwa [← (hφ_spec a hns hne).2]
  -- φ is injective on nonzero set
  have hφ_inj : Set.InjOn φ
      {a | ∃ _ : a.negSupport ⊆ S, monomialCoeff a S ⟦q⟧ ≠ 0} := by
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
  exact Set.Finite.of_finite_image
    ((num.support.finite_toSet).subset (Set.image_subset_iff.mpr
      (fun a ha => Finset.mem_coe.mpr (hφ_mem a ha))))
    hφ_inj

end FiniteSupport

/-! ### Component chain maps -/

section ComponentChainMap

variable {d : ℤ} {𝓜 : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R)}
  [SetLike.GradedSMul (𝒜 n R) 𝓜]

/-- Extract the `a`-component from a cochain of the algebraic complex. -/
def componentHom (a : LaurentExp n d) (p : ℕ) :
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S.1)) →+
    _root_.relSimplexCochain a.negSupport R p where
  toFun := fun f ⟨S, hS, _hns⟩ => monomialCoeff a S (f ⟨S, hS⟩)
  map_zero' := by
    ext ⟨S, hS, _hns⟩; simp only [Pi.zero_apply]
    exact (monomialCoeffHom a S).map_zero
  map_add' x y := by
    ext ⟨S, hS, _hns⟩; simp only [Pi.add_apply]
    exact (monomialCoeffHom a S).map_add (x ⟨S, hS⟩) (y ⟨S, hS⟩)

/-- The component extraction commutes with differentials. -/
theorem component_comm_δ (a : LaurentExp n d) (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) 𝓜 (coordProd n R S.1)) :
    componentHom a (p + 1)
      (algebraicδ n R 𝓜 p f) =
    _root_.relSimplexδHom a.negSupport R p (componentHom a p f) := by
  ext ⟨T, hT, hfull⟩
  simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    algebraicδ, _root_.relSimplexδHom]
  rw [_root_.relSimplexδ_apply]
  change (monomialCoeffHom a T) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  simp only [monomialCoeffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hface
  · congr 1; exact monomialCoeff_coordRestrict a hT j hface _
  · rw [monomialCoeff_coordRestrict_vanish a hT j hface hfull _, smul_zero]

end ComponentChainMap

/-! ### Bridge: degree-0 coefficient agrees with zero-exponent extraction -/

section ZeroBridge

/-- When `a = 0` (degree 0), `monomialCoeff` agrees with `zeroExpCoeffMod`.
This bridges the general shifted coefficient extraction with the degree-0 extraction
used by `extractionHom`. -/
theorem monomialCoeff_zero_eq (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S)) :
    monomialCoeff (0 : LaurentExp n 0) S x = zeroExpCoeffMod (R := R) S x := by
  refine Quotient.inductionOn x fun q => ?_
  -- LHS: unfold via val_mk, liftOn_mk
  show (HomogeneousLocalizedModule.mk q).val.liftOn
    (monomialCoeffShiftFun (0 : LaurentExp n 0) S)
    (monomialCoeffShiftFun_wd (0 : LaurentExp n 0) S) = _
  rw [HomogeneousLocalizedModule.val_mk, LocalizedModule.liftOn_mk]
  -- monomialCoeffShiftFun at a=0: clearingPow=0, numFinsupp=0
  simp only [monomialCoeffShiftFun]
  have h1 : (0 : LaurentExp n 0).clearingPow S = 0 := by
    unfold LaurentExp.clearingPow
    simp only [show ∀ i, (0 : LaurentExp n 0).1 i = 0 from fun _ => rfl, neg_zero,
      Int.toNat_zero]
    exact (Finset.sup_eq_bot_iff _ _).mpr (fun _ _ => rfl)
  have h2 : (0 : LaurentExp n 0).numFinsupp S = 0 := by
    ext i; simp [LaurentExp.numFinsupp_apply, LaurentExp.numExp, h1,
      show (0 : LaurentExp n 0).1 i = 0 from rfl]
  rw [h1, h2, zero_add, pow_zero, one_mul]
  -- RHS: zeroExpCoeffMod S ⟦q⟧ = coeff (coordProdFinsupp S N) q.num, definitionally
  rfl

/-- `componentHom` at `a = 0` agrees with `extractionHom`. -/
theorem componentHom_zero_apply (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1))
    {S : Finset (Fin (n + 1))} (hS : S.card = p + 1)
    (hns : (0 : LaurentExp n 0).negSupport ⊆ S) :
    componentHom (0 : LaurentExp n 0) p f ⟨S, hS, hns⟩ =
    extractionHom p f ⟨S, hS, Finset.empty_subset S⟩ := by
  simp only [componentHom, extractionHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact monomialCoeff_zero_eq S (f ⟨S, hS⟩)

end ZeroBridge

/-! ### Integer-shifted module infrastructure -/

section IntShift

variable {d : ℤ}

/-- The `GradedSMul` instance for `intShift (𝒜 n R) d`. When `(j : ℤ) + d < 0`,
the target component is `⊥` and elements are zero; otherwise it reduces to
the standard graded multiplication. -/
instance intShiftGradedSMul :
    SetLike.GradedSMul (𝒜 n R) (GradedModule.intShift (𝒜 n R) d) where
  smul_mem {i j a b} ha hb := by
    show a • b ∈ GradedModule.intShift (𝒜 n R) d (i +ᵥ j)
    rw [show (i +ᵥ j : ℕ) = i + j from vadd_eq_add i j]
    simp only [GradedModule.intShift] at hb ⊢
    split_ifs at hb with hj
    · -- (j:ℤ)+d ≥ 0: standard graded multiplication
      have hij : 0 ≤ (↑(i + j) : ℤ) + d := by push_cast; linarith
      rw [if_pos hij]
      have hkey : i + ((j : ℤ) + d).toNat = ((↑(i + j) : ℤ) + d).toNat := by omega
      rw [← hkey]
      exact SetLike.GradedMul.mul_mem ha hb
    · -- (j:ℤ)+d < 0: b ∈ ⊥, so b = 0 and a • b = 0
      have hb0 : b = 0 := by rwa [Submodule.mem_bot] at hb
      rw [hb0, smul_zero]
      split_ifs
      · exact zero_mem _
      · exact (Submodule.mem_bot (R := MvPolynomial (Fin (n + 1)) R)).2 rfl

/-- The monomial element in the `intShift`-module localization. Unlike `monomialElemShift`,
this works for all `d ∈ ℤ` (not just `d ≥ 0`), using `numExp_sum_int` for degree
compatibility. -/
def monomialElemIntShift (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.intShift (𝒜 n R) d)
      (coordProd n R S) :=
  HomogeneousLocalizedModule.Away.mk (𝒜 n R) (GradedModule.intShift (𝒜 n R) d)
    (coordProd_mem_homogeneous n R S)
    (a.clearingPow S)
    (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i)
    (by
      show (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i) ∈
        (GradedModule.intShift (𝒜 n R) d) (a.clearingPow S * S.card)
      rw [GradedModule.intShift_apply_of_nonneg _ _ _
        (a.clearingPow_mul_card_add_nonneg S hS)]
      have h := SetLike.prod_pow_mem_graded (F := Finset.univ) (𝒜 n R)
        (fun _ : Fin (n + 1) => (1 : ℕ)) (coord n R) (fun i => a.numExp S i)
        (fun i _ => coord_mem_homogeneousSubmodule n R i)
      simp only [smul_eq_mul, mul_one] at h
      rwa [a.numExp_sum_int S hS] at h)

/-- Scalar multiplication of `r : R` with an `intShift` monomial element. -/
def smulMonomialElemIntShift (r : R) (a : LaurentExp n d)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.intShift (𝒜 n R) d)
      (coordProd n R S) :=
  HomogeneousLocalizedModule.Away.mk (𝒜 n R) (GradedModule.intShift (𝒜 n R) d)
    (coordProd_mem_homogeneous n R S)
    (a.clearingPow S)
    (MvPolynomial.C r * ∏ i : Fin (n + 1), coord n R i ^ a.numExp S i)
    (by
      show MvPolynomial.C r * (∏ i, coord n R i ^ a.numExp S i) ∈
        (GradedModule.intShift (𝒜 n R) d) (a.clearingPow S * S.card)
      rw [GradedModule.intShift_apply_of_nonneg _ _ _
        (a.clearingPow_mul_card_add_nonneg S hS)]
      have h_prod := SetLike.prod_pow_mem_graded (F := Finset.univ) (𝒜 n R)
        (fun _ : Fin (n + 1) => (1 : ℕ)) (coord n R) (fun i => a.numExp S i)
        (fun i _ => coord_mem_homogeneousSubmodule n R i)
      simp only [smul_eq_mul, mul_one] at h_prod
      rw [a.numExp_sum_int S hS] at h_prod
      have hC : MvPolynomial.C r ∈ 𝒜 n R 0 := MvPolynomial.isHomogeneous_C _ r
      have := SetLike.mul_mem_graded hC h_prod
      rwa [zero_add] at this)

/-- Orthogonality: `monomialCoeff` extracts `1` from the matching monomial. -/
theorem monomialCoeffIntShift_self (a : LaurentExp n d)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) :
    monomialCoeff a S (monomialElemIntShift (R := R) a S hS) = 1 := by
  simp only [monomialCoeff, monomialElemIntShift,
    HomogeneousLocalizedModule.Away.val_mk, LocalizedModule.liftOn_mk,
    monomialCoeffShiftFun]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S (a.numFinsupp S)
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _),
    prod_coord_pow_eq_monomial, coordProd_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
  exact if_pos (add_comm _ _)

/-- Orthogonality: `monomialCoeff` gives `0` on a different monomial. -/
theorem monomialCoeffIntShift_ne (a a' : LaurentExp n d) (ha : a ≠ a')
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S)
    (hS' : a'.negSupport ⊆ S) :
    monomialCoeff a S (monomialElemIntShift (R := R) a' S hS') = 0 := by
  simp only [monomialCoeff, monomialElemIntShift,
    HomogeneousLocalizedModule.Away.val_mk, LocalizedModule.liftOn_mk,
    monomialCoeffShiftFun]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S (a.numFinsupp S)
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _),
    prod_coord_pow_eq_monomial, coordProd_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
  refine if_neg fun h => ha ?_
  refine Subtype.ext (funext fun i => ?_)
  have hi : (coordProdFinsupp S (a.clearingPow S)) i + a'.numExp S i =
      a.numExp S i + (coordProdFinsupp S (a'.clearingPow S)) i :=
    DFunLike.congr_fun h i
  by_cases hiS : i ∈ S
  · simp only [coordProdFinsupp_apply_mem hiS] at hi
    have hnn := a.clearingPow_nonneg S i hiS
    have hnn' := a'.clearingPow_nonneg S i hiS
    have h1 := congr_arg ((↑) : ℕ → ℤ) hi
    simp only [Nat.cast_add, LaurentExp.numExp, if_pos hiS] at h1
    rw [Int.toNat_of_nonneg hnn, Int.toNat_of_nonneg hnn'] at h1
    linarith
  · simp only [coordProdFinsupp_apply_notMem hiS, add_zero, zero_add] at hi
    have hpa : 0 ≤ a.1 i := (a.not_mem_negSupport_iff i).mp (fun hm => hiS (hS hm))
    have hpa' : 0 ≤ a'.1 i :=
      (a'.not_mem_negSupport_iff i).mp (fun hm => hiS (hS' hm))
    have h1 := congr_arg ((↑) : ℕ → ℤ) hi
    simp only [LaurentExp.numExp, if_neg hiS] at h1
    rw [Int.toNat_of_nonneg hpa, Int.toNat_of_nonneg hpa'] at h1
    linarith

/-- Combined orthogonality-linearity for `intShift`. -/
theorem monomialCoeffIntShift_smulMonomialElemIntShift
    (a a' : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S) (r : R) :
    monomialCoeff a' S
      (smulMonomialElemIntShift (R := R) r a S hS) =
    if a' = a then r else 0 := by
  simp only [monomialCoeff, smulMonomialElemIntShift,
    HomogeneousLocalizedModule.Away.val_mk,
    LocalizedModule.liftOn_mk, monomialCoeffShiftFun]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S (a'.numFinsupp S)
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _)]
  rw [show (coordProd n R S) ^ a'.clearingPow S *
      (MvPolynomial.C r * ∏ i, coord n R i ^ a.numExp S i) =
    MvPolynomial.C r * ((coordProd n R S) ^ a'.clearingPow S *
      ∏ i, coord n R i ^ a.numExp S i) from by ring,
    MvPolynomial.coeff_C_mul, prod_coord_pow_eq_monomial, coordProd_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
  by_cases h : a' = a
  · subst h
    rw [if_pos rfl]
    simp only [LaurentExp.numFinsupp]
    rw [if_pos (add_comm _ _), mul_one]
  · rw [if_neg h]
    rw [if_neg, mul_zero]
    intro heq
    exact h (by
      refine Subtype.ext (funext fun i => ?_)
      have hi : (coordProdFinsupp S (a'.clearingPow S)) i + a.numExp S i =
          a'.numExp S i + (coordProdFinsupp S (a.clearingPow S)) i :=
        DFunLike.congr_fun heq i
      by_cases hiS : i ∈ S
      · simp only [coordProdFinsupp_apply_mem hiS] at hi
        have hnn := a'.clearingPow_nonneg S i hiS
        have hnn' := a.clearingPow_nonneg S i hiS
        have h1 := congr_arg ((↑) : ℕ → ℤ) hi
        simp only [Nat.cast_add, LaurentExp.numExp, if_pos hiS] at h1
        rw [Int.toNat_of_nonneg hnn, Int.toNat_of_nonneg hnn'] at h1
        linarith
      · simp only [coordProdFinsupp_apply_notMem hiS, add_zero, zero_add] at hi
        have hpa' : 0 ≤ a'.1 i :=
          (a'.not_mem_negSupport_iff i).mp (fun hm => hiS (hS' hm))
        have hpa : 0 ≤ a.1 i :=
          (a.not_mem_negSupport_iff i).mp (fun hm => hiS (hS hm))
        have h1 := congr_arg ((↑) : ℕ → ℤ) hi
        simp only [LaurentExp.numExp, if_neg hiS] at h1
        rw [Int.toNat_of_nonneg hpa', Int.toNat_of_nonneg hpa] at h1
        linarith)

/-- If all `intShift` monomial coefficients are zero, the element is zero. -/
theorem monomialCoeffIntShift_determines_zero (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.intShift (𝒜 n R) d) (coordProd n R S))
    (h : ∀ (a : LaurentExp n d) (_ : a.negSupport ⊆ S),
      monomialCoeff a S x = 0) :
    x = 0 := by
  revert h; refine Quotient.inductionOn x fun q h => ?_
  suffices hnum : (q.num : MvPolynomial (Fin (n + 1)) R) = 0 by
    apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R S))
    simp only [HomogeneousLocalizedModule.val_zero]
    change LocalizedModule.mk (q.num : MvPolynomial (Fin (n + 1)) R)
      ⟨(q.den : MvPolynomial (Fin (n + 1)) R), q.den_mem⟩ = 0
    rw [hnum, LocalizedModule.zero_mk]
  by_contra hne
  have hsup : (↑q.num : MvPolynomial (Fin (n + 1)) R).support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, ne_eq, MvPolynomial.support_eq_empty]
  obtain ⟨m, hm⟩ := hsup
  set N := q.den_mem.choose
  have hN_spec : (coordProd n R S) ^ N = (↑q.den : MvPolynomial _ R) :=
    q.den_mem.choose_spec
  -- q.deg = N * S.card
  have hdeg : q.deg = N * S.card := by
    by_cases hden : (↑q.den : MvPolynomial (Fin (n + 1)) R) = 0
    · exfalso; apply hne
      suffices Subsingleton R from Subsingleton.elim _ _
      rw [← not_nontrivial_iff_subsingleton]; intro
      exact absurd hden (by
        rw [← hN_spec, coordProd_pow_eq_monomial]
        exact (MvPolynomial.monomial_eq_zero.not.mpr one_ne_zero))
    · have hsup' : (↑q.den : MvPolynomial (Fin (n + 1)) R).support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro heq; exact hden (MvPolynomial.support_eq_empty.mp heq)
      obtain ⟨m', hm'⟩ := hsup'
      have hden_hom : (↑q.den : MvPolynomial (Fin (n + 1)) R).IsHomogeneous q.deg :=
        q.den.2
      have hcoord_hom : ((coordProd n R S) ^ N : MvPolynomial _ R).IsHomogeneous
          (N * S.card) := by rw [mul_comm]; exact (coordProd_mem_homogeneous n R S).pow N
      have h1 := hden_hom (Finsupp.mem_support_iff.mp hm')
      have h2 := (hN_spec ▸ hcoord_hom) (Finsupp.mem_support_iff.mp hm')
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at h1 h2
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1 h2; omega
  -- (q.deg : ℤ) + d ≥ 0 (otherwise q.num ∈ ⊥, contradicting hne)
  have hmem : (q.num : MvPolynomial _ R) ∈
      (GradedModule.intShift (𝒜 n R) d) q.deg := q.num.2
  have hnn : 0 ≤ (q.deg : ℤ) + d := by
    by_contra hlt; push_neg at hlt
    have := hmem; simp only [GradedModule.intShift, if_neg (not_le.mpr hlt)] at this
    exact hne (by rwa [Submodule.mem_bot] at this)
  -- ∑ m_i = ((N * S.card : ℤ) + d).toNat
  have hm_deg : (∑ i, m i : ℕ) = ((↑(N * S.card) : ℤ) + d).toNat := by
    have hnum_hom : (↑q.num : MvPolynomial (Fin (n + 1)) R).IsHomogeneous
        (((q.deg : ℤ) + d).toNat) := by
      have := hmem; simp only [GradedModule.intShift, if_pos hnn] at this; exact this
    have := hnum_hom (Finsupp.mem_support_iff.mp hm)
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), hdeg] at this
  -- Construct the Laurent exponent from m and N
  have hm_intsum : (∑ i, (m i : ℤ) : ℤ) = (↑N : ℤ) * ↑S.card + d := by
    have h' := congr_arg (Nat.cast (R := ℤ)) hm_deg; push_cast at h'
    rwa [Int.toNat_of_nonneg (by exact_mod_cast hdeg ▸ hnn)] at h'
  set a : LaurentExp n d :=
    ⟨fun i => if i ∈ S then (↑(m i) : ℤ) - ↑N else ↑(m i), by
      simp_rw [show ∀ i, (if i ∈ S then (↑(m i) : ℤ) - ↑N else ↑(m i)) =
        ↑(m i) + if i ∈ S then -(↑N : ℤ) else 0 from fun i => by split_ifs <;> omega]
      rw [Finset.sum_add_distrib]
      have : ∑ i : Fin (n + 1), (if i ∈ S then -(↑N : ℤ) else 0) =
          -(↑N : ℤ) * ↑S.card := by
        simp_rw [show ∀ i : Fin (n + 1), (if i ∈ S then -(↑N : ℤ) else 0) =
          -(↑N : ℤ) * if i ∈ S then 1 else 0 from fun i => by split_ifs <;> omega]
        rw [← Finset.mul_sum]
        simp [Finset.sum_boole, Nat.card_eq_fintype_card]
      linarith [hm_intsum]⟩ with ha_def
  -- negSupport a ⊆ S
  have hns : a.negSupport ⊆ S := by
    intro i hi; rw [LaurentExp.mem_negSupport_iff] at hi
    by_contra hiS; simp [ha_def, hiS] at hi; omega
  -- Index identity
  have hindex : a.numFinsupp S + coordProdFinsupp S N =
      coordProdFinsupp S (a.clearingPow S) + m := by
    ext i; by_cases hiS : i ∈ S
    · simp only [Finsupp.coe_add, Pi.add_apply, LaurentExp.numFinsupp_apply,
        LaurentExp.numExp, if_pos hiS, coordProdFinsupp_apply_mem hiS]
      have hcp := a.clearingPow_nonneg S i hiS
      have : a.val i = (↑(m i) : ℤ) - ↑N := by simp [ha_def, hiS]
      rw [this] at hcp ⊢; omega
    · simp only [Finsupp.coe_add, Pi.add_apply, LaurentExp.numFinsupp_apply,
        LaurentExp.numExp, if_neg hiS, coordProdFinsupp_apply_notMem hiS]
      have : a.val i = ↑(m i) := by simp [ha_def, hiS]
      rw [this, Int.toNat_natCast]; omega
  -- Coefficient computation
  have hcoeff : monomialCoeff a S ⟦q⟧ =
      MvPolynomial.coeff m (↑q.num : MvPolynomial _ R) := by
    show (HomogeneousLocalizedModule.mk q).val.liftOn
      (monomialCoeffShiftFun a S) (monomialCoeffShiftFun_wd a S) = _
    rw [HomogeneousLocalizedModule.val_mk, LocalizedModule.liftOn_mk,
      show monomialCoeffShiftFun a S ((q.num : MvPolynomial _ R),
        ⟨(q.den : MvPolynomial _ R), q.den_mem⟩) =
        MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S N)
        ((coordProd n R S) ^ a.clearingPow S * (q.num : MvPolynomial _ R)) from rfl,
      hindex]
    exact coeff_coordProd_pow_mul S _ m _
  exact absurd (hcoeff.symm.trans (h a hns)) (Finsupp.mem_support_iff.mp hm)

end IntShift

end AlgebraicGeometry.Proj
