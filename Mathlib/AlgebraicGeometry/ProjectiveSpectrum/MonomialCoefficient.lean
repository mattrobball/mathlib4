/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.MonomialDecomposition
import Mathlib.Algebra.Module.GradedModule.Shift

/-!
# Monomial coefficient extraction for degree-d module localizations

This file provides the infrastructure for extracting monomial coefficients from
elements of the degree-shifted module localization `HomogeneousLocalizedModule.Away 𝒜
(GradedModule.shift 𝒜 d.toNat)`. This generalizes the degree-0 coefficient extraction
in `MonomialDecomposition.lean` to arbitrary degree `d ∈ ℤ`.

The key definitions and results are:

* `monomialElemShift` — the monomial element in the shifted module localization
* `smulMonomialElemShift` — scalar multiplication `r · monomialElem a`
* `monomialCoeffShift` — coefficient extraction from the shifted module localization
* `monomialCoeffShiftHom` — `monomialCoeffShift` as an `AddMonoidHom`
* `monomialCoeffShift_self` / `monomialCoeffShift_ne` — orthogonality
* `monomialCoeffShift_coordRestrict` / `_vanish` — face compatibility
* `monomialCoeffShift_determines_zero` — injectivity (for `d ≥ 0`)
* `monomialCoeffShift_finite_support` — finiteness of nonzero coefficients
* `componentHomShift` — component extraction as a chain map
* `componentShift_comm_δ` — commutativity with differentials

When `d = 0`, `GradedModule.shift 𝒜 0 = 𝒜` definitionally (since `shift` is an
`abbrev` and `Nat.add_zero` is definitional), so these specialize to the degree-0 case.

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
private theorem monomialCoeffShiftFun_wd (a : LaurentExp n d)
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

/-- Generalized monomial coefficient extraction from the shifted module localization.
Defined via `val` (injection into `LocalizedModule`) and `LocalizedModule.liftOn`. -/
def monomialCoeffShift (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R S)) : R :=
  x.val.liftOn (monomialCoeffShiftFun a S) (monomialCoeffShiftFun_wd a S)

/-- `monomialCoeffShift` as an `AddMonoidHom`. -/
def monomialCoeffShiftHom (a : LaurentExp n d) (S : Finset (Fin (n + 1))) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R S) →+ R where
  toFun := monomialCoeffShift a S
  map_zero' := by
    show monomialCoeffShift a S 0 = 0
    simp only [monomialCoeffShift, HomogeneousLocalizedModule.val_zero]
    rw [show (0 : LocalizedModule (Submonoid.powers (coordProd n R S))
        (MvPolynomial (Fin (n + 1)) R)) = LocalizedModule.mk 0 1 from by
      rw [LocalizedModule.zero_mk], LocalizedModule.liftOn_mk]
    simp [monomialCoeffShiftFun, mul_zero, MvPolynomial.coeff_zero]
  map_add' x y := by
    show monomialCoeffShift a S (x + y) =
      monomialCoeffShift a S x + monomialCoeffShift a S y
    simp only [monomialCoeffShift, HomogeneousLocalizedModule.val_add]
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

end MonomialCoeffShift

/-! ### Orthogonality for shifted monomial elements -/

section ShiftOrthogonality

variable (d : ℤ) (hd : 0 ≤ d)

/-- Extracting the coefficient of a monomial at itself gives `1`. -/
theorem monomialCoeffShift_self (a : LaurentExp n d)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) :
    monomialCoeffShift a S (monomialElemShift (R := R) d hd a S hS) = 1 := by
  simp only [monomialCoeffShift, monomialElemShift,
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
    monomialCoeffShift a S (monomialElemShift (R := R) d hd a' S hS') = 0 := by
  simp only [monomialCoeffShift, monomialElemShift,
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
    monomialCoeffShift a S
      (smulMonomialElemShift (R := R) d hd r a' S hS') =
    if a = a' then r else 0 := by
  simp only [monomialCoeffShift, smulMonomialElemShift,
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

section ShiftFaceCompat

variable {d : ℤ}

/-- `monomialCoeffShift` commutes with `coordRestrict`. -/
theorem monomialCoeffShift_coordRestrict (a : LaurentExp n d)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (hface : a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeffShift a T
      (coordRestrict n R (GradedModule.shift (𝒜 n R) d.toNat) T hT j x) =
    monomialCoeffShift a (TopCat.eraseNth T hT j).1 x := by
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
  have hRHS : monomialCoeffShift a face ⟦q⟧ =
      MvPolynomial.coeff (a.numFinsupp face + coordProdFinsupp face N)
        ((coordProd n R face) ^ cp *
          (q.num : MvPolynomial (Fin (n + 1)) R)) := by
    simp only [monomialCoeffShift, HomogeneousLocalizedModule.val_mk,
      LocalizedModule.liftOn_mk, monomialCoeffShiftFun]
    rw [← hcp_eq]
  rw [hRHS]; clear hRHS
  -- LHS: unfold coordRestrict and monomialCoeffShift
  simp only [monomialCoeffShift, coordRestrict]
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
        linarith
      · rw [coordProdFinsupp_apply_notMem hiT,
          coordProdFinsupp_apply_notMem (fun h => hiT (hi_face_iff.mp h))]
        have : a.numExp face i = a.numExp T i := by
          simp only [LaurentExp.numExp, if_neg (fun h => hiT (hi_face_iff.mp h)),
            if_neg hiT]
        linarith
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

/-- `monomialCoeffShift` vanishes when negSupport is not contained in a face. -/
theorem monomialCoeffShift_coordRestrict_vanish (a : LaurentExp n d)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (hnotface : ¬a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (hfull : a.negSupport ⊆ T)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat)
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeffShift a T
      (coordRestrict n R (GradedModule.shift (𝒜 n R) d.toNat) T hT j x) = 0 := by
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
  simp only [monomialCoeffShift, coordRestrict]
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

end ShiftFaceCompat

/-! ### Injectivity and finite support -/

section ShiftInjectivity

variable {d : ℤ}

/-- If all shifted monomial coefficients are zero, the element is zero. -/
theorem monomialCoeffShift_determines_zero (hd : 0 ≤ d) (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S))
    (h : ∀ (a : LaurentExp n d) (_ : a.negSupport ⊆ S),
      monomialCoeffShift a S x = 0) :
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
  have hcoeff : monomialCoeffShift a S ⟦q⟧ =
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

/-- Only finitely many Laurent exponents have nonzero shifted monomial coefficients. -/
theorem monomialCoeffShift_finite_support (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R)
      (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S)) :
    {a : LaurentExp n d | ∃ _ : a.negSupport ⊆ S,
      monomialCoeffShift a S x ≠ 0}.Finite := by
  revert x; refine Quotient.ind fun q => ?_
  set N := q.den_mem.choose
  set num := (q.num : MvPolynomial (Fin (n + 1)) R)
  let φ : LaurentExp n d → Fin (n + 1) →₀ ℕ := fun a =>
    a.numFinsupp S + coordProdFinsupp S N - coordProdFinsupp S (a.clearingPow S)
  have hφ_spec : ∀ a (_ : a.negSupport ⊆ S),
      monomialCoeffShift a S ⟦q⟧ ≠ 0 →
      coordProdFinsupp S (a.clearingPow S) ≤
        a.numFinsupp S + coordProdFinsupp S N ∧
      monomialCoeffShift a S ⟦q⟧ = MvPolynomial.coeff (φ a) num := by
    intro a _hns hne
    have hraw : monomialCoeffShift a S ⟦q⟧ =
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
      monomialCoeffShift a S ⟦q⟧ ≠ 0}, φ a ∈ num.support := by
    intro a ⟨hns, hne⟩
    rw [MvPolynomial.mem_support_iff]
    rwa [← (hφ_spec a hns hne).2]
  -- φ is injective on nonzero set
  have hφ_inj : Set.InjOn φ
      {a | ∃ _ : a.negSupport ⊆ S, monomialCoeffShift a S ⟦q⟧ ≠ 0} := by
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
  toFun := fun f ⟨S, hS, _hns⟩ => monomialCoeffShift a S (f ⟨S, hS⟩)
  map_zero' := by
    ext ⟨S, hS, _hns⟩; simp only [Pi.zero_apply]
    exact (monomialCoeffShiftHom a S).map_zero
  map_add' x y := by
    ext ⟨S, hS, _hns⟩; simp only [Pi.add_apply]
    exact (monomialCoeffShiftHom a S).map_add (x ⟨S, hS⟩) (y ⟨S, hS⟩)

/-- The component extraction commutes with differentials. -/
theorem componentShift_comm_δ (a : LaurentExp n d) (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R)
        (GradedModule.shift (𝒜 n R) d.toNat) (coordProd n R S.1)) :
    componentHomShift a (p + 1)
      (algebraicδ n R (GradedModule.shift (𝒜 n R) d.toNat) p f) =
    _root_.relSimplexδHom a.negSupport R p (componentHomShift a p f) := by
  ext ⟨T, hT, hfull⟩
  simp only [componentHomShift, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    algebraicδ, _root_.relSimplexδHom, _root_.relSimplexδ_apply]
  show (monomialCoeffShiftHom a T) _ = _
  rw [map_sum]
  congr 1; ext j
  rw [map_zsmul]
  simp only [monomialCoeffShiftHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hface
  · congr 1; exact monomialCoeffShift_coordRestrict a hT j hface _
  · rw [monomialCoeffShift_coordRestrict_vanish a hT j hface hfull _, smul_zero]

end ShiftComponentChainMap

/-! ### Bridge: degree-0 coefficient agrees with zero-exponent extraction -/

section ZeroBridge

/-- When `a = 0` (degree 0), `monomialCoeffShift` agrees with `zeroExpCoeffMod`.
This bridges the general shifted coefficient extraction with the degree-0 extraction
used by `extractionHom`. -/
theorem monomialCoeffShift_zero_eq (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S)) :
    monomialCoeffShift (0 : LaurentExp n 0) S x = zeroExpCoeffMod (R := R) S x := by
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

/-- `componentHomShift` at `a = 0` agrees with `extractionHom`. -/
theorem componentHomShift_zero_apply (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1))
    {S : Finset (Fin (n + 1))} (hS : S.card = p + 1)
    (hns : (0 : LaurentExp n 0).negSupport ⊆ S) :
    componentHomShift (0 : LaurentExp n 0) p f ⟨S, hS, hns⟩ =
    extractionHom p f ⟨S, hS, Finset.empty_subset S⟩ := by
  simp only [componentHomShift, extractionHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact monomialCoeffShift_zero_eq S (f ⟨S, hS⟩)

end ZeroBridge

end AlgebraicGeometry.Proj
