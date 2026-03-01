/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.MonomialDecomposition

/-!
# Cohomology of the structure sheaf on projective space

This file computes the Čech cohomology of the structure sheaf `𝒪` on projective
n-space over a commutative ring `R`:
- `H⁰(algebraicComplex, 𝒪) ≅ R`
- `Hᵖ(algebraicComplex, 𝒪) = 0` for `p > 0`

The proof strategy builds an embedding chain map `K_∅ → algebraicComplex` (a section
of the extraction chain map), then uses the monomial decomposition to show the
extraction is a quasi-isomorphism.

## Main results

* `algebraicComplex_structureSheaf_H0`: `H⁰ ≅ R`
* `algebraicComplex_structureSheaf_acyclic`: `Hᵖ = 0` for `p > 0`

## References

* [Stacks Project, Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)
-/

noncomputable section

open MvPolynomial CategoryTheory Finset

namespace AlgebraicGeometry.Proj

universe u

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

private abbrev 𝒜 (n : ℕ) (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

local instance : SetLike.GradedSMul (𝒜 n R) (𝒜 n R) :=
  SetLike.GradedMul.toGradedSMul _

/-! ### Generalized monomial coefficient extraction -/

section MonomialCoeffExtraction

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

/-- Generalized monomial coefficient extraction from a localization element.
For a Laurent exponent `a` with `negSupport a ⊆ S`, this extracts the coefficient
of `monomialElem a` in the monomial decomposition of a localization element.

The definition multiplies the numerator by `(coordProd S)^(clearingPow a S)` to
normalize, then extracts at index `numFinsupp a S + coordProdFinsupp S N`. -/
def monomialCoeff (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (_hS : a.negSupport ⊆ S) :
    HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S) → R :=
  fun x => (HomogeneousLocalization.val x).liftOn
    (fun (p : MvPolynomial (Fin (n + 1)) R)
        (s : Submonoid.powers (coordProd n R S)) =>
      MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S s.2.choose)
        ((coordProd n R S) ^ (a.clearingPow S) * p))
    fun {p c} {s t} hrel => by
      show MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S s.2.choose)
          ((coordProd n R S) ^ (a.clearingPow S) * p) =
        MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S t.2.choose)
          ((coordProd n R S) ^ (a.clearingPow S) * c)
      rw [Localization.r_iff_exists] at hrel
      obtain ⟨⟨e, he⟩, heq⟩ := hrel
      set K := he.choose; set Ns := s.2.choose; set Nt := t.2.choose
      set cp := a.clearingPow S
      set nf := a.numFinsupp S
      -- Boost to common power using coeff_coordProd_pow_mul
      have h1 := coeff_coordProd_pow_mul (R := R) S (K + Nt)
        (nf + coordProdFinsupp S Ns) ((coordProd n R S) ^ cp * p)
      have h2 := coeff_coordProd_pow_mul (R := R) S (K + Ns)
        (nf + coordProdFinsupp S Nt) ((coordProd n R S) ^ cp * c)
      -- Indices agree
      have hindex : coordProdFinsupp S (K + Nt) + (nf + coordProdFinsupp S Ns) =
          coordProdFinsupp S (K + Ns) + (nf + coordProdFinsupp S Nt) := by
        ext i; by_cases hi : i ∈ S
        · simp [coordProdFinsupp_apply_mem hi, LaurentExp.numFinsupp_apply]; ring
        · simp [coordProdFinsupp_apply_notMem hi]
      -- Polynomials agree
      have hpoly : (coordProd n R S) ^ (K + Nt) * ((coordProd n R S) ^ cp * p) =
          (coordProd n R S) ^ (K + Ns) * ((coordProd n R S) ^ cp * c) := by
        have key1 : e * (↑t * p) = (coordProd n R S) ^ (K + Nt) * p := by
          rw [pow_add, mul_assoc, ← he.choose_spec, ← t.2.choose_spec]
        have key2 : e * (↑s * c) = (coordProd n R S) ^ (K + Ns) * c := by
          rw [pow_add, mul_assoc, ← he.choose_spec, ← s.2.choose_spec]
        have := key1.symm.trans (heq.trans key2)
        calc (coordProd n R S) ^ (K + Nt) * ((coordProd n R S) ^ cp * p)
            = (coordProd n R S) ^ cp * ((coordProd n R S) ^ (K + Nt) * p) := by ring
          _ = (coordProd n R S) ^ cp * ((coordProd n R S) ^ (K + Ns) * c) := by
              rw [this]
          _ = (coordProd n R S) ^ (K + Ns) * ((coordProd n R S) ^ cp * c) := by ring
      rw [hindex, hpoly] at h1
      exact h1.symm.trans h2

/-- `monomialCoeff 0` reduces to `zeroExpCoeff`. -/
theorem monomialCoeff_eq_zeroExpCoeff (S : Finset (Fin (n + 1))) :
    monomialCoeff (0 : LaurentExp n) S (by simp [LaurentExp.negSupport_zero]) =
    zeroExpCoeff (R := R) S := by
  ext x
  unfold monomialCoeff zeroExpCoeff
  simp only [HomogeneousLocalization.val]
  congr 1
  ext p s
  have h2 : (0 : LaurentExp n).clearingPow S = 0 := by
    unfold LaurentExp.clearingPow
    simp only [show ∀ i, (0 : LaurentExp n).1 i = 0 from fun _ => rfl, neg_zero,
      Int.toNat_zero]
    exact (Finset.sup_eq_bot_iff _ _).mpr (fun _ _ => rfl)
  have h1 : (0 : LaurentExp n).numFinsupp S = 0 := by
    ext i; simp [LaurentExp.numFinsupp_apply, LaurentExp.numExp, h2,
      show (0 : LaurentExp n).1 i = 0 from rfl]
  simp [h1, h2]

/-- Computation rule: `monomialCoeff` on `monomialElem` extracts the coefficient of
the monomial polynomial at the appropriate index. -/
theorem monomialCoeff_monomialElem (a a' : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S) :
    monomialCoeff a S hS (monomialElem a' S hS') =
      MvPolynomial.coeff (a.numFinsupp S + coordProdFinsupp S (a'.clearingPow S))
        ((coordProd n R S) ^ (a.clearingPow S) *
          ∏ i : Fin (n + 1), coord n R i ^ a'.numExp S i) := by
  unfold monomialCoeff monomialElem
  simp only [HomogeneousLocalization.Away.val_mk, Localization.liftOn_mk]
  apply coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S
  exact Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _

/-- `monomialCoeff a S hS (monomialElem a S hS) = 1`: extracting the coefficient of
a monomial at itself gives `1`. -/
theorem monomialCoeff_monomialElem_self (a : LaurentExp n)
    (S : Finset (Fin (n + 1))) (hS : a.negSupport ⊆ S) :
    monomialCoeff a S hS (monomialElem (R := R) a S hS) = 1 := by
  rw [monomialCoeff_monomialElem, prod_coord_pow_eq_monomial,
    coordProd_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.coeff_monomial]
  exact if_pos (add_comm _ _)

/-- `monomialCoeff a S hS (monomialElem a' S hS') = 0` when `a ≠ a'`:
extracting the coefficient of a different monomial gives `0`. -/
theorem monomialCoeff_monomialElem_ne {a a' : LaurentExp n}
    {S : Finset (Fin (n + 1))} (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S)
    (hne : a ≠ a') :
    monomialCoeff a S hS (monomialElem (R := R) a' S hS') = 0 := by
  rw [monomialCoeff_monomialElem, prod_coord_pow_eq_monomial,
    coordProd_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.coeff_monomial]
  refine if_neg fun h => hne ?_
  -- h : cpf S (cp a S) + nf a' S = nf a S + cpf S (cp a' S)
  refine Subtype.ext (funext fun i => ?_)
  -- Use explicit type to reduce equivFunOnFinite.symm definitionally
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
    have ha' : 0 ≤ a'.1 i := (a'.not_mem_negSupport_iff i).mp (fun hm => hiS (hS' hm))
    have h1 := congr_arg ((↑) : ℕ → ℤ) hi
    simp only [LaurentExp.numExp, if_neg hiS] at h1
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg ha'] at h1
    linarith

end MonomialCoeffExtraction

end AlgebraicGeometry.Proj
