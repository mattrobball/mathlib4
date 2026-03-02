/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.CechCover
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.CechCohomology

/-!
# Monomial decomposition of the structure sheaf algebraic complex

For the structure sheaf `𝒪` on projective n-space `Proj(R[x₀,...,xₙ])`, the algebraic
Čech complex decomposes as a direct sum of relative simplex complexes `K_T`, indexed by
**Laurent exponents**: integer vectors `a : Fin(n+1) → ℤ` with `∑ aᵢ = d`.

The degree parameter `d` defaults to `0` for the structure sheaf. Each monomial
`∏ xᵢ^aᵢ` in the degree-`d` localization `R[x₀,...,xₙ]_(coordProd S)` defines a
basis element, and its **negative support** `T(a) = {i : aᵢ < 0}` determines which
localization it lives in (it requires `T(a) ⊆ S`). This gives a bijection between
the cochains of the algebraic complex and a direct sum of `K_{T(a)}` cochains.

Combined with the acyclicity results from `RelativeSimplexComplex.lean`, this yields:
- `H⁰(algebraicComplex, 𝒪) ≅ R`
- `Hᵖ(algebraicComplex, 𝒪) = 0` for `p > 0`

## Main definitions

* `AlgebraicGeometry.Proj.LaurentExp`: Laurent exponents of degree `d` (default 0).
* `AlgebraicGeometry.Proj.negSupport`: The negative support of a Laurent exponent.

## References

* [Stacks Project, Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)
-/

noncomputable section

open MvPolynomial CategoryTheory Finset

namespace AlgebraicGeometry.Proj

universe u

variable (n : ℕ) (R : Type u) [CommRing R]

attribute [local instance] mvPolynomialGrading

private abbrev 𝒜 (n : ℕ) (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-! ### Laurent exponents and negative support -/

/-- A Laurent exponent of degree `d`: an integer vector `a : Fin (n+1) → ℤ` with `∑ aᵢ = d`.
These index the Laurent monomials in the degree-`d` localization. When `d = 0` (the default),
these are the degree-zero Laurent monomials used for the structure sheaf. -/
def LaurentExp (n : ℕ) (d : ℤ := 0) := { a : Fin (n + 1) → ℤ // ∑ i, a i = d }

namespace LaurentExp

variable {n : ℕ} {d : ℤ}

instance : Zero (LaurentExp n) := ⟨⟨0, by simp⟩⟩

instance : DecidableEq (LaurentExp n d) := Subtype.instDecidableEq

/-- The negative support: the set of indices where the exponent is strictly negative. -/
def negSupport (a : LaurentExp n d) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => decide (a.1 i < 0))

theorem mem_negSupport_iff (a : LaurentExp n d) (i : Fin (n + 1)) :
    i ∈ negSupport a ↔ a.1 i < 0 := by
  simp [negSupport]

theorem not_mem_negSupport_iff (a : LaurentExp n d) (i : Fin (n + 1)) :
    i ∉ negSupport a ↔ 0 ≤ a.1 i := by
  rw [mem_negSupport_iff]; omega

@[simp]
theorem negSupport_zero : negSupport (0 : LaurentExp n) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i; rw [mem_negSupport_iff]
  change ¬ (0 : ℤ) < 0; omega

/-- The negative support cannot be all of `Fin (n + 1)`: if all `aᵢ < 0` then
`∑ aᵢ < 0`, contradicting `∑ aᵢ = d ≥ 0`. -/
theorem negSupport_ne_univ (a : LaurentExp n d) (hd : 0 ≤ d) :
    negSupport a ≠ Finset.univ := by
  intro h
  have hlt : ∀ i, a.1 i < 0 := fun i =>
    (mem_negSupport_iff a i).mp (h ▸ mem_univ i)
  have : ∑ i, a.1 i < 0 := Finset.sum_neg (f := a.1) (s := Finset.univ)
    (fun i _ => hlt i) ⟨⟨0, Nat.zero_lt_succ n⟩, mem_univ _⟩
  linarith [a.2]

/-- If `negSupport a = ∅` for a degree-0 Laurent exponent, then `a = 0`. -/
theorem negSupport_empty_iff (a : LaurentExp n) :
    negSupport a = ∅ ↔ a = (0 : LaurentExp n) := by
  constructor
  · intro h
    have hpos : ∀ j, 0 ≤ a.1 j := by
      intro j; rw [← not_mem_negSupport_iff]; rw [h]; exact Finset.notMem_empty _
    refine Subtype.ext (funext fun i => ?_)
    have hge : 0 ≤ a.1 i := hpos i
    have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, a.1 j :=
      Finset.sum_nonneg fun j _ => hpos j
    have hsplit : a.1 i + ∑ j ∈ Finset.univ.erase i, a.1 j = 0 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]; exact a.2
    show a.1 i = 0; linarith
  · rintro rfl; exact negSupport_zero

/-- If `negSupport a = ∅`, then all entries are nonneg. -/
theorem negSupport_empty_iff_nonneg (a : LaurentExp n d) :
    negSupport a = ∅ ↔ ∀ i, 0 ≤ a.1 i := by
  constructor
  · intro h i; rw [← not_mem_negSupport_iff]; rw [h]; exact Finset.notMem_empty _
  · intro h; rw [Finset.eq_empty_iff_forall_notMem]
    intro i; rw [not_mem_negSupport_iff]; exact h i

end LaurentExp

/-! ### Adjoin coordinates over 𝒜₀ -/

/-- The coordinate variables generate `MvPolynomial` as an algebra over the degree-zero
part `𝒜₀`. This is the graded version of `MvPolynomial.adjoin_range_X`. -/
theorem adjoin_coord_eq_top :
    Algebra.adjoin (↥(𝒜 n R 0)) (Set.range (coord n R)) = ⊤ := by
  rw [Algebra.eq_top_iff]
  intro x
  induction x using MvPolynomial.induction_on with
  | C r =>
    have hmem : MvPolynomial.C r ∈ 𝒜 n R 0 := isHomogeneous_C _ r
    exact (Algebra.adjoin (↥(𝒜 n R 0)) _).algebraMap_mem ⟨_, hmem⟩
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-! ### Ring ↔ Module localization equivalence -/

section RingModuleEquiv

variable {ι' : Type*} [AddCommMonoid ι'] [DecidableEq ι']
  {R' : Type*} [CommRing R'] {A : Type*} [CommRing A] [Algebra R' A]
  (𝒜' : ι' → Submodule R' A) [GradedAlgebra 𝒜'] {f : A}

/-- Convert a ring `NumDenSameDeg` to a module `NumDenSameDeg` when the module
grading equals the ring grading (`𝓜 = 𝒜`). The data is identical. -/
private def ringToModuleND
    (p : HomogeneousLocalization.NumDenSameDeg 𝒜' (Submonoid.powers f)) :
    HomogeneousLocalizedModule.NumDenSameDeg 𝒜' 𝒜' (Submonoid.powers f) :=
  ⟨p.deg, p.num, p.den, p.den_mem⟩

/-- Convert a module `NumDenSameDeg` back to a ring `NumDenSameDeg`. -/
private def moduleToRingND
    (p : HomogeneousLocalizedModule.NumDenSameDeg 𝒜' 𝒜' (Submonoid.powers f)) :
    HomogeneousLocalization.NumDenSameDeg 𝒜' (Submonoid.powers f) :=
  ⟨p.deg, p.num, p.den, p.den_mem⟩

/-- The localization equivalence relations agree: `Localization.mk a s = Localization.mk b t`
iff `LocalizedModule.mk a s = LocalizedModule.mk b t`, when the module is the ring itself. -/
private theorem localization_mk_eq_iff_localizedModule_mk_eq
    {a b : A} {s t : Submonoid.powers f} :
    Localization.mk a s = Localization.mk b t ↔
    LocalizedModule.mk (R := A) a s = LocalizedModule.mk b t := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists, LocalizedModule.mk_eq]
  simp only [Submonoid.smul_def, smul_eq_mul]

/-- The `AddEquiv` between the ring localization `𝒜_(f)` and the module localization
when `𝓜 = 𝒜` (the structure sheaf case). -/
def awayRingModuleEquiv :
    HomogeneousLocalization.Away 𝒜' f ≃+
    HomogeneousLocalizedModule.Away 𝒜' 𝒜' f where
  toFun := Quotient.map' (ringToModuleND 𝒜') fun _ _ h =>
    (localization_mk_eq_iff_localizedModule_mk_eq).mp h
  invFun := Quotient.map' (moduleToRingND 𝒜') fun _ _ h =>
    (localization_mk_eq_iff_localizedModule_mk_eq).mpr h
  left_inv x := Quotient.inductionOn' x fun _ => rfl
  right_inv x := Quotient.inductionOn' x fun _ => rfl
  map_add' x y := by
    haveI : SetLike.GradedSMul 𝒜' 𝒜' := SetLike.GradedMul.toGradedSMul 𝒜'
    induction x, y using Quotient.inductionOn₂' with
    | _ p q =>
      simp only [← HomogeneousLocalization.mk_add, Quotient.map'_mk'',
        ← HomogeneousLocalizedModule.mk_add]
      apply HomogeneousLocalizedModule.ext (Submonoid.powers f)
      simp only [HomogeneousLocalizedModule.val_mk,
        HomogeneousLocalizedModule.NumDenSameDeg.embedding, ringToModuleND,
        HomogeneousLocalization.NumDenSameDeg.num_add,
        HomogeneousLocalization.NumDenSameDeg.den_add,
        HomogeneousLocalizedModule.NumDenSameDeg.num_add,
        HomogeneousLocalizedModule.NumDenSameDeg.den_add]
      congr 1
      simp only [smul_eq_mul]; ring

end RingModuleEquiv

/-! ### Monomial elements in Away localization -/

section MonomialElements

namespace LaurentExp

variable {n : ℕ} {d : ℤ}

/-- The clearing power: maximum of `(-aᵢ).toNat` for `i ∈ S`. This ensures
`aᵢ + clearingPow a S ≥ 0` for all `i ∈ S`. Returns `0` for `S = ∅`. -/
def clearingPow (a : LaurentExp n d) (S : Finset (Fin (n + 1))) : ℕ :=
  S.sup (fun i => (-a.1 i).toNat)

theorem clearingPow_nonneg (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ S) :
    0 ≤ a.1 i + ↑(a.clearingPow S) := by
  have : (-a.1 i).toNat ≤ a.clearingPow S :=
    Finset.le_sup (f := fun i => (-a.1 i).toNat) hi
  omega

/-- The numerator exponent for the monomial element at index `i`. -/
def numExp (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : ℕ :=
  if i ∈ S then (a.1 i + ↑(a.clearingPow S)).toNat else (a.1 i).toNat

private theorem numExp_cast (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) (i : Fin (n + 1)) :
    (a.numExp S i : ℤ) = a.1 i + if i ∈ S then ↑(a.clearingPow S) else 0 := by
  simp only [numExp]
  split_ifs with hi
  · exact Int.toNat_of_nonneg (a.clearingPow_nonneg S i hi)
  · have : 0 ≤ a.1 i := (a.not_mem_negSupport_iff i).mp (fun h => hi (hS h))
    rw [add_zero]
    exact Int.toNat_of_nonneg this

/-- The sum of numerator exponents: `∑ numExp = clearingPow * |S| + d.toNat`.
For degree-0 exponents this gives `clearingPow * |S|`. For nonneg degree `d`,
this gives the numerator degree in the shifted module localization. -/
theorem numExp_sum (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    (∑ i : Fin (n + 1), a.numExp S i : ℤ) =
      ↑(a.clearingPow S) * ↑S.card + d := by
  push_cast [a.numExp_cast S hS]
  rw [Finset.sum_add_distrib, a.2]
  have : Finset.univ.filter (fun x : Fin (n + 1) => x ∈ S) = S := by ext x; simp
  rw [← Finset.sum_filter, this, Finset.sum_const, nsmul_eq_mul, mul_comm]
  ring

/-- Specialization of `numExp_sum` for degree-0 exponents, giving a `ℕ` equality. -/
theorem numExp_sum_zero (a : LaurentExp n (0 : ℤ)) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    ∑ i : Fin (n + 1), a.numExp S i = a.clearingPow S * S.card := by
  have h := numExp_sum a S hS
  simp only [Int.natCast_ediv, CharP.cast_eq_zero, add_zero] at h
  exact_mod_cast h

/-- Specialization of `numExp_sum` for nonneg-degree exponents, giving a `ℕ` equality. -/
theorem numExp_sum_nonneg (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) (hd : 0 ≤ d) :
    ∑ i : Fin (n + 1), a.numExp S i = a.clearingPow S * S.card + d.toNat := by
  have h := numExp_sum a S hS
  -- h : (↑(∑ numExp) : ℤ) = ↑cp * ↑|S| + d
  -- Goal: ∑ numExp = cp * |S| + d.toNat (in ℕ)
  have key : (↑(a.clearingPow S * S.card + d.toNat) : ℤ) =
      ↑(a.clearingPow S) * ↑S.card + d := by
    push_cast; exact (Int.toNat_of_nonneg hd).symm ▸ rfl
  exact_mod_cast h.trans key.symm

end LaurentExp

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

/-- The monomial element in `Away (𝒜 n R) (coordProd n R S)` corresponding to a
Laurent exponent `a` with `negSupport a ⊆ S`. This represents the monomial
`∏ Xᵢ^aᵢ` in the degree-zero localization at `coordProd S`. -/
def monomialElem (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S) :=
  HomogeneousLocalization.Away.mk (𝒜 n R) (coordProd_mem_homogeneous n R S)
    (a.clearingPow S)
    (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i)
    (by
      have h := SetLike.prod_pow_mem_graded (F := Finset.univ) (𝒜 n R)
        (fun _ : Fin (n + 1) => (1 : ℕ)) (coord n R) (fun i => a.numExp S i)
        (fun i _ => coord_mem_homogeneousSubmodule n R i)
      simp only [smul_eq_mul, mul_one] at h
      rwa [a.numExp_sum_zero S hS] at h)

/-- The Away localization at `coordProd S` is spanned over `𝒜₀` by monomials.
This specializes `Away.span_mk_prod_pow_eq_top` to coordinate variables. -/
theorem coordProd_away_span_eq_top (S : Finset (Fin (n + 1))) :
    Submodule.span (↥(𝒜 n R 0))
      { HomogeneousLocalization.Away.mk (𝒜 n R) (coordProd_mem_homogeneous n R S)
          N (∏ i : Fin (n + 1), coord n R i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded (𝒜 n R) (fun _ => (1 : ℕ))
            (coord n R) ai (fun i _ => coord_mem_homogeneousSubmodule n R i)) |
        (N : ℕ) (ai : Fin (n + 1) → ℕ)
        (hai : ∑ i, ai i • (1 : ℕ) = N • S.card) } = ⊤ :=
  HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
    (coordProd_mem_homogeneous n R S) (coord n R) (adjoin_coord_eq_top n R)
    (fun _ => 1) (fun i => coord_mem_homogeneousSubmodule n R i)

end MonomialElements

/-! ### Chain map property: face maps preserve monomial elements -/

section ChainMap

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

local instance gradedSMulSelf : SetLike.GradedSMul (𝒜 n R) (𝒜 n R) :=
  SetLike.GradedMul.toGradedSMul _

namespace LaurentExp

/-- Erasing an index with nonneg exponent does not change the clearing power.
When `0 ≤ a.1 j`, the term `(-a.1 j).toNat = 0` does not affect the sup. -/
theorem clearingPow_erase {d : ℤ} {a : LaurentExp n d} {S : Finset (Fin (n + 1))}
    {j : Fin (n + 1)} (hj : j ∈ S) (hjnn : 0 ≤ a.1 j) :
    a.clearingPow (S.erase j) = a.clearingPow S := by
  apply le_antisymm
  · exact Finset.sup_mono (Finset.erase_subset j S)
  · refine Finset.sup_le fun i hi => ?_
    by_cases heq : i = j
    · subst heq
      simp [clearingPow, Int.toNat_eq_zero.mpr (neg_nonpos_of_nonneg hjnn)]
    · exact Finset.le_sup (f := fun i => (-a.1 i).toNat)
        (Finset.mem_erase.mpr ⟨heq, hi⟩)

/-- `numExp` is unchanged at indices distinct from the erased element. -/
theorem numExp_erase_of_ne {d : ℤ} {a : LaurentExp n d} {S : Finset (Fin (n + 1))}
    {j i : Fin (n + 1)} (hj : j ∈ S) (hjnn : 0 ≤ a.1 j) (hne : i ≠ j) :
    a.numExp (S.erase j) i = a.numExp S i := by
  simp only [numExp, clearingPow_erase hj hjnn]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Finset.mem_erase.mp h1).2 h2
  · exact absurd (Finset.mem_erase.mpr ⟨hne, h2⟩) h1
  · rfl

/-- At the erased index, `numExp` at the face plus the clearing power gives `numExp`
at the full set. -/
theorem numExp_erase_add {d : ℤ} {a : LaurentExp n d} {S : Finset (Fin (n + 1))}
    {j : Fin (n + 1)} (hj : j ∈ S) (hjnn : 0 ≤ a.1 j) :
    a.numExp (S.erase j) j + a.clearingPow S = a.numExp S j := by
  simp only [numExp, Finset.notMem_erase, ↓reduceIte, hj, clearingPow_erase hj hjnn]
  suffices h : (↑((a.1 j).toNat + a.clearingPow S) : ℤ) =
      ↑((a.1 j + ↑(a.clearingPow S)).toNat) by exact_mod_cast h
  rw [Nat.cast_add, Int.toNat_of_nonneg hjnn,
    Int.toNat_of_nonneg (add_nonneg hjnn (Int.natCast_nonneg _))]

end LaurentExp

/-- The monomial element in the module localization, for use with the algebraic
complex and `coordRestrict`. -/
def monomialElemMod (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S) :=
  HomogeneousLocalizedModule.Away.mk (𝒜 n R) (𝒜 n R)
    (coordProd_mem_homogeneous n R S)
    (a.clearingPow S)
    (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i)
    (by
      have h := SetLike.prod_pow_mem_graded (F := Finset.univ) (𝒜 n R)
        (fun _ : Fin (n + 1) => (1 : ℕ)) (coord n R) (fun i => a.numExp S i)
        (fun i _ => coord_mem_homogeneousSubmodule n R i)
      simp only [smul_eq_mul, mul_one] at h
      rwa [a.numExp_sum_zero S hS] at h)

/-- The numerator identity: multiplying the face numerator by the erased coordinate
power gives the full numerator. -/
theorem monomialElem_numerator_mul (a : LaurentExp n)
    {S : Finset (Fin (n + 1))}
    {j : Fin (n + 1)} (hj : j ∈ S) (hjnn : 0 ≤ a.1 j) :
    coord n R j ^ a.clearingPow S *
      ∏ i : Fin (n + 1), coord n R i ^ a.numExp (S.erase j) i =
    ∏ i : Fin (n + 1), coord n R i ^ a.numExp S i := by
  conv_rhs =>
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => coord n R i ^ a.numExp S i) (Finset.mem_univ j)]
  conv_lhs =>
    arg 2
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => coord n R i ^ a.numExp (S.erase j) i) (Finset.mem_univ j)]
  rw [← mul_assoc, ← pow_add]
  congr 1
  · exact congr_arg (coord n R j ^ ·)
      ((Nat.add_comm _ _).trans (a.numExp_erase_add hj hjnn))
  · exact Finset.prod_congr rfl fun i hi =>
      congr_arg _ (a.numExp_erase_of_ne hj hjnn (Finset.mem_erase.mp hi).1)

/-- Face restriction preserves monomial elements: restricting the monomial for `a` at
face `eraseNth T hT j` gives the monomial for `a` at `T`. This is the key
compatibility between `coordRestrict` and the monomial decomposition. -/
theorem coordRestrict_monomialElemMod {p : ℕ} (a : LaurentExp n)
    {T : Finset (Fin (n + 1))} (hT : T.card = p + 2) (j : Fin (p + 2))
    (hface : a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (hfull : a.negSupport ⊆ T) :
    coordRestrict n R (𝒜 n R) T hT j
      (monomialElemMod a (TopCat.eraseNth T hT j).1 hface) =
    monomialElemMod a T hfull := by
  set j_elem := TopCat.nthElem T hT j
  have hj_mem : j_elem ∈ T := TopCat.nthElem_mem T hT j
  have hface_eq : (TopCat.eraseNth T hT j).1 = T.erase j_elem := rfl
  have hj_nn : 0 ≤ a.1 j_elem := by
    rw [← a.not_mem_negSupport_iff]
    exact fun hmem => absurd (hface hmem) (hface_eq ▸ Finset.notMem_erase j_elem T)
  -- Reduce to equality in LocalizedModule via val_injective
  apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R T))
  -- Unfold coordRestrict to awayMap and monomialElemMod to Away.mk, compute val
  unfold coordRestrict monomialElemMod
  rw [HomogeneousLocalizedModule.awayMap_Away_mk, HomogeneousLocalizedModule.Away.val_mk]
  -- Both sides are now LocalizedModule.mk; align clearing powers
  rw [hface_eq, a.clearingPow_erase hj_mem hj_nn]
  -- Numerator: (coord j_elem ^ N) • num_face = num_T
  -- Denominator: same val, different proofs
  congr 1
  show (coord n R j_elem ^ a.clearingPow T : MvPolynomial (Fin (n + 1)) R) •
    ∏ i, coord n R i ^ a.numExp (T.erase j_elem) i =
    ∏ i, coord n R i ^ a.numExp T i
  rw [smul_eq_mul]
  exact monomialElem_numerator_mul a hj_mem hj_nn

/-! ### Monomial cochains and the algebraic coboundary -/

namespace LaurentExp

/-- Characterization of when the negative support is contained in a face:
`negSupport a ⊆ eraseNth T hT j` iff the erased element `nthElem T hT j`
has nonneg exponent in `a`, given that `negSupport a ⊆ T`. -/
theorem negSupport_subset_eraseNth_iff {d : ℤ} (a : LaurentExp n d)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2)) (hfull : a.negSupport ⊆ T) :
    a.negSupport ⊆ (TopCat.eraseNth T hT j).1 ↔
      0 ≤ a.1 (TopCat.nthElem T hT j) := by
  constructor
  · intro h
    rw [← a.not_mem_negSupport_iff]
    exact fun hmem => absurd (h hmem) (Finset.notMem_erase _ _)
  · intro hnn i hi
    exact Finset.mem_erase.mpr
      ⟨fun heq => by rw [heq, a.mem_negSupport_iff] at hi; linarith, hfull hi⟩

end LaurentExp

/-- The constant monomial cochain: assigns `monomialElemMod a S` to each
`(p+1)`-element set `S` containing `negSupport a`, and `0` otherwise. -/
def monomialCochain (a : LaurentExp n) (p : ℕ) :
    ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1) :=
  fun ⟨S, _⟩ => if h : a.negSupport ⊆ S then monomialElemMod a S h else 0

/-- The algebraic coboundary of a monomial cochain vanishes at sets not containing
`negSupport a`: all face terms are zero since no face can contain `negSupport a`. -/
theorem algebraicδ_monomialCochain_eq_zero {p : ℕ} (a : LaurentExp n)
    {T : Finset (Fin (n + 1))} (hT : T.card = p + 2) (hns : ¬a.negSupport ⊆ T) :
    algebraicδ n R (𝒜 n R) p (monomialCochain a p) ⟨T, hT⟩ = 0 := by
  show ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
      coordRestrict n R (𝒜 n R) T hT j
        (monomialCochain a p (TopCat.eraseNth T hT j)) = 0
  apply Finset.sum_eq_zero
  intro j _
  have hface : ¬a.negSupport ⊆ (TopCat.eraseNth T hT j).1 :=
    fun h => hns (h.trans (erase_subset _ _))
  simp only [monomialCochain, dif_neg hface, map_zero, smul_zero]

/-- The algebraic coboundary of a monomial cochain at a set containing `negSupport a`
is a signed sum of copies of the monomial at `T`, with the signs and vanishing
pattern matching the relative simplex differential `relSimplexδ`. -/
theorem algebraicδ_monomialCochain_subset {p : ℕ} (a : LaurentExp n)
    {T : Finset (Fin (n + 1))} (hT : T.card = p + 2) (hfull : a.negSupport ⊆ T) :
    algebraicδ n R (𝒜 n R) p (monomialCochain a p) ⟨T, hT⟩ =
      ∑ j : Fin (p + 2),
        if a.negSupport ⊆ (TopCat.eraseNth T hT j).1
        then ((-1 : ℤ) ^ j.val) • monomialElemMod a T hfull
        else 0 := by
  show ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
      coordRestrict n R (𝒜 n R) T hT j
        (monomialCochain a p (TopCat.eraseNth T hT j)) = _
  congr 1; ext j
  by_cases hface : a.negSupport ⊆ (TopCat.eraseNth T hT j).1
  · simp only [monomialCochain, dif_pos hface, if_pos hface]
    rw [coordRestrict_monomialElemMod (R := R) a hT j hface hfull]
  · simp only [monomialCochain, dif_neg hface, map_zero, smul_zero, if_neg hface]

/-- The algebraic coboundary of a monomial cochain equals the relative simplex
coboundary of the constant integer cochain `1`, scalar-multiplied by the monomial.
This exhibits the compatibility between the algebraic and combinatorial differentials:
the monomial decomposition is a chain map. -/
theorem algebraicδ_monomialCochain_eq_relSimplexδ_smul {p : ℕ} (a : LaurentExp n)
    {T : Finset (Fin (n + 1))} (hT : T.card = p + 2) (hfull : a.negSupport ⊆ T) :
    algebraicδ n R (𝒜 n R) p (monomialCochain a p) ⟨T, hT⟩ =
      (relSimplexδ a.negSupport ℤ p (fun _ => 1) ⟨T, ⟨hT, hfull⟩⟩) •
        monomialElemMod a T hfull := by
  rw [algebraicδ_monomialCochain_subset a hT hfull, relSimplexδ_apply, Finset.sum_smul]
  congr 1; funext j
  split_ifs with h
  · simp [smul_eq_mul]
  · exact (zero_smul ℤ (monomialElemMod (R := R) a T hfull)).symm

end ChainMap

/-! ### Coefficient extraction from monomial elements -/

section CoefficientExtraction

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

namespace LaurentExp

variable {d : ℤ}

/-- The Finsupp encoding the numerator exponents for Laurent exponent `a` at set `S`.
This is the `Finsupp` version of `numExp a S`. -/
def numFinsupp (a : LaurentExp n d) (S : Finset (Fin (n + 1))) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (a.numExp S)

@[simp]
theorem numFinsupp_apply (a : LaurentExp n d) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : a.numFinsupp S i = a.numExp S i := rfl

/-- `numFinsupp` is injective: if two Laurent exponents produce the same numerator
exponent pattern at a common containing set `S`, they must be equal. -/
theorem numFinsupp_injective {a a' : LaurentExp n d} {S : Finset (Fin (n + 1))}
    (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S)
    (h : a.numFinsupp S = a'.numFinsupp S) : a = a' := by
  have heq : ∀ i, a.numExp S i = a'.numExp S i := fun i => DFunLike.congr_fun h i
  have hout : ∀ i, i ∉ S → a.1 i = a'.1 i := by
    intro i hi
    have ha : 0 ≤ a.1 i := (a.not_mem_negSupport_iff i).mp (fun hm => hi (hS hm))
    have ha' : 0 ≤ a'.1 i := (a'.not_mem_negSupport_iff i).mp (fun hm => hi (hS' hm))
    have := heq i
    unfold numExp at this; rw [if_neg hi, if_neg hi] at this
    omega
  by_cases hSe : S = ∅
  · subst hSe
    -- All entries are nonneg (negSupport ⊆ ∅), so numExp i = (aᵢ).toNat
    refine Subtype.ext (funext fun i => ?_)
    have ha : 0 ≤ a.1 i := (a.not_mem_negSupport_iff i).mp
      (fun hm => absurd (hS hm) (Finset.notMem_empty _))
    have ha' : 0 ≤ a'.1 i := (a'.not_mem_negSupport_iff i).mp
      (fun hm => absurd (hS' hm) (Finset.notMem_empty _))
    have := heq i
    unfold numExp at this; rw [if_neg (Finset.notMem_empty _),
      if_neg (Finset.notMem_empty _)] at this
    omega
  · have hcpS : a.clearingPow S = a'.clearingPow S := by
      have hsumEq : (∑ i : Fin (n + 1), (a.numExp S i : ℤ)) =
          ∑ i, (a'.numExp S i : ℤ) :=
        Finset.sum_congr rfl fun i _ => by exact_mod_cast heq i
      rw [a.numExp_sum S hS, a'.numExp_sum S hS'] at hsumEq
      -- hsumEq : ↑cp * ↑|S| + d = ↑cp' * ↑|S| + d
      have hpos : 0 < S.card :=
        Finset.card_pos.mpr (by rwa [Finset.nonempty_iff_ne_empty])
      have hmul : a.clearingPow S * S.card = a'.clearingPow S * S.card := by
        exact_mod_cast (show (↑(a.clearingPow S) : ℤ) * ↑S.card =
          ↑(a'.clearingPow S) * ↑S.card by linarith)
      exact mul_right_cancel₀ hpos.ne' hmul
    refine Subtype.ext (funext fun i => ?_)
    by_cases hi : i ∈ S
    · have := heq i
      unfold numExp at this; rw [if_pos hi, if_pos hi, hcpS] at this
      have ha : 0 ≤ a.1 i + ↑(a'.clearingPow S) := by
        rw [← hcpS]; exact a.clearingPow_nonneg S i hi
      have ha' : 0 ≤ a'.1 i + ↑(a'.clearingPow S) := a'.clearingPow_nonneg S i hi
      omega
    · exact hout i hi

end LaurentExp

/-- Product of coordinate variable powers equals a monomial: `∏ Xᵢ^(g i) = monomial g̃ 1`
where `g̃ = Finsupp.equivFunOnFinite.symm g`. Extends `MvPolynomial.prod_X_pow_eq_monomial`
from the Finsupp support to all indices. -/
theorem prod_coord_pow_eq_monomial (g : Fin (n + 1) → ℕ) :
    (∏ i : Fin (n + 1), coord n R i ^ g i : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm g) 1 := by
  trans (∏ i ∈ (Finsupp.equivFunOnFinite.symm g).support,
      MvPolynomial.X i ^ (Finsupp.equivFunOnFinite.symm g) i : MvPolynomial _ R)
  · exact (Finset.prod_subset (Finset.subset_univ _)
      fun i _ hi => by
        have : g i = 0 := Finsupp.notMem_support_iff.mp hi
        rw [this, pow_zero]).symm
  · exact MvPolynomial.prod_X_pow_eq_monomial

/-- Coefficient of `numFinsupp a S` in the monomial numerator of `monomialElem a S`
is `1`. -/
theorem monomialElem_coeff_self (a : LaurentExp n) (S : Finset (Fin (n + 1))) :
    MvPolynomial.coeff (a.numFinsupp S)
      (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i :
        MvPolynomial (Fin (n + 1)) R) = 1 := by
  have h := prod_coord_pow_eq_monomial (R := R) (a.numExp S)
  rw [h, MvPolynomial.coeff_monomial]; exact if_pos rfl

/-- Coefficient of `numFinsupp a S` in the numerator of a different monomial element
is `0`. -/
theorem monomialElem_coeff_ne {a a' : LaurentExp n} {S : Finset (Fin (n + 1))}
    (hS : a.negSupport ⊆ S) (hS' : a'.negSupport ⊆ S) (hne : a ≠ a') :
    MvPolynomial.coeff (a.numFinsupp S)
      (∏ i : Fin (n + 1), coord n R i ^ a'.numExp S i :
        MvPolynomial (Fin (n + 1)) R) = 0 := by
  have h := prod_coord_pow_eq_monomial (R := R) (a'.numExp S)
  rw [h, MvPolynomial.coeff_monomial]
  exact if_neg (fun heq => hne (LaurentExp.numFinsupp_injective hS hS' heq.symm))

end CoefficientExtraction

/-! ### Quotient-level coefficient extraction -/

section QuotientExtraction

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

/-- The Finsupp assigning `N` to each index in `S` and `0` elsewhere.
This encodes the exponent vector of `(coordProd S)^N`. -/
def coordProdFinsupp (S : Finset (Fin (n + 1))) (N : ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.indicator S (fun _ _ => N)

@[simp]
theorem coordProdFinsupp_apply_mem {S : Finset (Fin (n + 1))} {i : Fin (n + 1)}
    (hi : i ∈ S) (N : ℕ) : coordProdFinsupp S N i = N :=
  Finsupp.indicator_of_mem hi _

@[simp]
theorem coordProdFinsupp_apply_notMem {S : Finset (Fin (n + 1))} {i : Fin (n + 1)}
    (hi : i ∉ S) (N : ℕ) : coordProdFinsupp S N i = 0 :=
  Finsupp.indicator_of_notMem hi _

@[simp]
theorem coordProdFinsupp_zero (S : Finset (Fin (n + 1))) :
    coordProdFinsupp S 0 = 0 := by
  ext i; simp [coordProdFinsupp, Finsupp.indicator_apply]

theorem coordProdFinsupp_add (S : Finset (Fin (n + 1))) (M N : ℕ) :
    coordProdFinsupp S (M + N) = coordProdFinsupp S M + coordProdFinsupp S N := by
  ext i; simp only [coordProdFinsupp, Finsupp.indicator_apply, Finsupp.coe_add,
    Pi.add_apply]; split_ifs <;> omega

/-- `(coordProd S)^N` equals the monomial with exponent `coordProdFinsupp S N`. -/
theorem coordProd_pow_eq_monomial (S : Finset (Fin (n + 1))) (N : ℕ) :
    (coordProd n R S) ^ N =
      MvPolynomial.monomial (coordProdFinsupp S N) (1 : R) := by
  rw [coordProd, ← Finset.prod_pow,
    show ∏ i ∈ S, coord n R i ^ N =
        ∏ i ∈ S, coord n R i ^ (coordProdFinsupp S N i) from
      Finset.prod_congr rfl fun i hi => by rw [coordProdFinsupp_apply_mem hi],
    show ∏ i ∈ S, coord n R i ^ (coordProdFinsupp S N i) =
        ∏ i : Fin (n + 1), coord n R i ^ (coordProdFinsupp S N i) from
      Finset.prod_subset (Finset.subset_univ S) fun i _ hi => by
        rw [coordProdFinsupp_apply_notMem hi, pow_zero],
    prod_coord_pow_eq_monomial,
    show Finsupp.equivFunOnFinite.symm (fun i => coordProdFinsupp S N i) =
        coordProdFinsupp S N from Finsupp.ext fun i => rfl]

/-- Shifting lemma: multiplying by `(coordProd S)^K` shifts coefficient extraction. -/
theorem coeff_coordProd_pow_mul (S : Finset (Fin (n + 1))) (K : ℕ)
    (m : Fin (n + 1) →₀ ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.coeff (coordProdFinsupp S K + m) ((coordProd n R S) ^ K * p) =
      MvPolynomial.coeff m p := by
  rw [coordProd_pow_eq_monomial, MvPolynomial.coeff_monomial_mul, one_mul]

/-- If two powers of `coordProd S` agree, coefficient extraction gives the same result. -/
theorem coeff_coordProdFinsupp_eq_of_pow_eq (S : Finset (Fin (n + 1))) {M N : ℕ}
    (h : (coordProd n R S) ^ M = (coordProd n R S) ^ N)
    (x : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.coeff (coordProdFinsupp S M) x =
      MvPolynomial.coeff (coordProdFinsupp S N) x := by
  have heq : (coordProd n R S) ^ M * x = (coordProd n R S) ^ N * x := by rw [h]
  have h1 := coeff_coordProd_pow_mul (R := R) S M (coordProdFinsupp S N) x
  have h2 := coeff_coordProd_pow_mul (R := R) S N (coordProdFinsupp S M) x
  have hcomm : coordProdFinsupp S M + coordProdFinsupp S N =
      coordProdFinsupp S N + coordProdFinsupp S M := add_comm _ _
  rw [hcomm, heq] at h1
  exact h2.symm.trans h1

/-- Zero-exponent coefficient extraction from a localization element.
For `a / (coordProd S)^N`, this extracts `MvPolynomial.coeff (coordProdFinsupp S N) a`.
Well-definedness follows from the shifting lemma: multiplying numerator and denominator
by the same power of `coordProd S` does not change the extracted coefficient. -/
def zeroExpCoeff (S : Finset (Fin (n + 1))) :
    HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S) → R :=
  fun x => (HomogeneousLocalization.val x).liftOn
    (fun (a : MvPolynomial (Fin (n + 1)) R)
        (s : Submonoid.powers (coordProd n R S)) =>
      MvPolynomial.coeff (coordProdFinsupp S s.2.choose) a)
    fun {a c} {b d} hrel => by
      show MvPolynomial.coeff (coordProdFinsupp S b.2.choose) a =
        MvPolynomial.coeff (coordProdFinsupp S d.2.choose) c
      rw [Localization.r_iff_exists] at hrel
      obtain ⟨⟨e, he⟩, heq⟩ := hrel
      set K := he.choose; set Nb := b.2.choose; set Nd := d.2.choose
      -- Rewrite the localization relation in terms of coordProd powers
      have key1 : e * (↑d * a) = (coordProd n R S) ^ (K + Nd) * a := by
        rw [pow_add, mul_assoc, ← he.choose_spec, ← d.2.choose_spec]
      have key2 : e * (↑b * c) = (coordProd n R S) ^ (K + Nb) * c := by
        rw [pow_add, mul_assoc, ← he.choose_spec, ← b.2.choose_spec]
      have heq' : (coordProd n R S) ^ (K + Nd) * a =
          (coordProd n R S) ^ (K + Nb) * c := key1.symm.trans (heq.trans key2)
      -- Apply shifting lemma to both sides
      have h1 := coeff_coordProd_pow_mul (R := R) S (K + Nd)
        (coordProdFinsupp S Nb) a
      have h2 := coeff_coordProd_pow_mul (R := R) S (K + Nb)
        (coordProdFinsupp S Nd) c
      -- The Finsupp indices are equal after rearranging
      have hindex : coordProdFinsupp S (K + Nd) + coordProdFinsupp S Nb =
          coordProdFinsupp S (K + Nb) + coordProdFinsupp S Nd := by
        rw [← coordProdFinsupp_add, ← coordProdFinsupp_add]; congr 1; omega
      rw [hindex, heq'] at h1
      exact h1.symm.trans h2

/-- Computation rule: `zeroExpCoeff` on `monomialElem` extracts the coefficient of
the appropriate monomial in the numerator polynomial. -/
theorem zeroExpCoeff_monomialElem (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    zeroExpCoeff (R := R) S (monomialElem a S hS) =
      MvPolynomial.coeff (coordProdFinsupp S (a.clearingPow S))
        (∏ i : Fin (n + 1), coord n R i ^ a.numExp S i) := by
  unfold zeroExpCoeff monomialElem
  simp only [HomogeneousLocalization.Away.val_mk, Localization.liftOn_mk]
  apply coeff_coordProdFinsupp_eq_of_pow_eq (R := R)
  exact Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _

/-- `zeroExpCoeff` of the zero-exponent monomial is `1`. -/
theorem zeroExpCoeff_monomialElem_zero (S : Finset (Fin (n + 1))) :
    zeroExpCoeff (R := R) S (monomialElem (0 : LaurentExp n) S
      (by simp [LaurentExp.negSupport_zero])) = 1 := by
  rw [zeroExpCoeff_monomialElem]
  have hval : (0 : LaurentExp n).1 = (0 : Fin (n + 1) → ℤ) := rfl
  have hcp : (0 : LaurentExp n).clearingPow S = 0 := by
    simp only [LaurentExp.clearingPow, hval, Pi.zero_apply, neg_zero, Int.toNat_zero]
    exact (Finset.sup_eq_bot_iff _ S).mpr (fun _ _ => rfl)
  have hne : ∀ i, (0 : LaurentExp n).numExp S i = 0 := by
    intro i
    simp only [LaurentExp.numExp, hval, Pi.zero_apply, Int.toNat_zero, hcp,
      Nat.cast_zero, add_zero, ite_self]
  simp_rw [hcp, coordProdFinsupp_zero, hne, pow_zero, Finset.prod_const_one,
    MvPolynomial.coeff_zero_one]

/-- If `coordProdFinsupp S (clearingPow a S) = numFinsupp a S`, then `a = 0`. -/
private theorem numFinsupp_eq_coordProdFinsupp_imp_zero {a : LaurentExp n}
    {S : Finset (Fin (n + 1))} (hS : a.negSupport ⊆ S)
    (h : a.numFinsupp S = coordProdFinsupp S (a.clearingPow S)) : a = 0 := by
  refine Subtype.ext (funext fun i => show a.1 i = 0 from ?_)
  have hi := DFunLike.congr_fun h i
  by_cases hiS : i ∈ S
  · simp only [LaurentExp.numFinsupp_apply, LaurentExp.numExp, if_pos hiS,
      coordProdFinsupp_apply_mem hiS] at hi
    have hnn := a.clearingPow_nonneg S i hiS
    omega
  · simp only [LaurentExp.numFinsupp_apply, LaurentExp.numExp, if_neg hiS,
      coordProdFinsupp_apply_notMem hiS] at hi
    have hnn : 0 ≤ a.1 i := (a.not_mem_negSupport_iff i).mp (fun hm => hiS (hS hm))
    omega

/-- `zeroExpCoeff` of a nonzero-exponent monomial is `0`. -/
theorem zeroExpCoeff_monomialElem_ne (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) (ha : a ≠ 0) :
    zeroExpCoeff (R := R) S (monomialElem a S hS) = 0 := by
  rw [zeroExpCoeff_monomialElem, prod_coord_pow_eq_monomial, MvPolynomial.coeff_monomial]
  refine if_neg (fun h => ha ?_)
  exact numFinsupp_eq_coordProdFinsupp_imp_zero hS h

end QuotientExtraction

/-! ### Additivity of zero-exponent coefficient extraction -/

section ZeroExpCoeffAdditivity

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

/-- `zeroExpCoeff` commutes with addition. The proof reduces to the Localization
addition formula `mk a s + mk b t = mk (t*a + s*b) (s*t)` and the shifting lemma. -/
private theorem zeroExpCoeff_add (S : Finset (Fin (n + 1)))
    (x y : HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) :
    zeroExpCoeff S (x + y) = zeroExpCoeff S x + zeroExpCoeff S y := by
  -- Reduce to representatives via HomogeneousLocalization val
  have hval_add := HomogeneousLocalization.val_add x y
  unfold zeroExpCoeff
  rw [hval_add]
  -- Induct on localization representatives
  refine Localization.induction_on₂ (HomogeneousLocalization.val x)
    (HomogeneousLocalization.val y) fun ⟨a, s⟩ ⟨c, t⟩ => ?_
  -- Unfold liftOn on mk and add_mk
  rw [Localization.add_mk, Localization.liftOn_mk, Localization.liftOn_mk,
    Localization.liftOn_mk]
  -- Simplify pair projections
  dsimp only [Prod.fst, Prod.snd]
  set Ns := s.2.choose with hNs_def; set Nt := t.2.choose with hNt_def
  set Nst := (s * t).2.choose with hNst_def
  rw [MvPolynomial.coeff_add]
  -- Extract power specifications with clean types
  have hs_spec : (coordProd n R S) ^ Ns = ↑s := s.2.choose_spec
  have ht_spec : (coordProd n R S) ^ Nt = ↑t := t.2.choose_spec
  have hst_spec : (coordProd n R S) ^ Nst = ↑(s * t) := (s * t).2.choose_spec
  -- f^Nst = s*t = f^Ns * f^Nt = f^(Ns+Nt)
  have hpow : (coordProd n R S) ^ Nst = (coordProd n R S) ^ (Ns + Nt) := by
    rw [hst_spec, Submonoid.coe_mul, ← hs_spec, ← ht_spec, ← pow_add]
  -- Apply coeff_coordProdFinsupp_eq_of_pow_eq to normalize the power
  rw [coeff_coordProdFinsupp_eq_of_pow_eq (R := R) S hpow (↑t * a),
    coeff_coordProdFinsupp_eq_of_pow_eq (R := R) S hpow (↑s * c)]
  -- Now: coeff(cPF S (Ns+Nt))(↑t * a) + coeff(cPF S (Ns+Nt))(↑s * c)
  -- ↑t = f^Nt, ↑s = f^Ns
  rw [show (↑t : MvPolynomial (Fin (n + 1)) R) = (coordProd n R S) ^ Nt from
    ht_spec.symm,
    show (↑s : MvPolynomial (Fin (n + 1)) R) = (coordProd n R S) ^ Ns from
    hs_spec.symm]
  -- Use the shifting lemma
  have h1 := coeff_coordProd_pow_mul (R := R) S Nt (coordProdFinsupp S Ns) a
  have h2 := coeff_coordProd_pow_mul (R := R) S Ns (coordProdFinsupp S Nt) c
  rw [← coordProdFinsupp_add] at h1 h2
  rw [show Nt + Ns = Ns + Nt from by omega] at h1
  rw [h1, h2, add_comm]

/-- `zeroExpCoeff` as an `AddMonoidHom`. -/
def zeroExpCoeffHom (S : Finset (Fin (n + 1))) :
    HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S) →+ R where
  toFun := zeroExpCoeff S
  map_zero' := by
    show zeroExpCoeff S 0 = 0
    unfold zeroExpCoeff
    rw [HomogeneousLocalization.val_zero]
    -- 0 in Localization is mk 0 1
    change (0 : Localization (Submonoid.powers (coordProd n R S))).liftOn _ _ = 0
    rw [show (0 : Localization (Submonoid.powers (coordProd n R S))) =
      Localization.mk 0 1 from (Localization.mk_zero 1).symm, Localization.liftOn_mk]
    exact MvPolynomial.coeff_zero _
  map_add' := zeroExpCoeff_add S

/-- The module version: extracts the zero-exponent coefficient from the module
localization by composing with `awayRingModuleEquiv.symm`. -/
def zeroExpCoeffMod (S : Finset (Fin (n + 1))) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S) →+ R :=
  (zeroExpCoeffHom S).comp (awayRingModuleEquiv (𝒜 n R)).symm.toAddMonoidHom

/-- `zeroExpCoeffMod S` on a representative `mk q` computes as a polynomial coefficient:
it extracts `coeff (coordProdFinsupp S N) (q.num)` where `N = q.den_mem.choose`. -/
private theorem zeroExpCoeffMod_mk (S : Finset (Fin (n + 1)))
    (q : HomogeneousLocalizedModule.NumDenSameDeg (𝒜 n R) (𝒜 n R)
      (Submonoid.powers (coordProd n R S))) :
    zeroExpCoeffMod S (HomogeneousLocalizedModule.mk q) =
    MvPolynomial.coeff (coordProdFinsupp S q.den_mem.choose)
      (q.num : MvPolynomial (Fin (n + 1)) R) := rfl

/-! #### Face-preservation for zero-exponent extraction -/

/-- Decomposition of `coordProdFinsupp` over insertion: for `k ∉ S`,
`coordProdFinsupp (insert k S) N = Finsupp.single k N + coordProdFinsupp S N`. -/
theorem coordProdFinsupp_insert {S : Finset (Fin (n + 1))} {k : Fin (n + 1)}
    (hk : k ∉ S) (N : ℕ) :
    coordProdFinsupp (insert k S) N = Finsupp.single k N + coordProdFinsupp S N := by
  ext i
  simp only [coordProdFinsupp, Finsupp.indicator_apply, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply, Finset.mem_insert]
  by_cases hik : i = k
  · subst hik; simp [hk]
  · simp only [hik, false_or, if_neg (Ne.symm hik)]; omega

/-- Face-preservation: `zeroExpCoeffMod` commutes with `coordRestrict`.
Extracting the zero-exponent coefficient after face restriction gives the same
result as extracting before restriction. This is the key property that makes
`zeroExpCoeffMod` define a chain map. -/
theorem zeroExpCoeffMod_coordRestrict {p : ℕ}
    {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R)
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    zeroExpCoeffMod (R := R) T
      (coordRestrict n R (𝒜 n R) T hT j x) =
    zeroExpCoeffMod (R := R) (TopCat.eraseNth T hT j).1 x := by
  -- Reduce to a representative of the module quotient
  refine Quotient.inductionOn x fun q => ?_
  -- Now the goal has ⟦q⟧ in place of x
  -- Both sides reduce definitionally to polynomial coefficient computations
  -- LHS: coeff (coordProdFinsupp T M) ((coord k)^N * q.num) where M = Classical.choose
  -- RHS: coeff (coordProdFinsupp face N) q.num where N = q.den_mem.choose
  -- Rewrite RHS to polynomial coefficient form
  rw [show zeroExpCoeffMod (R := R) (TopCat.eraseNth T hT j).1 ⟦q⟧ =
    MvPolynomial.coeff (coordProdFinsupp (TopCat.eraseNth T hT j).1 q.den_mem.choose)
      (q.num : MvPolynomial (Fin (n + 1)) R) from rfl]
  -- LHS definitionally equals: coeff (cpf T M) ((coord k)^N • q.num)
  -- RHS (already rewritten): coeff (cpf face N) q.num
  -- Strategy: show LHS = coeff(cpf T N)((coord k)^N * q.num) = RHS
  -- Extract N to break syntactic dependency on T for rewrites
  set N := q.den_mem.choose with hN_def
  have hk_notmem : TopCat.nthElem T hT j ∉ (TopCat.eraseNth T hT j).1 :=
    Finset.notMem_erase _ T
  have hT_eq : T = insert (TopCat.nthElem T hT j) (TopCat.eraseNth T hT j).1 :=
    (Finset.insert_erase (TopCat.nthElem_mem T hT j)).symm
  -- Part 2: polynomial shifting identity
  have poly_shift :
      MvPolynomial.coeff (coordProdFinsupp T N)
        ((coord n R (TopCat.nthElem T hT j)) ^ N *
          (q.num : MvPolynomial (Fin (n + 1)) R)) =
      MvPolynomial.coeff (coordProdFinsupp (TopCat.eraseNth T hT j).1 N)
        (q.num : MvPolynomial (Fin (n + 1)) R) := by
    -- Rewrite coordProdFinsupp T N = single k N + coordProdFinsupp face N
    -- N is a local variable (via set), so conv_lhs avoids dependent type issues
    have hcpf : coordProdFinsupp T N =
        Finsupp.single (TopCat.nthElem T hT j) N +
        coordProdFinsupp (TopCat.eraseNth T hT j).1 N := by
      conv_lhs => rw [hT_eq]
      exact coordProdFinsupp_insert hk_notmem N
    rw [hcpf, coord, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_monomial_mul, one_mul]
  -- Split via trans to avoid motive issues with rw
  trans MvPolynomial.coeff (coordProdFinsupp T N)
    ((coord n R (TopCat.nthElem T hT j)) ^ N *
      (q.num : MvPolynomial (Fin (n + 1)) R))
  · -- Part 1: LHS = coeff(cpf T N)((coord k)^N * q.num)
    -- The LHS definitionally reduces to coeff(cpf T M)((coord k)^N • q.num)
    -- where M = Classical.choose on an intermediate den_mem.
    -- We resolve the Classical.choose opacity via coeff_coordProdFinsupp_eq_of_pow_eq.
    -- Step 1: Compute (coordProd T)^N = q.den * (coord k)^N
    have hpow_eq : (coordProd n R T) ^ N =
        (q.den : MvPolynomial (Fin (n + 1)) R) *
          (coord n R (TopCat.nthElem T hT j)) ^ N := by
      have h1 : coordProd n R T = coordProd n R (TopCat.eraseNth T hT j).1 *
          coord n R (TopCat.nthElem T hT j) :=
        coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j)
      have h2 : (coordProd n R (TopCat.eraseNth T hT j).1) ^ N =
          (q.den : MvPolynomial (Fin (n + 1)) R) := q.den_mem.choose_spec
      simp only [h1, mul_pow, h2]
    -- Step 2: Use `show` (not `rw`) to expose the definitional reduction,
    -- avoiding dependent type motive issues with `T`.
    -- By proof irrelevance, the intermediate den_mem = ⟨N, hpow_eq⟩.
    show MvPolynomial.coeff
      (coordProdFinsupp T
        (⟨N, hpow_eq⟩ :
          (q.den : MvPolynomial (Fin (n + 1)) R) *
            (coord n R (TopCat.nthElem T hT j)) ^ N ∈
          Submonoid.powers (coordProd n R T)).choose)
      ((coord n R (TopCat.nthElem T hT j)) ^ N •
        (q.num : MvPolynomial (Fin (n + 1)) R)) =
      MvPolynomial.coeff (coordProdFinsupp T N)
        ((coord n R (TopCat.nthElem T hT j)) ^ N *
          (q.num : MvPolynomial (Fin (n + 1)) R))
    -- Step 3: Convert • to * and normalize Classical.choose power
    rw [smul_eq_mul]
    apply coeff_coordProdFinsupp_eq_of_pow_eq
    exact (⟨N, hpow_eq⟩ :
      (q.den : MvPolynomial (Fin (n + 1)) R) *
        (coord n R (TopCat.nthElem T hT j)) ^ N ∈
      Submonoid.powers (coordProd n R T)).choose_spec.trans hpow_eq.symm
  · -- Part 2: polynomial shifting identity
    exact poly_shift

end ZeroExpCoeffAdditivity

/-! ### Extraction chain map and cohomology consequences -/

section CohomologyConsequences

variable {n : ℕ} {R : Type u} [CommRing R]

attribute [local instance] mvPolynomialGrading

local instance : SetLike.GradedSMul (𝒜 n R) (𝒜 n R) :=
  SetLike.GradedMul.toGradedSMul _

/-- The degree-`p` extraction map: applies `zeroExpCoeffMod` at each subset `S` to
extract the zero-exponent coefficient from each localization. This sends a cochain of
the algebraic complex to a cochain of the relative simplex complex for `T = ∅`. -/
def extractionHom (p : ℕ) :
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1)) →+
    _root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R p where
  toFun := fun f ⟨S, hS, _⟩ => zeroExpCoeffMod S (f ⟨S, hS⟩)
  map_zero' := by ext ⟨S, hS, _⟩; simp [map_zero]
  map_add' _ _ := by ext ⟨S, hS, _⟩; simp [Pi.add_apply, map_add]

/-- The extraction map commutes with the differentials:
`extractionHom(p+1)(algebraicδ(f)) = relSimplexδ(extractionHom(p)(f))`.
This is the chain map property, following from `zeroExpCoeffMod_coordRestrict`. -/
theorem extraction_comm_δ (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1)) :
    extractionHom (p + 1) (algebraicδ n R (𝒜 n R) p f) =
    _root_.relSimplexδHom (∅ : Finset (Fin (n + 1))) R p (extractionHom p f) := by
  ext ⟨T, hT, _⟩
  -- LHS: zeroExpCoeffMod T (∑_j (-1)^j • coordRestrict(f(face_j)))
  -- RHS: ∑_j (-1)^j • zeroExpCoeffMod (face_j) (f(face_j))
  simp only [extractionHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    algebraicδ, _root_.relSimplexδHom, _root_.relSimplexδ_apply,
    dif_pos (Finset.empty_subset _)]
  rw [map_sum]
  congr 1; ext j
  rw [map_zsmul]
  congr 1
  exact zeroExpCoeffMod_coordRestrict hT j (f (TopCat.eraseNth T hT j))

/-- The extraction chain map from the structure-sheaf algebraic complex to the
relative simplex complex `K_∅`. -/
noncomputable def extractionChainMap :
    algebraicComplex n R (𝒜 n R) ⟶
    _root_.relSimplexComplex (∅ : Finset (Fin (n + 1))) R :=
  CochainComplex.ofHom
    (fun p => AddCommGrp.of (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1)))
    (fun p => AddCommGrp.ofHom (algebraicδ n R (𝒜 n R) p))
    (fun p => algebraicδ_comp_algebraicδ n R (𝒜 n R) p)
    (fun p => AddCommGrp.of (_root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R p))
    (fun p => AddCommGrp.ofHom (_root_.relSimplexδHom (∅ : Finset (Fin (n + 1))) R p))
    (fun p => AddCommGrp.ext (_root_.relSimplexδ_comp_eq_zero
      (∅ : Finset (Fin (n + 1))) R p))
    (fun p => AddCommGrp.ofHom (extractionHom p))
    (fun p => AddCommGrp.ext (fun f => (extraction_comm_δ p f).symm))

end CohomologyConsequences

end AlgebraicGeometry.Proj
