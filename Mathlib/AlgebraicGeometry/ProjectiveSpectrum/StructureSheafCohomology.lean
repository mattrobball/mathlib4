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

open MvPolynomial CategoryTheory CategoryTheory.Limits Finset

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

/-! ### Embedding chain map K_∅ → algebraicComplex -/

section EmbeddingChainMap

/-- The constant element embedding into the ring localization: sends `r : R` to the
element `C(r)/1` in the degree-zero ring localization at `coordProd S`. -/
def constRingElemHom (S : Finset (Fin (n + 1))) :
    R →+ HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S) where
  toFun r := HomogeneousLocalization.Away.mk (𝒜 n R)
    (coordProd_mem_homogeneous n R S) 0 (MvPolynomial.C r)
    (by simpa using MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_zero]
  map_add' r s := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add]
    simp only [HomogeneousLocalization.Away.val_mk, map_add, Localization.add_mk]
    congr 1
    · ring
    · simp [Submonoid.mk_mul_mk]

/-- The constant element embedding into the module localization: sends `r : R` to
`C(r)/1` in the degree-zero module localization at `coordProd S`, by composing
the ring embedding with the ring-module equivalence. -/
def constModElemHom (S : Finset (Fin (n + 1))) :
    R →+ HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S) :=
  (awayRingModuleEquiv (𝒜 n R)).toAddMonoidHom.comp (constRingElemHom S)

/-- Face restriction preserves constant elements: restricting `C(r)/1` from a face
to the full simplex yields `C(r)/1` at the full simplex. -/
theorem coordRestrict_constModElem {p : ℕ} {T : Finset (Fin (n + 1))}
    (hT : T.card = p + 2) (j : Fin (p + 2)) (r : R) :
    coordRestrict n R (𝒜 n R) T hT j (constModElemHom (TopCat.eraseNth T hT j).1 r) =
    constModElemHom T r := by
  -- Both sides are elements of the module localization at T
  -- LHS: coordRestrict (awayRingModuleEquiv (mk 0 (C r)))
  -- RHS: awayRingModuleEquiv (mk 0 (C r))
  -- Use val_injective at the LocalizedModule level
  apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R T))
  -- LHS val: by awayMap_Away_mk, gives LocalizedModule.mk (g^0 • C r) ⟨x^0, ...⟩
  -- RHS val: LocalizedModule.mk (C r) ⟨(coordProd T)^0, ...⟩
  -- These are equal since g^0 • C r = 1 • C r = C r
  simp only [constModElemHom, AddMonoidHom.coe_comp, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, Function.comp_apply, constRingElemHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, coordRestrict]
  erw [HomogeneousLocalizedModule.awayMap_Away_mk]
  case hf => exact coordProd_mem_homogeneous n R _
  simp only [HomogeneousLocalizedModule.Away.val_mk, pow_zero, one_smul]
  rfl

/-- The degree-`p` embedding map: sends each cochain value `r` to `C(r)/1` in the
module localization. -/
def embeddingHom (p : ℕ) :
    _root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R p →+
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1)) :=
  Pi.addMonoidHom fun ⟨S, hS⟩ =>
    (constModElemHom S).comp
      (Pi.evalAddMonoidHom _ ⟨S, hS, Finset.empty_subset S⟩)

/-- The embedding commutes with the differentials:
`algebraicδ(embeddingHom(f)) = embeddingHom(relSimplexδ(f))`. -/
theorem embedding_comm_δ (p : ℕ)
    (f : _root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R p) :
    algebraicδ n R (𝒜 n R) p (embeddingHom p f) =
    embeddingHom (p + 1) (_root_.relSimplexδHom (∅ : Finset (Fin (n + 1))) R p f) := by
  ext ⟨T, hT⟩
  simp only [algebraicδ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, embeddingHom,
    Pi.addMonoidHom_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    Pi.evalAddMonoidHom_apply]
  simp only [_root_.relSimplexδHom, _root_.relSimplexδ_apply, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, dif_pos (Finset.empty_subset _), map_sum, map_zsmul]
  simp_rw [coordRestrict_constModElem hT]

/-- The embedding chain map from `K_∅` to the algebraic complex: a section of the
extraction chain map. -/
noncomputable def embeddingChainMap :
    _root_.relSimplexComplex (∅ : Finset (Fin (n + 1))) R ⟶
    algebraicComplex n R (𝒜 n R) :=
  CochainComplex.ofHom
    (fun p => AddCommGrp.of
      (_root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R p))
    (fun p => AddCommGrp.ofHom
      (_root_.relSimplexδHom (∅ : Finset (Fin (n + 1))) R p))
    (fun p => AddCommGrp.ext
      (_root_.relSimplexδ_comp_eq_zero (∅ : Finset (Fin (n + 1))) R p))
    (fun p => AddCommGrp.of (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1)))
    (fun p => AddCommGrp.ofHom (algebraicδ n R (𝒜 n R) p))
    (fun p => algebraicδ_comp_algebraicδ n R (𝒜 n R) p)
    (fun p => AddCommGrp.ofHom (embeddingHom p))
    (fun p => AddCommGrp.ext (fun f => embedding_comm_δ p f))

/-- Zero-exponent extraction of a constant element gives back the original value:
`zeroExpCoeffMod S (C(r)/1) = r`. -/
theorem zeroExpCoeffMod_constModElem (S : Finset (Fin (n + 1))) (r : R) :
    zeroExpCoeffMod (R := R) S (constModElemHom S r) = r := by
  -- constModElemHom = awayRingModuleEquiv ∘ constRingElemHom
  -- zeroExpCoeffMod = zeroExpCoeffHom ∘ awayRingModuleEquiv.symm
  -- So zeroExpCoeffMod (constModElemHom r) = zeroExpCoeffHom (constRingElemHom r)
  show zeroExpCoeffMod S ((awayRingModuleEquiv (𝒜 n R)) (constRingElemHom S r)) = r
  simp only [zeroExpCoeffMod, AddMonoidHom.coe_comp, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, Function.comp_apply, AddEquiv.symm_apply_apply]
  -- Now: zeroExpCoeffHom S (constRingElemHom S r) = r
  -- = zeroExpCoeff S (mk 0 (C r) _) = coeff (cpf S N) (C r) where N = choose
  -- Normalize N to 0 via coeff_coordProdFinsupp_eq_of_pow_eq, then coeff 0 (C r) = r
  simp only [zeroExpCoeffHom, constRingElemHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  unfold zeroExpCoeff
  rw [HomogeneousLocalization.Away.val_mk, Localization.liftOn_mk]
  apply (coeff_coordProdFinsupp_eq_of_pow_eq (R := R) S
    (Exists.choose_spec (p := fun m => _ ^ m = _ ^ _) _) (MvPolynomial.C r)).trans
  simp [coordProdFinsupp_zero, MvPolynomial.coeff_C]

/-- Extraction after embedding is the identity: `extractionHom ∘ embeddingHom = id`. -/
theorem extraction_embedding_eq (p : ℕ)
    (f : _root_.relSimplexCochain (∅ : Finset (Fin (n + 1))) R p) :
    extractionHom p (embeddingHom p f) = f := by
  ext ⟨S, hS, _⟩
  simp only [extractionHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, embeddingHom,
    Pi.addMonoidHom_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    Pi.evalAddMonoidHom_apply]
  exact zeroExpCoeffMod_constModElem S (f ⟨S, hS, Finset.empty_subset S⟩)

/-- The extraction chain map after the embedding chain map is the identity. -/
theorem extraction_embedding_eq_id :
    embeddingChainMap ≫ extractionChainMap = 𝟙
      (_root_.relSimplexComplex (∅ : Finset (Fin (n + 1))) R) := by
  ext p : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    embeddingChainMap, extractionChainMap, CochainComplex.ofHom_f]
  ext f
  exact extraction_embedding_eq p f

end EmbeddingChainMap

/-! ### Monomial coefficient extraction: additivity and chain maps -/

section MonomialCoeffChainMap

/-- `monomialCoeff` commutes with addition. The proof follows the same pattern
as `zeroExpCoeff_add`, with an extra `clearingPow` multiplication. -/
private theorem monomialCoeff_add (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S)
    (x y : HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) :
    monomialCoeff a S hS (x + y) =
    monomialCoeff a S hS x + monomialCoeff a S hS y := by
  have hval_add := HomogeneousLocalization.val_add x y
  unfold monomialCoeff
  rw [hval_add]
  refine Localization.induction_on₂ (HomogeneousLocalization.val x)
    (HomogeneousLocalization.val y) fun ⟨p, s⟩ ⟨c, t⟩ => ?_
  rw [Localization.add_mk, Localization.liftOn_mk, Localization.liftOn_mk,
    Localization.liftOn_mk]
  dsimp only [Prod.fst, Prod.snd]
  set nf := a.numFinsupp S
  set cp := (coordProd n R S) ^ a.clearingPow S
  set Ns := s.2.choose; set Nt := t.2.choose; set Nst := (s * t).2.choose
  rw [mul_add, MvPolynomial.coeff_add]
  have hs_spec : (coordProd n R S) ^ Ns = ↑s := s.2.choose_spec
  have ht_spec : (coordProd n R S) ^ Nt = ↑t := t.2.choose_spec
  have hst_spec : (coordProd n R S) ^ Nst = ↑(s * t) := (s * t).2.choose_spec
  have hpow : (coordProd n R S) ^ Nst = (coordProd n R S) ^ (Ns + Nt) := by
    rw [hst_spec, Submonoid.coe_mul, ← hs_spec, ← ht_spec, ← pow_add]
  rw [coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S nf hpow (cp * (↑t * p)),
    coeff_shift_coordProdFinsupp_eq_of_pow_eq (R := R) S nf hpow (cp * (↑s * c))]
  rw [show (↑t : MvPolynomial _ R) = (coordProd n R S) ^ Nt from ht_spec.symm,
    show (↑s : MvPolynomial _ R) = (coordProd n R S) ^ Ns from hs_spec.symm]
  -- Use shifting: cp * (f^K * q) = f^K * (cp * q), then coeff_coordProd_pow_mul
  have hindex : ∀ a' b : ℕ,
      nf + coordProdFinsupp S (a' + b) =
      coordProdFinsupp S a' + (nf + coordProdFinsupp S b) := by
    intro a' b; ext i; by_cases hi : i ∈ S
    · simp [coordProdFinsupp_apply_mem hi]; ring
    · simp [coordProdFinsupp_apply_notMem hi]
  have h1 : MvPolynomial.coeff (nf + coordProdFinsupp S (Ns + Nt))
      (cp * ((coordProd n R S) ^ Ns * c)) =
    MvPolynomial.coeff (nf + coordProdFinsupp S Nt) (cp * c) := by
    rw [hindex Ns Nt, show cp * ((coordProd n R S) ^ Ns * c) =
        (coordProd n R S) ^ Ns * (cp * c) from by ring]
    exact coeff_coordProd_pow_mul _ _ _ _
  have h2 : MvPolynomial.coeff (nf + coordProdFinsupp S (Ns + Nt))
      (cp * ((coordProd n R S) ^ Nt * p)) =
    MvPolynomial.coeff (nf + coordProdFinsupp S Ns) (cp * p) := by
    rw [show Ns + Nt = Nt + Ns from by omega, hindex Nt Ns,
      show cp * ((coordProd n R S) ^ Nt * p) =
        (coordProd n R S) ^ Nt * (cp * p) from by ring]
    exact coeff_coordProd_pow_mul _ _ _ _
  rw [h1, h2, add_comm]

/-- `monomialCoeff` as an `AddMonoidHom`. -/
def monomialCoeffHom (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S) →+ R where
  toFun := monomialCoeff a S hS
  map_zero' := by
    show monomialCoeff a S hS 0 = 0
    unfold monomialCoeff
    rw [HomogeneousLocalization.val_zero]
    change (0 : Localization (Submonoid.powers (coordProd n R S))).liftOn _ _ = 0
    rw [show (0 : Localization (Submonoid.powers (coordProd n R S))) =
      Localization.mk 0 1 from (Localization.mk_zero 1).symm, Localization.liftOn_mk]
    simp [mul_zero, MvPolynomial.coeff_zero]
  map_add' := monomialCoeff_add a S hS

/-- The module version of `monomialCoeff`: extracts the `a`-monomial coefficient
from the module localization by composing with `awayRingModuleEquiv.symm`. -/
def monomialCoeffMod (a : LaurentExp n) (S : Finset (Fin (n + 1)))
    (hS : a.negSupport ⊆ S) :
    HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S) →+ R :=
  (monomialCoeffHom a S hS).comp (awayRingModuleEquiv (𝒜 n R)).symm.toAddMonoidHom

/-- `monomialCoeffMod 0` reduces to `zeroExpCoeffMod`. -/
theorem monomialCoeffMod_eq_zeroExpCoeffMod (S : Finset (Fin (n + 1))) :
    monomialCoeffMod (0 : LaurentExp n) S
      (by simp [LaurentExp.negSupport_zero]) =
    zeroExpCoeffMod (R := R) S := by
  ext x
  simp only [monomialCoeffMod, monomialCoeffHom, zeroExpCoeffMod, zeroExpCoeffHom,
    AddMonoidHom.coe_comp, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    Function.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact congr_fun (monomialCoeff_eq_zeroExpCoeff S) _

/-- Face preservation for `monomialCoeffMod`: extracting after face restriction
gives the same result as extracting at the face, when the negative support is
contained in the face. -/
theorem monomialCoeffMod_coordRestrict (a : LaurentExp n)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2)) (hfull : a.negSupport ⊆ T)
    (hface : a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R)
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeffMod a T hfull
      (coordRestrict n R (𝒜 n R) T hT j x) =
    monomialCoeffMod a (TopCat.eraseNth T hT j).1 hface x := by
  -- Revert face-dependent variables, set abbreviations, then reintroduce.
  -- This avoids the `set face` renaming issue where `q` becomes `q✝`.
  revert hface x
  set j_elem := TopCat.nthElem T hT j
  set face := (TopCat.eraseNth T hT j).1
  intro hface x
  refine Quotient.inductionOn x fun q => ?_
  -- Rewrite RHS to polynomial coefficient form
  rw [show monomialCoeffMod a face hface ⟦q⟧ =
    MvPolynomial.coeff
      (a.numFinsupp face + coordProdFinsupp face q.den_mem.choose)
      ((coordProd n R face) ^ a.clearingPow face *
        (q.num : MvPolynomial (Fin (n + 1)) R)) from by
    simp only [monomialCoeffMod, monomialCoeffHom, AddMonoidHom.coe_comp,
      AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Function.comp_apply,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, monomialCoeff]
    rfl]
  -- set N (OK since q's type doesn't involve N)
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
  rw [hcp_eq]
  -- Step 1: Polynomial shifting identity
  -- (coord j_elem)^(cp+N) * ((coordProd face)^cp * q.num) gives the right coefficient
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
  -- nf(a,T) + cpf(T,N) = single(j_elem, cp+N) + (nf(a,face) + cpf(face,N))
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
      -- Normalize to use face/j_elem/cp abbreviations for omega
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
  -- (coordProd T)^cp * (coord j_elem)^N = (coord j_elem)^(cp+N) * (coordProd face)^cp
  have hpoly :
      (coordProd n R T) ^ cp * (coord n R j_elem) ^ N =
      (coord n R j_elem) ^ (cp + N) * (coordProd n R face) ^ cp := by
    have h1 : coordProd n R T = coordProd n R face * coord n R j_elem :=
      coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j)
    rw [h1, mul_pow, mul_assoc, ← pow_add]; ring
  -- Combine: trans through the shifted polynomial
  trans MvPolynomial.coeff
    (Finsupp.single j_elem (cp + N) + (a.numFinsupp face + coordProdFinsupp face N))
    ((coord n R j_elem) ^ (cp + N) *
      ((coordProd n R face) ^ cp *
        (q.num : MvPolynomial (Fin (n + 1)) R)))
  · -- LHS = coeff at shifted index of shifted polynomial
    have hpow_eq : (coordProd n R T) ^ N =
        (q.den : MvPolynomial (Fin (n + 1)) R) *
          (coord n R j_elem) ^ N := by
      have h1 : coordProd n R T = coordProd n R face *
          coord n R j_elem :=
        coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j)
      have h2 : (coordProd n R face) ^ N =
          (q.den : MvPolynomial (Fin (n + 1)) R) := q.den_mem.choose_spec
      simp only [h1, mul_pow, h2]
    show MvPolynomial.coeff
      (a.numFinsupp T + coordProdFinsupp T
        (⟨N, hpow_eq⟩ :
          (q.den : MvPolynomial (Fin (n + 1)) R) *
            (coord n R j_elem) ^ N ∈
          Submonoid.powers (coordProd n R T)).choose)
      ((coordProd n R T) ^ cp *
        ((coord n R j_elem) ^ N •
          (q.num : MvPolynomial (Fin (n + 1)) R))) =
      MvPolynomial.coeff
        (Finsupp.single j_elem (cp + N) +
          (a.numFinsupp face + coordProdFinsupp face N))
        ((coord n R j_elem) ^ (cp + N) *
          ((coordProd n R face) ^ cp *
            (q.num : MvPolynomial (Fin (n + 1)) R)))
    rw [smul_eq_mul]
    -- Normalize the polynomial: (cP T)^cp * ((coord j)^N * q.num)
    --   = (coord j)^(cp+N) * ((cP face)^cp * q.num) via hpoly + reassociation
    have hpoly_ext : (coordProd n R T) ^ cp * ((coord n R j_elem) ^ N *
        (q.num : MvPolynomial (Fin (n + 1)) R)) =
      (coord n R j_elem) ^ (cp + N) * ((coordProd n R face) ^ cp *
        (q.num : MvPolynomial (Fin (n + 1)) R)) := by
      rw [← mul_assoc, hpoly, mul_assoc]
    rw [hpoly_ext, ← hindex]
    apply coeff_shift_coordProdFinsupp_eq_of_pow_eq
    exact (⟨N, hpow_eq⟩ :
      (q.den : MvPolynomial (Fin (n + 1)) R) *
        (coord n R j_elem) ^ N ∈
      Submonoid.powers (coordProd n R T)).choose_spec.trans hpow_eq.symm
  · -- RHS follows from poly_shift
    exact poly_shift

/-- Vanishing for `monomialCoeffMod` after face restriction: when the negative
support is NOT contained in the face, the monomial coefficient at `T` vanishes.
The key is that `coeff_monomial_mul'` returns `0` when the monomial exponent
exceeds the extraction index at the erased coordinate. -/
theorem monomialCoeffMod_coordRestrict_vanish (a : LaurentExp n)
    {p : ℕ} {T : Finset (Fin (n + 1))} (hT : T.card = p + 2)
    (j : Fin (p + 2)) (hfull : a.negSupport ⊆ T)
    (hface_neg : ¬a.negSupport ⊆ (TopCat.eraseNth T hT j).1)
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R)
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    monomialCoeffMod a T hfull
      (coordRestrict n R (𝒜 n R) T hT j x) = 0 := by
  -- Reduce to a representative
  refine Quotient.inductionOn x fun q => ?_
  -- Set abbreviations that DON'T rename q (avoid set face before trans)
  set j_elem := TopCat.nthElem T hT j
  set N := q.den_mem.choose
  set cp := a.clearingPow T
  -- j_elem is in the negative support: a.1 j_elem < 0
  have hj_neg : a.1 j_elem < 0 := by
    by_contra h
    push_neg at h
    exact hface_neg ((a.negSupport_subset_eraseNth_iff hT j hfull).mpr h)
  have hj_mem : j_elem ∈ T := TopCat.nthElem_mem T hT j
  -- Power identity for the denominator
  have hpow_eq : (coordProd n R T) ^ N =
      (q.den : MvPolynomial (Fin (n + 1)) R) *
        (coord n R j_elem) ^ N := by
    have h1 : coordProd n R T =
        coordProd n R (TopCat.eraseNth T hT j).1 * coord n R j_elem :=
      coordProd_eq_erase_mul n R T hj_mem
    have h2 : (coordProd n R (TopCat.eraseNth T hT j).1) ^ N =
        (q.den : MvPolynomial (Fin (n + 1)) R) := q.den_mem.choose_spec
    simp only [h1, mul_pow, h2]
  -- Reduce to a normalized coefficient via trans (before set face)
  trans MvPolynomial.coeff
    (a.numFinsupp T + coordProdFinsupp T N)
    ((coordProd n R T) ^ cp * ((coord n R j_elem) ^ N *
      (q.num : MvPolynomial (Fin (n + 1)) R)))
  · -- monomialCoeffMod (coordRestrict ⟦q⟧) = coeff (with choose) = coeff (with N)
    show MvPolynomial.coeff
      (a.numFinsupp T + coordProdFinsupp T
        (⟨N, hpow_eq⟩ :
          (q.den : MvPolynomial (Fin (n + 1)) R) *
            (coord n R j_elem) ^ N ∈
          Submonoid.powers (coordProd n R T)).choose)
      ((coordProd n R T) ^ cp *
        ((coord n R j_elem) ^ N •
          (q.num : MvPolynomial (Fin (n + 1)) R))) =
      MvPolynomial.coeff
        (a.numFinsupp T + coordProdFinsupp T N)
        ((coordProd n R T) ^ cp * ((coord n R j_elem) ^ N *
          (q.num : MvPolynomial (Fin (n + 1)) R)))
    rw [smul_eq_mul]
    apply coeff_shift_coordProdFinsupp_eq_of_pow_eq
    exact (⟨N, hpow_eq⟩ :
      (q.den : MvPolynomial (Fin (n + 1)) R) *
        (coord n R j_elem) ^ N ∈
      Submonoid.powers (coordProd n R T)).choose_spec.trans hpow_eq.symm
  · -- The coefficient vanishes: monomial exponent exceeds extraction index at j_elem
    -- Avoid `set face` which renames q to q✝
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
    have : (a.1 j_elem + ↑cp).toNat < cp := by
      suffices h : (↑((a.1 j_elem + ↑cp).toNat) : ℤ) < ↑cp by exact_mod_cast h
      rw [Int.toNat_of_nonneg hnn]; linarith
    omega

/-- The degree-`p` component extraction map: applies `monomialCoeffMod a` at each
subset `S` to extract the `a`-monomial coefficient from each localization. -/
def componentHom (a : LaurentExp n) (p : ℕ) :
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1)) →+
    _root_.relSimplexCochain (a.negSupport) R p where
  toFun f := fun ⟨S, hS, hns⟩ => monomialCoeffMod a S hns (f ⟨S, hS⟩)
  map_zero' := by ext ⟨S, hS, _⟩; simp [map_zero]
  map_add' _ _ := by ext ⟨S, hS, _⟩; simp [Pi.add_apply, map_add]

/-- The component extraction commutes with the differentials:
`componentHom(algebraicδ(f)) = relSimplexδ(componentHom(f))`. -/
theorem component_comm_δ (a : LaurentExp n) (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1)) :
    componentHom a (p + 1) (algebraicδ n R (𝒜 n R) p f) =
    _root_.relSimplexδHom a.negSupport R p (componentHom a p f) := by
  ext ⟨T, hT, hfull⟩
  simp only [componentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    algebraicδ, _root_.relSimplexδHom, _root_.relSimplexδ_apply]
  rw [map_sum]
  congr 1; ext j
  rw [map_zsmul]
  split_ifs with hface
  · congr 1; exact monomialCoeffMod_coordRestrict a hT j hfull hface _
  · rw [monomialCoeffMod_coordRestrict_vanish a hT j hfull hface _, smul_zero]

/-- The zero-exponent component extraction agrees with the extraction map pointwise. -/
theorem componentHom_zero_apply (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1))
    {S : Finset (Fin (n + 1))} (hS : S.card = p + 1)
    (hns : (0 : LaurentExp n).negSupport ⊆ S) :
    componentHom (0 : LaurentExp n) p f ⟨S, hS, hns⟩ =
    extractionHom p f ⟨S, hS, Finset.empty_subset S⟩ := by
  simp only [componentHom, extractionHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  show monomialCoeffMod 0 S _ (f ⟨S, hS⟩) = zeroExpCoeffMod S (f ⟨S, hS⟩)
  exact DFunLike.congr_fun (monomialCoeffMod_eq_zeroExpCoeffMod (R := R) S) _

end MonomialCoeffChainMap

/-! ### Injectivity of monomial coefficient extraction -/

section MonomialCoeffInjectivity

/-- If all monomial coefficients of a ring localization element are zero, the element
is zero. For each monomial in the numerator polynomial, one constructs a Laurent
exponent whose extraction recovers that specific polynomial coefficient. -/
theorem monomialCoeff_determines_zero (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S))
    (h : ∀ (a : LaurentExp n) (hS : a.negSupport ⊆ S),
      monomialCoeff a S hS x = 0) :
    x = 0 := by
  revert h; refine Quotient.inductionOn x fun q h => ?_
  -- Suffices to show the numerator polynomial is zero
  suffices hnum : (q.num : MvPolynomial (Fin (n + 1)) R) = 0 by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_zero]
    show HomogeneousLocalization.NumDenSameDeg.embedding _ _ q = 0
    simp only [HomogeneousLocalization.NumDenSameDeg.embedding, hnum,
      Localization.mk_zero]
  -- Proof by contradiction: if q.num ≠ 0, find a nonzero coefficient
  by_contra hne
  have hsup : (↑q.num : MvPolynomial (Fin (n + 1)) R).support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, ne_eq, MvPolynomial.support_eq_empty]
  obtain ⟨m, hm⟩ := hsup
  set N := q.den_mem.choose
  have hN_spec : (coordProd n R S) ^ N = (↑q.den : MvPolynomial _ R) :=
    q.den_mem.choose_spec
  -- q.deg = N * S.card: degree uniqueness for nonzero homogeneous polynomial
  have hdeg : q.deg = N * S.card := by
    by_cases hden : (↑q.den : MvPolynomial (Fin (n + 1)) R) = 0
    · -- coordProd^N = 0 forces R to be trivial, hence q.num = 0, contradiction
      exfalso; apply hne
      suffices Subsingleton R from Subsingleton.elim _ _
      rw [← not_nontrivial_iff_subsingleton]; intro
      exact absurd hden (by
        rw [← hN_spec, coordProd_pow_eq_monomial]
        exact (MvPolynomial.monomial_eq_zero.not.mpr one_ne_zero))
    · have hsup : (↑q.den : MvPolynomial (Fin (n + 1)) R).support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro heq; exact hden (MvPolynomial.support_eq_empty.mp heq)
      obtain ⟨m', hm'⟩ := hsup
      have hden_hom : (↑q.den : MvPolynomial (Fin (n + 1)) R).IsHomogeneous q.deg :=
        q.den.2
      have hcoord_hom : ((coordProd n R S) ^ N : MvPolynomial _ R).IsHomogeneous
          (N * S.card) := by rw [mul_comm]; exact (coordProd_mem_homogeneous n R S).pow N
      have h1 := hden_hom (Finsupp.mem_support_iff.mp hm')
      have h2 := (hN_spec ▸ hcoord_hom) (Finsupp.mem_support_iff.mp hm')
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at h1 h2
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1 h2; omega
  -- m ∈ support(q.num) implies ∑ m_i = q.deg = N * S.card
  have hm_deg : (∑ i, m i : ℕ) = N * S.card := by
    have hnum_hom : (↑q.num : MvPolynomial (Fin (n + 1)) R).IsHomogeneous q.deg :=
      q.num.2
    have := hnum_hom (Finsupp.mem_support_iff.mp hm)
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), hdeg] at this
  -- Construct the Laurent exponent from m and N
  have hm_intsum : (∑ i, (m i : ℤ) : ℤ) = (↑N : ℤ) * ↑S.card := by
    have h := congr_arg (Nat.cast (R := ℤ)) hm_deg; push_cast at h; exact h
  set a : LaurentExp n :=
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
  -- Index identity: nf a S + cpf S N = cpf S (cp a S) + m
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
  -- Coefficient computation: monomialCoeff extracts coeff m q.num
  have hcoeff : monomialCoeff a S hns ⟦q⟧ =
      MvPolynomial.coeff m (↑q.num : MvPolynomial _ R) := by
    show (HomogeneousLocalization.val ⟦q⟧).liftOn _ _ = _
    rw [show HomogeneousLocalization.val (⟦q⟧ :
        HomogeneousLocalization.Away (𝒜 n R) (coordProd n R S)) =
      Localization.mk (↑q.num) ⟨↑q.den, q.den_mem⟩ from rfl,
      Localization.liftOn_mk, hindex]
    exact coeff_coordProd_pow_mul S _ m _
  -- Contradiction: h says coefficient is 0, but m is in support
  exact absurd (hcoeff.symm.trans (h a hns)) (Finsupp.mem_support_iff.mp hm)

/-- Module version: if all monomial coefficients of a module localization element are
zero, the element is zero. Reduces to the ring version via `awayRingModuleEquiv`. -/
theorem monomialCoeffMod_determines_zero (S : Finset (Fin (n + 1)))
    (x : HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S))
    (h : ∀ (a : LaurentExp n) (hS : a.negSupport ⊆ S),
      monomialCoeffMod a S hS x = 0) :
    x = 0 := by
  have h' : (awayRingModuleEquiv (𝒜 n R)).symm x = 0 :=
    monomialCoeff_determines_zero S _ (fun a hS => h a hS)
  calc x = (awayRingModuleEquiv (𝒜 n R)) ((awayRingModuleEquiv (𝒜 n R)).symm x) :=
      ((awayRingModuleEquiv (𝒜 n R)).apply_symm_apply x).symm
    _ = 0 := by rw [h', map_zero]

end MonomialCoeffInjectivity

/-! ### H⁰ computation -/

section CohomologyH0

/-- A 0-cocycle in the algebraic complex with zero extraction is zero. Uses monomial
coefficient injectivity and acyclicity of `K_T` for nonempty proper `T`. -/
theorem algebraicCocycle_zero_of_extraction_zero
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = 0 + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1))
    (hcocycle : algebraicδ n R (𝒜 n R) 0 f = 0)
    (hextract : extractionHom 0 f = 0) :
    f = 0 := by
  funext ⟨S, hS⟩
  apply monomialCoeffMod_determines_zero
  intro a ha
  -- componentHom a 0 f is a 0-cocycle in K_{negSupport(a)}
  have hcomp_cocycle :
      _root_.relSimplexδHom a.negSupport R 0 (componentHom a 0 f) = 0 := by
    rw [← component_comm_δ a 0 f, hcocycle, map_zero]
  by_cases ha0 : a = (0 : LaurentExp n)
  · -- a = 0: componentHom reduces to extractionHom, which is 0
    subst ha0
    change componentHom 0 0 f ⟨S, hS, ha⟩ = 0
    rw [componentHom_zero_apply 0 f hS ha]
    exact congr_fun hextract ⟨S, hS, Finset.empty_subset S⟩
  · -- a ≠ 0: K_{negSupport(a)} is acyclic, so the 0-cocycle is 0
    have hne : a.negSupport.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty, ne_eq, LaurentExp.negSupport_empty_iff]
    have hne' : a.negSupport ≠ Finset.univ := a.negSupport_ne_univ (le_refl 0)
    have hac := _root_.relSimplexComplex_acyclic a.negSupport R hne hne'
    -- Acyclicity at degree 0 for ℕ-indexed complex means ker(d⁰) = 0
    show componentHom a 0 f ⟨S, hS, ha⟩ = 0
    suffices hz : componentHom a 0 f = 0 from congr_fun hz ⟨S, hS, ha⟩
    set K := _root_.relSimplexComplex a.negSupport R
    -- K is exact at degree 0 (from acyclicity): ker(g) ≤ range(f)
    have hker_le := ((K.sc 0).ab_exact_iff_ker_le_range).mp (hac 0)
    -- The incoming map f is 0 (no degree -1 in ℕ-complex)
    have hf_zero : (K.sc 0).f = 0 :=
      K.shape _ _ (fun h => by simp [ComplexShape.up_Rel] at h)
    -- So range(f) = ⊥
    have hrange_bot : (K.sc 0).f.hom.range = ⊥ := by
      have : (K.sc 0).f.hom = 0 := congr_arg AddCommGrp.Hom.hom hf_zero
      rw [this]; exact AddMonoidHom.range_zero
    -- Our element is in ker(g): the differential kills it
    have hg_mem : componentHom a 0 f ∈ (K.sc 0).g.hom.ker := by
      rw [AddMonoidHom.mem_ker]
      show K.d 0 ((ComplexShape.up ℕ).next 0) (componentHom a 0 f) = 0
      rw [(ComplexShape.up ℕ).next_eq' (show (0 : ℕ) + 1 = 1 from rfl),
        show K.d 0 1 = AddCommGrp.ofHom
          (_root_.relSimplexδHom a.negSupport R 0) from
          CochainComplex.of_d _ _ _ 0]
      exact hcomp_cocycle
    -- ker(g) ≤ range(f) = ⊥, so element ∈ ⊥ = {0}
    rw [hrange_bot] at hker_le
    exact AddSubgroup.mem_bot.mp (hker_le hg_mem)

/-- A 0-cocycle equals the embedding of its extraction (composed with
the constant cochain map). This is the key identity for left-invertibility
of the `kerEquiv` used in the `H⁰` computation. -/
private theorem embedding_extraction_cocycle_eq
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = 0 + 1},
      HomogeneousLocalizedModule.Away (𝒜 n R) (𝒜 n R) (coordProd n R S.1))
    (hcocycle : algebraicδ n R (𝒜 n R) 0 f = 0) :
    embeddingHom 0 (_root_.TopCat.relSimplexConstCochainHom R
      (_root_.TopCat.relSimplexEvalSingleton R 0 (extractionHom 0 f))) = f := by
  have hext_cocycle : _root_.relSimplexδHom (∅ : Finset (Fin (n + 1))) R 0
      (extractionHom 0 f) = 0 := by
    rw [← extraction_comm_δ 0 f, hcocycle, map_zero]
  rw [← _root_.TopCat.relSimplexCochain_empty_ker_const R
    (extractionHom 0 f) hext_cocycle]
  -- Goal: embeddingHom 0 (extractionHom 0 f) = f
  exact (sub_eq_zero.mp (algebraicCocycle_zero_of_extraction_zero
    (f - embeddingHom 0 (extractionHom 0 f))
    (by rw [map_sub, hcocycle, embedding_comm_δ 0 (extractionHom 0 f),
        hext_cocycle, map_zero, sub_zero])
    (by rw [map_sub, extraction_embedding_eq 0 (extractionHom 0 f), sub_self]))).symm

/-- `H⁰(algebraicComplex) ≅ R`: the degree-zero cohomology of the algebraic Čech
complex for the structure sheaf on projective space is isomorphic to the base ring.

The proof unwraps the categorical homology via `abHomologyIso`, then builds a concrete
`AddEquiv` between `ker(algebraicδ 0)` and `R` using:
- Forward: extraction followed by evaluation at `{0}`
- Inverse: constant cochain followed by embedding
The section property (`extraction ∘ embedding = id`) gives right inverse, and the
cocycle vanishing theorem gives left inverse. -/
noncomputable def algebraicComplex_H0_iso :
    (algebraicComplex n R (𝒜 n R)).homology 0 ≅ AddCommGrp.of R := by
  set A := algebraicComplex n R (𝒜 n R)
  -- Step 1: Unwrap homology via short complex
  refine A.homologyIsoSc' _ 0 1 rfl ((ComplexShape.up ℕ).next_eq' rfl) ≪≫ ?_
  set SA := A.sc' ((ComplexShape.up ℕ).prev 0) 0 1
  refine SA.abHomologyIso ≪≫ ?_
  -- Step 2: Incoming map f = 0 (no degree -1 in ℕ-indexed complex), so range = ⊥
  have hf : SA.f = 0 := A.shape _ _ (by simp [ComplexShape.up_Rel])
  have habToCycles_zero : SA.abToCycles = 0 := by
    ext x : 1; refine Subtype.ext ?_; change (SA.f x : SA.X₂) = 0; simp [hf]
  have hrange_bot : AddMonoidHom.range SA.abToCycles = ⊥ := by
    rw [habToCycles_zero]; exact AddMonoidHom.range_zero
  -- SA.g.hom = algebraicδ 0 (by CochainComplex.of_d)
  have hg_hom : SA.g.hom = algebraicδ n R (𝒜 n R) 0 := by
    show (A.d 0 1).hom = _
    have h : A.d 0 1 = AddCommGrp.ofHom (algebraicδ n R (𝒜 n R) 0) :=
      CochainComplex.of_d _ _ _ 0
    rw [h]; rfl
  -- Step 3: Build (ker g / range abToCycles) ≃+ R
  have kerEquiv : AddMonoidHom.ker SA.g.hom ≃+ R :=
    { toFun := fun f => _root_.TopCat.relSimplexEvalSingleton R 0 (extractionHom 0 f.1)
      invFun := fun r => ⟨embeddingHom 0 (_root_.TopCat.relSimplexConstCochainHom R r), by
        rw [AddMonoidHom.mem_ker, hg_hom]
        -- Prove at the concrete Pi type, then close via defeq
        exact show algebraicδ n R (𝒜 n R) 0
          (embeddingHom 0 (_root_.TopCat.relSimplexConstCochainHom R r)) = 0 by
          rw [embedding_comm_δ 0, _root_.TopCat.relSimplexδ_constCochain_eq_zero R r,
            map_zero]⟩
      left_inv := fun ⟨f, hf⟩ => by
        rw [AddMonoidHom.mem_ker] at hf
        exact Subtype.ext (embedding_extraction_cocycle_eq f (by rw [← hg_hom]; exact hf))
      right_inv := fun r => by
        show _root_.TopCat.relSimplexEvalSingleton R 0
          (extractionHom 0 (embeddingHom 0
            (_root_.TopCat.relSimplexConstCochainHom R r))) = r
        rw [extraction_embedding_eq 0]
        rfl
      map_add' := fun ⟨f, _⟩ ⟨g, _⟩ => by simp [map_add] }
  have totalEquiv :
      (AddMonoidHom.ker SA.g.hom ⧸ AddMonoidHom.range SA.abToCycles) ≃+ R :=
    (QuotientAddGroup.quotientAddEquivOfEq hrange_bot).trans
      (QuotientAddGroup.quotientBot.trans kerEquiv)
  exact totalEquiv.toAddCommGrpIso

end CohomologyH0

end AlgebraicGeometry.Proj
