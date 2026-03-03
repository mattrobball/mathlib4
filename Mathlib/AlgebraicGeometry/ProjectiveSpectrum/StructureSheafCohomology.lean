/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.MonomialCoefficient

/-!
# Cohomology of the structure sheaf on projective space

This file computes the Čech cohomology of the structure sheaf `𝒪` on projective
n-space over a commutative ring `R`:
- `H⁰(algebraicComplex, 𝒪) ≅ R`

The proof builds an embedding chain map `K_∅ → algebraicComplex` (a section of the
extraction chain map), then uses the monomial decomposition to show the extraction
is a quasi-isomorphism at degree 0.

## Main results

* `algebraicComplex_H0_iso`: `H⁰ ≅ R`

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
  apply HomogeneousLocalizedModule.ext (Submonoid.powers (coordProd n R T))
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
  show zeroExpCoeffMod S ((awayRingModuleEquiv (𝒜 n R)) (constRingElemHom S r)) = r
  simp only [zeroExpCoeffMod, AddMonoidHom.coe_comp, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, Function.comp_apply, AddEquiv.symm_apply_apply]
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
  apply monomialCoeffShift_determines_zero (le_refl (0 : ℤ))
  intro a ha
  -- componentHomShift a 0 f is a 0-cocycle in K_{negSupport(a)}
  have hcomp_cocycle :
      _root_.relSimplexδHom a.negSupport R 0 (componentHomShift a 0 f) = 0 := by
    rw [← componentShift_comm_δ a 0 f]
    change componentHomShift a 1 (algebraicδ n R (𝒜 n R) 0 f) = 0
    rw [hcocycle, map_zero]
  by_cases ha0 : a = (0 : LaurentExp n)
  · -- a = 0: componentHomShift reduces to extractionHom, which is 0
    subst ha0
    change componentHomShift 0 0 f ⟨S, hS, ha⟩ = 0
    rw [componentHomShift_zero_apply 0 f hS ha]
    exact congr_fun hextract ⟨S, hS, Finset.empty_subset S⟩
  · -- a ≠ 0: K_{negSupport(a)} is acyclic, so the 0-cocycle is 0
    have hne : a.negSupport.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty, ne_eq, LaurentExp.negSupport_empty_iff]
    have hne' : a.negSupport ≠ Finset.univ := a.negSupport_ne_univ (le_refl 0)
    have hac := _root_.relSimplexComplex_acyclic a.negSupport R hne hne'
    -- Acyclicity at degree 0 for ℕ-indexed complex means ker(d⁰) = 0
    show componentHomShift a 0 f ⟨S, hS, ha⟩ = 0
    suffices hz : componentHomShift a 0 f = 0 from congr_fun hz ⟨S, hS, ha⟩
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
    have hg_mem : componentHomShift a 0 f ∈ (K.sc 0).g.hom.ker := by
      rw [AddMonoidHom.mem_ker]
      show K.d 0 ((ComplexShape.up ℕ).next 0) (componentHomShift a 0 f) = 0
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
