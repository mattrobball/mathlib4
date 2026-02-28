/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.GradedTilde
import Mathlib.Topology.Sheaves.CechCochainComplex

/-!
# Čech complex of `M̃` on projective space with the standard cover

Given a graded module `M` over the polynomial ring `R[x₀, ..., xₙ]`, we specialize the
Čech cochain complex to the sheaf `M̃` on `Proj(R[x₀, ..., xₙ])` with respect to the
standard coordinate cover `D₊(x₀), ..., D₊(xₙ)`.

## Main definitions

* `AlgebraicGeometry.Proj.standardCoverOpens`: The standard cover of projective n-space as
  opens of the projective spectrum.
* `AlgebraicGeometry.Proj.cechCoverInf_standardCover`: The Čech intersection
  `⋂_{i ∈ S} D₊(xᵢ)` equals `D₊(∏_{i ∈ S} xᵢ)`.
* `AlgebraicGeometry.Proj.cechComplexTilde`: The Čech cochain complex of `M̃` with the
  standard coordinate cover.
* `AlgebraicGeometry.Proj.awayToSectionCech`: The comparison map from the algebraic
  localization `M⁰_{∏ xᵢ}` to sections of `M̃` on the Čech intersection.
* `AlgebraicGeometry.Proj.algebraicToCech`: The comparison map from the product of algebraic
  localizations to the Čech cochain group.
* `AlgebraicGeometry.Proj.coordRestrict`: The face restriction map on algebraic localizations.
* `AlgebraicGeometry.Proj.algebraicδ`: The algebraic coboundary on the product of degree-zero
  localizations.
* `AlgebraicGeometry.Proj.algebraicToCech_comm`: The chain map property: `algebraicToCech`
  commutes with the coboundary maps.
* `AlgebraicGeometry.Proj.algebraicComplex`: The algebraic Čech cochain complex.
* `AlgebraicGeometry.Proj.algebraicToCechHom`: The chain map from the algebraic complex to the
  topological Čech complex.

## References

* [Stacks Project, Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)
-/

noncomputable section

open MvPolynomial CategoryTheory TopologicalSpace Opposite Finset

namespace AlgebraicGeometry.Proj

universe u

variable (n : ℕ) (R : Type u) [CommRing R]

attribute [local instance] mvPolynomialGrading

private abbrev 𝒜' (n : ℕ) (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

section StandardCoverOpens

/-- The standard cover of projective n-space as opens of the projective spectrum,
for use with the Čech complex. -/
def standardCoverOpens :
    Fin (n + 1) → Opens (ProjectiveSpectrum.top (𝒜' n R)) :=
  fun i => ProjectiveSpectrum.basicOpen (𝒜' n R) (coord n R i)

theorem cechCoverInf_standardCover (S : Finset (Fin (n + 1))) :
    TopCat.cechCoverInf (standardCoverOpens n R) S =
      ProjectiveSpectrum.basicOpen (𝒜' n R) (coordProd n R S) :=
  (ProjectiveSpectrum.basicOpen_finset_prod (𝒜' n R) S (coord n R)).symm

end StandardCoverOpens

section CechTilde

variable {M : Type u} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (Fin (n + 1)) R) M]
  (𝓜 : ℕ → Submodule R M) [SetLike.GradedSMul (𝒜' n R) 𝓜]

/-- The Čech cochain complex of `M̃` on `Proj(R[x₀,...,xₙ])` with the
standard coordinate cover `D₊(x₀), ..., D₊(xₙ)`. -/
def cechComplexTilde :
    CochainComplex AddCommGrp ℕ :=
  TopCat.cechComplex (GradedModule.tilde (𝒜' n R) 𝓜) (standardCoverOpens n R)

/-- The comparison map from `Away 𝒜 𝓜 (coordProd S)` to sections of `M̃` on the
Čech intersection `⋂_{i∈S} D₊(xᵢ)`, obtained by composing `awayToSection` with
the transport along `cechCoverInf_standardCover`. -/
def awayToSectionCech (S : Finset (Fin (n + 1))) :
    HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R S) →+
      (GradedModule.tilde (𝒜' n R) 𝓜).1.obj
        (op (TopCat.cechCoverInf (standardCoverOpens n R) S)) :=
  ((GradedModule.tilde (𝒜' n R) 𝓜).1.map
    (homOfLE (le_of_eq (cechCoverInf_standardCover n R S))).op).hom.comp
    (GradedModule.awayToSection (𝒜' n R) 𝓜 (coordProd n R S))

/-- The comparison map from the algebraic Čech cochain group (product of degree-0
localizations) to the topological Čech cochain group. -/
def algebraicToCech (p : ℕ) :
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R S.1)) →+
    TopCat.cechObj (GradedModule.tilde (𝒜' n R) 𝓜) (standardCoverOpens n R) p :=
  Pi.addMonoidHom fun S => (awayToSectionCech n R 𝓜 S.1).comp
    (Pi.evalAddMonoidHom _ S)

/-- The face restriction map on algebraic localizations: given `T` with `|T| = p + 2`
and `j : Fin (p + 2)`, maps `M⁰_{∏ xᵢ : i ∈ T\{tⱼ}}` to `M⁰_{∏ xᵢ : i ∈ T}`
via `awayMap` along the factorization `coordProd T = coordProd(T \ {tⱼ}) * xⱼ`. -/
def coordRestrict {p : ℕ} (T : Finset (Fin (n + 1))) (hT : T.card = p + 2)
    (j : Fin (p + 2)) :
    HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜
      (coordProd n R (TopCat.eraseNth T hT j).1) →+
    HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R T) :=
  HomogeneousLocalizedModule.awayMap (𝒜' n R) 𝓜
    (coord_mem_homogeneousSubmodule n R (TopCat.nthElem T hT j))
    (coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j))

/-- Naturality of `awayToSectionCech` with respect to `coordRestrict`: the algebraic
face restriction followed by the comparison map equals the comparison map followed by
the topological sheaf restriction. -/
theorem awayToSectionCech_naturality {p : ℕ} (T : Finset (Fin (n + 1)))
    (hT : T.card = p + 2) (j : Fin (p + 2))
    (a : HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜
      (coordProd n R (TopCat.eraseNth T hT j).1)) :
    awayToSectionCech n R 𝓜 T (coordRestrict n R 𝓜 T hT j a) =
      (GradedModule.tilde (𝒜' n R) 𝓜).1.map
        (homOfLE (TopCat.cechCoverInf_mono (standardCoverOpens n R)
          (Finset.erase_subset _ _))).op
        (awayToSectionCech n R 𝓜 (TopCat.eraseNth T hT j).1 a) := by
  apply Subtype.ext
  funext ⟨x, hx⟩
  exact HomogeneousLocalizedModule.mapId_awayMap (𝒜' n R) 𝓜
    (coord_mem_homogeneousSubmodule n R (TopCat.nthElem T hT j))
    (coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j)) _ _ a

/-- The algebraic coboundary on the product of degree-zero localizations.
For each `T` with `|T| = p + 2`, sends `f` to
`∑_{j=0}^{p+1} (-1)^j · coordRestrict(f_{T\{tⱼ}})`. -/
def algebraicδ (p : ℕ) :
    (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R S.1)) →+
    (∀ T : {T : Finset (Fin (n + 1)) // T.card = p + 2},
      HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R T.1)) where
  toFun := fun f ⟨T, hT⟩ =>
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
      coordRestrict n R 𝓜 T hT j (f (TopCat.eraseNth T hT j))
  map_zero' := by
    ext ⟨T, hT⟩; simp [map_zero, smul_zero, Finset.sum_const_zero]
  map_add' := fun f g => by
    ext ⟨T, hT⟩; simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

/-- The comparison map `algebraicToCech` commutes with the coboundary:
`algebraicToCech ∘ algebraicδ = cechδ ∘ algebraicToCech`, establishing that `algebraicToCech`
is a chain map from the algebraic complex to the topological Čech complex. -/
theorem algebraicToCech_comm (p : ℕ)
    (f : ∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R S.1)) :
    algebraicToCech n R 𝓜 (p + 1) (algebraicδ n R 𝓜 p f) =
      TopCat.cechδ (GradedModule.tilde (𝒜' n R) 𝓜) (standardCoverOpens n R) p
        (algebraicToCech n R 𝓜 p f) := by
  funext ⟨T, hT⟩
  -- Both sides reduce definitionally to explicit sums
  change awayToSectionCech n R 𝓜 T
      (∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
        coordRestrict n R 𝓜 T hT j (f (TopCat.eraseNth T hT j))) =
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
      (GradedModule.tilde (𝒜' n R) 𝓜).1.map
        (homOfLE (TopCat.cechCoverInf_mono (standardCoverOpens n R)
          (Finset.erase_subset _ _))).op
        (awayToSectionCech n R 𝓜 (TopCat.eraseNth T hT j).1 (f (TopCat.eraseNth T hT j)))
  rw [map_sum]; simp_rw [map_zsmul]
  congr 1; ext j; congr 1
  exact awayToSectionCech_naturality n R 𝓜 T hT j (f (TopCat.eraseNth T hT j))

set_option maxHeartbeats 400000 in
/-- Two `coordRestrict` compositions to the same target agree when the double-erased
source subtypes agree. This is the algebraic analogue of `restriction_comp_congr`. -/
private theorem coordRestrict_comp_congr {p : ℕ} {T : Finset (Fin (n + 1))}
    (hT : T.card = p + 3)
    {j₁ j₂ : Fin (p + 3)} {k₁ k₂ : Fin (p + 2)}
    {S : {S : Finset (Fin (n + 1)) // S.card = p + 1}}
    (hS₁ : TopCat.eraseNth (TopCat.eraseNth T hT j₁).1
      (TopCat.eraseNth T hT j₁).2 k₁ = S)
    (hS₂ : TopCat.eraseNth (TopCat.eraseNth T hT j₂).1
      (TopCat.eraseNth T hT j₂).2 k₂ = S)
    (a : HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R S.1)) :
    coordRestrict n R 𝓜 T hT j₁
      (coordRestrict n R 𝓜 (TopCat.eraseNth T hT j₁).1
        (TopCat.eraseNth T hT j₁).2 k₁ (hS₁ ▸ a)) =
    coordRestrict n R 𝓜 T hT j₂
      (coordRestrict n R 𝓜 (TopCat.eraseNth T hT j₂).1
        (TopCat.eraseNth T hT j₂).2 k₂ (hS₂ ▸ a)) := by
  subst hS₁
  unfold coordRestrict
  exact @HomogeneousLocalizedModule.awayMap_comp_congr_subst
    ℕ R (MvPolynomial (Fin (n + 1)) R) M _ _ _ _ _ _ (𝒜' n R) 𝓜 _ _ _ _
    {S : Finset (Fin (n + 1)) // S.card = p + 1}
    (fun S => coordProd n R S.1)
    (TopCat.eraseNth (TopCat.eraseNth T hT j₁).1
      (TopCat.eraseNth T hT j₁).2 k₁)
    (TopCat.eraseNth (TopCat.eraseNth T hT j₂).1
      (TopCat.eraseNth T hT j₂).2 k₂)
    1 1 1 1
    (coord n R (TopCat.nthElem (TopCat.eraseNth T hT j₁).1
      (TopCat.eraseNth T hT j₁).2 k₁))
    (coord n R (TopCat.nthElem T hT j₁))
    (coord n R (TopCat.nthElem (TopCat.eraseNth T hT j₂).1
      (TopCat.eraseNth T hT j₂).2 k₂))
    (coord n R (TopCat.nthElem T hT j₂))
    (coord_mem_homogeneousSubmodule n R
      (TopCat.nthElem (TopCat.eraseNth T hT j₁).1
        (TopCat.eraseNth T hT j₁).2 k₁))
    (coord_mem_homogeneousSubmodule n R (TopCat.nthElem T hT j₁))
    (coord_mem_homogeneousSubmodule n R
      (TopCat.nthElem (TopCat.eraseNth T hT j₂).1
        (TopCat.eraseNth T hT j₂).2 k₂))
    (coord_mem_homogeneousSubmodule n R (TopCat.nthElem T hT j₂))
    (coordProd n R (TopCat.eraseNth T hT j₁).1)
    (coordProd n R (TopCat.eraseNth T hT j₂).1)
    (coordProd n R T)
    (coordProd_eq_erase_mul n R (TopCat.eraseNth T hT j₁).1
      (TopCat.nthElem_mem (TopCat.eraseNth T hT j₁).1
        (TopCat.eraseNth T hT j₁).2 k₁))
    (coordProd_eq_erase_mul n R (TopCat.eraseNth T hT j₂).1
      (TopCat.nthElem_mem (TopCat.eraseNth T hT j₂).1
        (TopCat.eraseNth T hT j₂).2 k₂))
    (coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j₁))
    (coordProd_eq_erase_mul n R T (TopCat.nthElem_mem T hT j₂))
    hS₂ a

/-- The algebraic coboundary squares to zero: `algebraicδ (p+1) ∘ algebraicδ p = 0`. -/
theorem algebraicδ_comp_algebraicδ (p : ℕ) :
    AddCommGrp.ofHom (algebraicδ n R 𝓜 p) ≫
      AddCommGrp.ofHom (algebraicδ n R 𝓜 (p + 1)) = 0 :=
  AddCommGrp.ext fun f => by
  funext ⟨T, hT⟩
  change (algebraicδ n R 𝓜 (p + 1) (algebraicδ n R 𝓜 p f)) ⟨T, hT⟩ = 0
  show ∑ j : Fin (p + 3), ((-1 : ℤ) ^ j.val) •
    coordRestrict n R 𝓜 T hT j
      (∑ k : Fin (p + 2), ((-1 : ℤ) ^ k.val) •
        coordRestrict n R 𝓜 (TopCat.eraseNth T hT j).1 (TopCat.eraseNth T hT j).2 k
          (f (TopCat.eraseNth (TopCat.eraseNth T hT j).1
            (TopCat.eraseNth T hT j).2 k))) = 0
  simp_rw [map_sum, map_zsmul]
  conv_lhs => arg 2; ext j; rw [Finset.smul_sum]; arg 2; ext k; rw [smul_smul]
  rw [← Finset.sum_product']
  apply Finset.sum_ninvolution (TopCat.cechInvolution p)
  · intro jk
    have hval : (TopCat.eraseNth (TopCat.eraseNth T hT
          (TopCat.cechInvolution p jk).1).1
        (TopCat.eraseNth T hT (TopCat.cechInvolution p jk).1).2
        (TopCat.cechInvolution p jk).2) =
      (TopCat.eraseNth (TopCat.eraseNth T hT jk.1).1
        (TopCat.eraseNth T hT jk.1).2 jk.2) :=
      Subtype.ext (TopCat.eraseNth_eraseNth_involution p T hT jk)
    rw [TopCat.cechInvolution_sign, neg_smul, add_neg_eq_zero]
    congr 1
    -- Transport f(eraseNth²(inv jk)) to f(eraseNth²(jk)) via hval ▸.
    have dep : f (TopCat.eraseNth (TopCat.eraseNth T hT
            (TopCat.cechInvolution p jk).1).1
          (TopCat.eraseNth T hT (TopCat.cechInvolution p jk).1).2
          (TopCat.cechInvolution p jk).2) =
        hval ▸ (f (TopCat.eraseNth (TopCat.eraseNth T hT jk.1).1
            (TopCat.eraseNth T hT jk.1).2 jk.2)) := by
      revert hval
      generalize TopCat.eraseNth (TopCat.eraseNth T hT
            (TopCat.cechInvolution p jk).1).1
          (TopCat.eraseNth T hT (TopCat.cechInvolution p jk).1).2
          (TopCat.cechInvolution p jk).2 = S₁
      intro hval; subst hval; rfl
    rw [dep]
    have h := coordRestrict_comp_congr n R 𝓜 hT rfl hval
      (f (TopCat.eraseNth (TopCat.eraseNth T hT jk.1).1
        (TopCat.eraseNth T hT jk.1).2 jk.2))
    simp only [eq_mpr_eq_cast, cast_eq] at h
    exact h
  · intro jk _; exact TopCat.cechInvolution_ne p jk
  · intro _; exact Finset.mem_univ _
  · exact TopCat.cechInvolution_involutive p

/-- The algebraic Čech cochain complex: in degree `p`, the product of `M⁰_{∏ xᵢ}`
over all `(p+1)`-element subsets, with the algebraic coboundary `algebraicδ`. -/
def algebraicComplex : CochainComplex AddCommGrp ℕ :=
  CochainComplex.of
    (fun p => AddCommGrp.of (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R S.1)))
    (fun p => AddCommGrp.ofHom (algebraicδ n R 𝓜 p))
    (fun p => algebraicδ_comp_algebraicδ n R 𝓜 p)

/-- The chain map from the algebraic Čech complex to the topological Čech complex of `M̃`,
built from the comparison maps `algebraicToCech` at each degree. -/
def algebraicToCechHom :
    algebraicComplex n R 𝓜 ⟶ cechComplexTilde n R 𝓜 :=
  CochainComplex.ofHom
    (fun p => AddCommGrp.of (∀ S : {S : Finset (Fin (n + 1)) // S.card = p + 1},
      HomogeneousLocalizedModule.Away (𝒜' n R) 𝓜 (coordProd n R S.1)))
    (fun p => AddCommGrp.ofHom (algebraicδ n R 𝓜 p))
    (fun p => algebraicδ_comp_algebraicδ n R 𝓜 p)
    (TopCat.cechObj (GradedModule.tilde (𝒜' n R) 𝓜) (standardCoverOpens n R))
    (TopCat.cechδ (GradedModule.tilde (𝒜' n R) 𝓜) (standardCoverOpens n R))
    (TopCat.cechδ_comp_cechδ (GradedModule.tilde (𝒜' n R) 𝓜) (standardCoverOpens n R))
    (fun p => AddCommGrp.ofHom (algebraicToCech n R 𝓜 p))
    (fun p => AddCommGrp.ext (fun f =>
      (algebraicToCech_comm n R 𝓜 p f).symm))

end CechTilde

end AlgebraicGeometry.Proj
