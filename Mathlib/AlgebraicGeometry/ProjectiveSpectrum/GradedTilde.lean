/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module
import Mathlib.Algebra.Category.Grp.Limits

/-!
# The graded tilde construction `M̃` on `Proj(A)`

Given a graded ring `A = ⨁ᵢ 𝒜 i` and a graded `A`-module `M = ⨁ᵢ 𝓜 i`, we construct
a sheaf of abelian groups `M̃` on `Proj(A)` whose sections on an open `U` consist of
functions `f : Π x ∈ U, HomogeneousLocalizedModule 𝒜 𝓜 x` that are locally expressible as
fractions `m/s` with `m ∈ 𝓜 i` and `s ∈ 𝒜 i` of the same degree.

## Main definitions

* `ProjectiveSpectrum.GradedTilde.IsFraction`: predicate that a dependent function is a
  fixed fraction `m/s` of the same grading.
* `ProjectiveSpectrum.GradedTilde.isLocallyFraction`: the local predicate that a dependent
  function is locally a fraction.
* `ProjectiveSpectrum.GradedTilde.sectionsAddSubgroup`: the sections satisfying
  `isLocallyFraction` form an additive subgroup.
* `GradedModule.tilde`: the sheaf `M̃` valued in `AddCommGrp`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]
* [Jean-Pierre Serre, *Faisceaux algébriques cohérents*][Ser55]
-/

noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

universe u
variable {R : Type*} {A : Type u} {M : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable (𝓜 : ℕ → Submodule R M) [SetLike.GradedSMul 𝒜 𝓜]

local notation3 "mod_at " x =>
  HomogeneousLocalizedModule 𝒜 𝓜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x)).primeCompl

namespace ProjectiveSpectrum.GradedTilde

variable {𝒜 𝓜} in
/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`m / s` of *same grading* in each of the stalks (which are homogeneous localized modules at
various prime ideals). -/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, mod_at x.1) : Prop :=
  ∃ (i : ℕ) (m : 𝓜 i) (s : 𝒜 i) (s_nin : ∀ x : U, s.1 ∉ x.1.asHomogeneousIdeal),
    ∀ x : U, f x = .mk ⟨i, m, s, s_nin x⟩

/-- The predicate `IsFraction` is "prelocal", in the sense that if it holds on `U` it holds on any
open subset `V` of `U`. -/
def isFractionPrelocal :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => mod_at x where
  pred f := IsFraction f
  res := by rintro V U i f ⟨j, m, s, h, w⟩; exact ⟨j, m, s, (h <| i ·), (w <| i ·)⟩

/-- We define the graded tilde sheaf as the subsheaf of all dependent functions in
`Π x : U, HomogeneousLocalizedModule 𝒜 𝓜 x` consisting of those functions which can locally be
expressed as a fraction `m/s` of the same grading. -/
def isLocallyFraction :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => mod_at x :=
  (isFractionPrelocal 𝒜 𝓜).sheafify

namespace SectionSubgroup

variable {𝒜 𝓜}

open Submodule SetLike.GradedMonoid HomogeneousLocalizedModule

omit [SetLike.GradedSMul 𝒜 𝓜] in
theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜 𝓜).pred (0 : ∀ x : U.unop, mod_at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, 0, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, mod_at x.1)
    (ha : (isLocallyFraction 𝒜 𝓜).pred a) (hb : (isLocallyFraction 𝒜 𝓜).pred b) :
    (isLocallyFraction 𝒜 𝓜).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨(sb : A) • (ra : M) + (sa : A) • (rb : M),
        add_mem (add_comm jb ja ▸ SetLike.GradedSMul.smul_mem sb_mem ra_mem :
          (sb : A) • (ra : M) ∈ 𝓜 (ja + jb))
          (SetLike.GradedSMul.smul_mem sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y ↦
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
          (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp only [Opens.comp_apply, Opens.apply_mk, Pi.add_apply, wa y hy.1, wb y hy.2, ← mk_add]
  rfl

omit [SetLike.GradedSMul 𝒜 𝓜] in
theorem neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : ∀ x : U.unop, mod_at x.1)
    (ha : (isLocallyFraction 𝒜 𝓜).pred a) :
    (isLocallyFraction 𝒜 𝓜).pred (-a) := fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, nin, hy⟩
  refine ⟨V, m, i, j, ⟨-r, Submodule.neg_mem _ r_mem⟩, ⟨s, s_mem⟩, nin, fun y => ?_⟩
  simp only [Pi.neg_apply, hy y, ← mk_neg]; rfl

end SectionSubgroup

section

open SectionSubgroup

variable {𝒜 𝓜}

/-- The functions satisfying `isLocallyFraction` form an additive subgroup of all dependent
functions `Π x : U, HomogeneousLocalizedModule 𝒜 𝓜 x`. -/
def sectionsAddSubgroup (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddSubgroup (∀ x : U.unop, mod_at x.1) where
  carrier := {f | (isLocallyFraction 𝒜 𝓜).pred f}
  zero_mem' := zero_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _

end

/-- The graded tilde sheaf (valued in `Type`, not yet `AddCommGrp`) is the subsheaf consisting of
functions satisfying `isLocallyFraction`. -/
def structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 𝓜)

instance addCommGroupStructureSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((structureSheafInType 𝒜 𝓜).1.obj U) :=
  inferInstanceAs (AddCommGroup (sectionsAddSubgroup U))

/-- The graded tilde presheaf, valued in `AddCommGrp`, constructed by dressing up the `Type` valued
structure presheaf. -/
def structurePresheafInAddCommGrp :
    Presheaf AddCommGrp (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrp.of ((structureSheafInType 𝒜 𝓜).1.obj U)
  map i := AddCommGrp.ofHom
    { toFun := (structureSheafInType 𝒜 𝓜).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Some glue, verifying that the structure presheaf valued in `AddCommGrp` agrees with the `Type`
valued structure presheaf. -/
def structurePresheafCompForget :
    structurePresheafInAddCommGrp 𝒜 𝓜 ⋙ forget AddCommGrp ≅
      (structureSheafInType 𝒜 𝓜).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)

end ProjectiveSpectrum.GradedTilde

namespace GradedModule

open TopCat.Presheaf ProjectiveSpectrum.GradedTilde Opens

/-- The graded tilde construction `M̃`: a sheaf of abelian groups on `Proj(A)` associated to a
graded module `M` over a graded ring `A`. -/
def tilde : Sheaf AddCommGrp (ProjectiveSpectrum.top 𝒜) :=
  ⟨structurePresheafInAddCommGrp 𝒜 𝓜,
    (isSheaf_iff_isSheaf_comp
      (forget AddCommGrp) _).mpr
      (isSheaf_of_iso (structurePresheafCompForget 𝒜 𝓜).symm
        (structureSheafInType 𝒜 𝓜).cond)⟩

open HomogeneousLocalizedModule in
/-- The group homomorphism from the degree-zero localized module `M⁰_f` to sections of `M̃`
on the basic open set `D₊(f)`, defined by sending `s ∈ M⁰_f` to the section `x ↦ s` on
`D₊(f)`. This is the module-level analogue of `ProjectiveSpectrum.Proj.awayToSection`. -/
def awayToSection (f : A) :
    HomogeneousLocalizedModule.Away 𝒜 𝓜 f →+
      (tilde 𝒜 𝓜).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) where
  toFun s :=
    ⟨fun x ↦ HomogeneousLocalizedModule.mapId (Submonoid.powers_le.mpr x.2) s, fun x => by
      obtain ⟨s, rfl⟩ := Quotient.mk''_surjective s
      obtain ⟨n, hn : f ^ n = (s.den : A)⟩ := s.den_mem
      exact ⟨_, x.2, 𝟙 _, s.deg, s.num, s.den,
        fun y hsy ↦ y.2 (Ideal.IsPrime.mem_of_pow_mem inferInstance n (hn ▸ hsy)),
        fun _ ↦ rfl⟩⟩
  map_zero' := Subtype.ext <| funext fun _ => map_zero _
  map_add' _ _ := Subtype.ext <| funext fun _ => map_add _ _ _

section AwayMapNaturality

variable {f : A} {e : ℕ} {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g)

open HomogeneousLocalizedModule in
lemma awayMap_awayToSection (a : HomogeneousLocalizedModule.Away 𝒜 𝓜 f) :
    awayToSection 𝒜 𝓜 x (HomogeneousLocalizedModule.awayMap 𝒜 𝓜 hg hx a) =
    (tilde 𝒜 𝓜).1.map
      (homOfLE (hx ▸ ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 f g)).op
      (awayToSection 𝒜 𝓜 f a) := by
  apply Subtype.ext
  funext ⟨p, hp⟩
  exact HomogeneousLocalizedModule.mapId_awayMap 𝒜 𝓜 hg hx _ _ a

end AwayMapNaturality

end GradedModule

end AlgebraicGeometry
