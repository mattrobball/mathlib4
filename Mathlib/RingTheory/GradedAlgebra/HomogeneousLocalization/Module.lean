/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.GradedMulAction

/-!
# Homogeneous Localization for Graded Modules

Given a graded ring `A = ⨁ᵢ 𝒜 i` and a graded `A`-module `M = ⨁ᵢ 𝓜 i`, for a
submonoid `x` of `A` we define the **degree-zero part** of the localized module `Mₓ`,
consisting of fractions `m/s` where `m ∈ 𝓜 d` and `s ∈ 𝒜 d` have the same degree.

This construction is the module-level analogue of `HomogeneousLocalization` (which handles
the ring case `M = A`) and is the building block for the graded tilde construction
`M̃` on `Proj(A)`.

## Main definitions

* `HomogeneousLocalizedModule.NumDenSameDeg`: Pairs `(m, s)` with `m ∈ 𝓜 d`, `s ∈ 𝒜 d`,
  and `s ∈ x`, representing the fraction `m/s` of degree 0.
* `HomogeneousLocalizedModule`: The quotient of `NumDenSameDeg` identifying fractions
  that become equal in the localized module `Mₓ`.
* `HomogeneousLocalizedModule.Away`: The special case `x = Submonoid.powers f`.

## References

* [Stacks Project, Graded tilde](https://stacks.math.columbia.edu/tag/01M3)

## Tags

graded module, homogeneous localization, tilde construction
-/

noncomputable section

open DirectSum Pointwise SetLike

variable {ι R A M : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M]
variable (𝒜 : ι → Submodule R A)
variable (𝓜 : ι → Submodule R M)
variable (x : Submonoid A)

namespace HomogeneousLocalizedModule

section

/-- A pair `(m, s)` where `m ∈ 𝓜 d` and `s ∈ 𝒜 d` have the same degree and `s ∈ x`.
This represents the fraction `m/s` of degree 0 in the localized module. -/
structure NumDenSameDeg where
  deg : ι
  num : 𝓜 deg
  den : 𝒜 deg
  den_mem : (den : A) ∈ x

end

namespace NumDenSameDeg

variable {𝒜} {𝓜}

omit [Module A M] in
@[ext]
theorem ext {c1 c2 : NumDenSameDeg 𝒜 𝓜 x} (hdeg : c1.deg = c2.deg)
    (hnum : (c1.num : M) = c2.num) (hden : (c1.den : A) = c2.den) : c1 = c2 := by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  subst hdeg hnum hden
  congr

omit [Module A M] in
instance : Neg (NumDenSameDeg 𝒜 𝓜 x) where
  neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

omit [Module A M] in
@[simp]
theorem deg_neg (c : NumDenSameDeg 𝒜 𝓜 x) : (-c).deg = c.deg := rfl

omit [Module A M] in
@[simp]
theorem num_neg (c : NumDenSameDeg 𝒜 𝓜 x) : ((-c).num : M) = -c.num := rfl

omit [Module A M] in
@[simp]
theorem den_neg (c : NumDenSameDeg 𝒜 𝓜 x) : ((-c).den : A) = c.den := rfl

variable [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]

omit [Module A M] in
instance : Zero (NumDenSameDeg 𝒜 𝓜 x) where
  zero := ⟨0, 0, ⟨1, GradedOne.one_mem⟩, Submonoid.one_mem _⟩

omit [Module A M] in
@[simp]
theorem deg_zero : (0 : NumDenSameDeg 𝒜 𝓜 x).deg = 0 := rfl

omit [Module A M] in
@[simp]
theorem num_zero : (0 : NumDenSameDeg 𝒜 𝓜 x).num = 0 := rfl

omit [Module A M] in
@[simp]
theorem den_zero : ((0 : NumDenSameDeg 𝒜 𝓜 x).den : A) = 1 := rfl

instance [SetLike.GradedSMul 𝒜 𝓜] : Add (NumDenSameDeg 𝒜 𝓜 x) where
  add c1 c2 :=
    { deg := c1.deg + c2.deg
      num := ⟨(c2.den : A) • (c1.num : M) + (c1.den : A) • (c2.num : M),
        add_mem (add_comm c1.deg c2.deg ▸ SetLike.GradedSMul.smul_mem c2.den.2 c1.num.2)
          (SetLike.GradedSMul.smul_mem c1.den.2 c2.num.2)⟩
      den := ⟨c1.den * c2.den, GradedMul.mul_mem c1.den.2 c2.den.2⟩
      den_mem := Submonoid.mul_mem _ c1.den_mem c2.den_mem }

@[simp]
theorem deg_add [SetLike.GradedSMul 𝒜 𝓜] (c1 c2 : NumDenSameDeg 𝒜 𝓜 x) :
    (c1 + c2).deg = c1.deg + c2.deg := rfl

@[simp]
theorem num_add [SetLike.GradedSMul 𝒜 𝓜] (c1 c2 : NumDenSameDeg 𝒜 𝓜 x) :
    ((c1 + c2).num : M) =
      (c2.den : A) • (c1.num : M) + (c1.den : A) • (c2.num : M) := rfl

@[simp]
theorem den_add [SetLike.GradedSMul 𝒜 𝓜] (c1 c2 : NumDenSameDeg 𝒜 𝓜 x) :
    ((c1 + c2).den : A) = c1.den * c2.den := rfl

/-- The scalar action by `HomogeneousLocalization.NumDenSameDeg` (ring elements)
on `HomogeneousLocalizedModule.NumDenSameDeg` (module elements). -/
instance [SetLike.GradedSMul 𝒜 𝓜] :
    SMul (HomogeneousLocalization.NumDenSameDeg 𝒜 x) (NumDenSameDeg 𝒜 𝓜 x) where
  smul r m :=
    { deg := r.deg + m.deg
      num := ⟨(r.num : A) • (m.num : M),
        SetLike.GradedSMul.smul_mem r.num.2 m.num.2⟩
      den := ⟨r.den * m.den, GradedMul.mul_mem r.den.2 m.den.2⟩
      den_mem := Submonoid.mul_mem _ r.den_mem m.den_mem }

variable (𝒜 𝓜)

/-- The embedding of a homogeneous fraction `m/s` into the localized module `Mₓ`. -/
def embedding (p : NumDenSameDeg 𝒜 𝓜 x) : LocalizedModule x M :=
  LocalizedModule.mk (p.num : M) ⟨(p.den : A), p.den_mem⟩

variable {𝒜 𝓜}

variable [SetLike.GradedSMul 𝒜 𝓜]

private theorem embedding_add (c1 c2 : NumDenSameDeg 𝒜 𝓜 x) :
    embedding 𝒜 𝓜 x (c1 + c2) = embedding 𝒜 𝓜 x c1 + embedding 𝒜 𝓜 x c2 := by
  simp only [embedding, num_add, den_add, LocalizedModule.mk_add_mk,
    Submonoid.smul_def, Submonoid.coe_mul]
  exact congrArg (LocalizedModule.mk _) (Subtype.ext rfl)

end NumDenSameDeg

end HomogeneousLocalizedModule

/-- For a submonoid `x` of `A`, `HomogeneousLocalizedModule 𝒜 𝓜 x` is the degree-zero part
of the localized module `Mₓ`, consisting of fractions `m/s` where `m` and `s` have the
same degree. It is `NumDenSameDeg 𝒜 𝓜 x` modulo the kernel of the embedding into `Mₓ`. -/
def HomogeneousLocalizedModule : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalizedModule.NumDenSameDeg.embedding 𝒜 𝓜 x)

namespace HomogeneousLocalizedModule

open HomogeneousLocalizedModule.NumDenSameDeg

variable {𝒜} {𝓜} {x}

/-- Construct an element of `HomogeneousLocalizedModule 𝒜 𝓜 x` from a homogeneous fraction. -/
abbrev mk (y : NumDenSameDeg 𝒜 𝓜 x) : HomogeneousLocalizedModule 𝒜 𝓜 x :=
  Quotient.mk'' y

/-- View an element as a fraction in the localized module `Mₓ`. -/
def val (y : HomogeneousLocalizedModule 𝒜 𝓜 x) : LocalizedModule x M :=
  Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 𝓜 x) fun _ _ => id

@[simp]
theorem val_mk (i : NumDenSameDeg 𝒜 𝓜 x) :
    val (mk i) = LocalizedModule.mk (i.num : M) ⟨(i.den : A), i.den_mem⟩ :=
  rfl

variable (x)

theorem val_injective :
    Function.Injective
      (HomogeneousLocalizedModule.val (𝒜 := 𝒜) (𝓜 := 𝓜) (x := x)) :=
  fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h

@[ext]
theorem ext {a b : HomogeneousLocalizedModule 𝒜 𝓜 x} (h : a.val = b.val) : a = b :=
  val_injective x h

variable {x}

section AddCommGroup

variable [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

instance : Zero (HomogeneousLocalizedModule 𝒜 𝓜 x) where zero := Quotient.mk'' 0

omit [SetLike.GradedSMul 𝒜 𝓜] in
@[simp] lemma mk_zero : mk (0 : NumDenSameDeg 𝒜 𝓜 x) = 0 := rfl

instance : Neg (HomogeneousLocalizedModule 𝒜 𝓜 x) where
  neg := Quotient.map' Neg.neg
    fun c1 c2 (h : embedding 𝒜 𝓜 x c1 = embedding 𝒜 𝓜 x c2) => by
      change embedding 𝒜 𝓜 x (-c1) = embedding 𝒜 𝓜 x (-c2)
      simp only [embedding, num_neg, den_neg, ← LocalizedModule.mk_neg]
      exact congr_arg Neg.neg h

omit [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 𝓜] in
@[simp] lemma mk_neg (i : NumDenSameDeg 𝒜 𝓜 x) : mk (-i) = -mk i := rfl

instance : Add (HomogeneousLocalizedModule 𝒜 𝓜 x) where
  add := Quotient.map₂ (· + ·)
    fun c1 c2 (h : embedding 𝒜 𝓜 x c1 = embedding 𝒜 𝓜 x c2) c3 c4
        (h' : embedding 𝒜 𝓜 x c3 = embedding 𝒜 𝓜 x c4) => by
      change embedding 𝒜 𝓜 x (c1 + c3) = embedding 𝒜 𝓜 x (c2 + c4)
      rw [NumDenSameDeg.embedding_add, NumDenSameDeg.embedding_add, h, h']

@[simp] lemma mk_add (i j : NumDenSameDeg 𝒜 𝓜 x) : mk (i + j) = mk i + mk j := rfl

instance : Sub (HomogeneousLocalizedModule 𝒜 𝓜 x) where sub z1 z2 := z1 + -z2

omit [SetLike.GradedSMul 𝒜 𝓜] in
@[simp]
lemma val_zero : (0 : HomogeneousLocalizedModule 𝒜 𝓜 x).val = 0 := by
  show embedding 𝒜 𝓜 x (0 : NumDenSameDeg 𝒜 𝓜 x) = 0
  simp [embedding, LocalizedModule.zero_mk]

@[simp]
lemma val_add (a b : HomogeneousLocalizedModule 𝒜 𝓜 x) :
    (a + b).val = a.val + b.val := by
  induction a, b using Quotient.inductionOn₂' with
  | _ a b =>
    show embedding 𝒜 𝓜 x (a + b) = embedding 𝒜 𝓜 x a + embedding 𝒜 𝓜 x b
    simp only [embedding, num_add, den_add, LocalizedModule.mk_add_mk,
      Submonoid.smul_def, Submonoid.coe_mul]
    exact congrArg (LocalizedModule.mk _) (Subtype.ext rfl)

omit [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 𝓜] in
@[simp]
lemma val_neg (a : HomogeneousLocalizedModule 𝒜 𝓜 x) : (-a).val = -a.val := by
  induction a using Quotient.inductionOn' with
  | _ a =>
    show embedding 𝒜 𝓜 x (-a) = -(embedding 𝒜 𝓜 x a)
    simp [embedding, LocalizedModule.mk_neg]

instance : AddCommGroup (HomogeneousLocalizedModule 𝒜 𝓜 x) where
  add_assoc a b c := ext x (by simp [add_assoc])
  zero_add a := ext x (by simp)
  add_zero a := ext x (by simp)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext x (by simp)
  add_comm a b := ext x (by simp [add_comm])
  sub_eq_add_neg a b := rfl

end AddCommGroup

section Away

variable [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]

/-- The module-level analogue of `HomogeneousLocalization.Away`: the degree-zero part of `M`
localized at powers of a homogeneous element `f`. -/
abbrev Away (𝒜 : ι → Submodule R A) (𝓜 : ι → Submodule R M) (f : A) :=
  HomogeneousLocalizedModule 𝒜 𝓜 (Submonoid.powers f)

end Away

section AtPrime

variable [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]

/-- The degree-zero part of the homogeneous localized module at a prime ideal. This is the
module-level analogue of `HomogeneousLocalization.AtPrime`. -/
abbrev AtPrime (𝒜 : ι → Submodule R A) (𝓜 : ι → Submodule R M) (𝔭 : Ideal A) [𝔭.IsPrime] :=
  HomogeneousLocalizedModule 𝒜 𝓜 𝔭.primeCompl

end AtPrime

section MapId

variable [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

/-- When `P ≤ Q`, the natural group homomorphism from `HomogeneousLocalizedModule 𝒜 𝓜 P`
to `HomogeneousLocalizedModule 𝒜 𝓜 Q`, sending a fraction `m/s` with `s ∈ P` to
`m/s` viewed in the larger localization. This is the module-level analogue of
`HomogeneousLocalization.mapId`. -/
def mapId {P Q : Submonoid A} (h : P ≤ Q) :
    HomogeneousLocalizedModule 𝒜 𝓜 P →+ HomogeneousLocalizedModule 𝒜 𝓜 Q where
  toFun := Quotient.map'
    (fun p => ⟨p.deg, p.num, p.den, h p.den_mem⟩)
    fun p q (e : NumDenSameDeg.embedding 𝒜 𝓜 P p = NumDenSameDeg.embedding 𝒜 𝓜 P q) => by
      change NumDenSameDeg.embedding 𝒜 𝓜 Q _ = NumDenSameDeg.embedding 𝒜 𝓜 Q _
      simp only [NumDenSameDeg.embedding, LocalizedModule.mk_eq] at e ⊢
      obtain ⟨⟨u, hu⟩, e⟩ := e
      exact ⟨⟨u, h hu⟩, e⟩
  map_zero' := rfl
  map_add' a b := Quotient.inductionOn₂' a b fun _ _ => rfl

@[simp]
theorem mapId_mk {P Q : Submonoid A} (h : P ≤ Q) (p : NumDenSameDeg 𝒜 𝓜 P) :
    mapId h (mk p) = mk ⟨p.deg, p.num, p.den, h p.den_mem⟩ := rfl

end MapId

section mapAway

variable [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
variable {e : ι} {f g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g)
variable (𝒜 𝓜)

/-- Maps a representative `⟨d, m, s, hs⟩` of `M⁰_f` (where `f^n = s`) to
`⟨d + n • e, g^n • m, s * g^n, _⟩`, a representative of `M⁰_x` (where `x = f * g`). -/
private def awayMapNumDenSameDeg
    (p : NumDenSameDeg 𝒜 𝓜 (Submonoid.powers f)) :
    NumDenSameDeg 𝒜 𝓜 (Submonoid.powers x) :=
  let n := p.den_mem.choose
  ⟨p.deg + n • e,
    ⟨(g ^ n) • (p.num : M),
      add_comm p.deg (n • e) ▸
        SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n hg) p.num.2⟩,
    ⟨(p.den : A) * g ^ n,
      GradedMul.mul_mem p.den.2 (SetLike.pow_mem_graded n hg)⟩,
    ⟨n, by
      have h : f ^ n = (p.den : A) := p.den_mem.choose_spec
      change x ^ n = (p.den : A) * g ^ n
      rw [hx, mul_pow, h]⟩⟩

private theorem awayMapNumDenSameDeg_respects
    (p q : NumDenSameDeg 𝒜 𝓜 (Submonoid.powers f))
    (h : NumDenSameDeg.embedding 𝒜 𝓜 _ p = NumDenSameDeg.embedding 𝒜 𝓜 _ q) :
    NumDenSameDeg.embedding 𝒜 𝓜 _ (awayMapNumDenSameDeg 𝒜 𝓜 hg hx p) =
    NumDenSameDeg.embedding 𝒜 𝓜 _ (awayMapNumDenSameDeg 𝒜 𝓜 hg hx q) := by
  simp only [NumDenSameDeg.embedding, awayMapNumDenSameDeg, LocalizedModule.mk_eq] at h ⊢
  obtain ⟨⟨_, k, rfl⟩, h⟩ := h
  refine ⟨⟨x ^ k, k, rfl⟩, ?_⟩
  simp only [Submonoid.smul_def, ← mul_smul] at h ⊢
  set np := p.den_mem.choose
  set nq := q.den_mem.choose
  have key₁ : ∀ (a : A) (m : M),
      (x ^ k * (a * g ^ nq * g ^ np)) • m =
      g ^ (k + nq + np) • ((f ^ k * a) • m) := fun a m => by
    simp only [← mul_smul]; congr 1; rw [hx, mul_pow]; ring
  have key₂ : ∀ (a : A) (m : M),
      (x ^ k * (a * g ^ np * g ^ nq)) • m =
      g ^ (k + nq + np) • ((f ^ k * a) • m) := fun a m => by
    simp only [← mul_smul]; congr 1; rw [hx, mul_pow]; ring
  rw [key₁, key₂, h]

/-- The restriction map `M⁰_f → M⁰_x` for `x = f * g` with `g ∈ 𝒜 e`.
Sends `m / f^n` to `g^n • m / x^n`. Module-level analogue of
`HomogeneousLocalization.awayMap`. -/
def awayMap : Away 𝒜 𝓜 f →+ Away 𝒜 𝓜 x where
  toFun := Quotient.map' (awayMapNumDenSameDeg 𝒜 𝓜 hg hx)
    (awayMapNumDenSameDeg_respects 𝒜 𝓜 hg hx)
  map_zero' := by
    change mk (awayMapNumDenSameDeg 𝒜 𝓜 hg hx 0) = 0
    apply val_injective
    simp only [val_mk, val_zero]
    dsimp [awayMapNumDenSameDeg]
    simp [smul_zero, LocalizedModule.zero_mk]
  map_add' a b := by
    induction a, b using Quotient.inductionOn₂' with
    | _ p q =>
      change mk (awayMapNumDenSameDeg 𝒜 𝓜 hg hx (p + q)) =
        mk (awayMapNumDenSameDeg 𝒜 𝓜 hg hx p) + mk (awayMapNumDenSameDeg 𝒜 𝓜 hg hx q)
      rw [← mk_add]
      apply val_injective
      simp only [val_mk, LocalizedModule.mk_add_mk, LocalizedModule.mk_eq,
        awayMapNumDenSameDeg, NumDenSameDeg.num_add, NumDenSameDeg.den_add]
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, smul_add, ← mul_smul]
      congr 1 <;> (congr 1; ring)

@[simp]
lemma awayMap_mk (p : NumDenSameDeg 𝒜 𝓜 (Submonoid.powers f)) :
    awayMap 𝒜 𝓜 hg hx (mk p) = mk (awayMapNumDenSameDeg 𝒜 𝓜 hg hx p) := rfl

lemma val_awayMap_mk (p : NumDenSameDeg 𝒜 𝓜 (Submonoid.powers f)) :
    (awayMap 𝒜 𝓜 hg hx (mk p)).val =
    LocalizedModule.mk ((g ^ p.den_mem.choose : A) • (p.num : M))
      ⟨(p.den : A) * g ^ p.den_mem.choose,
       (Submonoid.mem_powers_iff _ _).mpr ⟨p.den_mem.choose, by
         have h : f ^ p.den_mem.choose = (p.den : A) := p.den_mem.choose_spec
         change x ^ p.den_mem.choose = (p.den : A) * g ^ p.den_mem.choose
         rw [hx, mul_pow, h]⟩⟩ := rfl

variable {d : ι} (hf : f ∈ 𝒜 d)

/-- Convenience constructor for `Away 𝒜 𝓜 f` when `f ∈ 𝒜 d`: the fraction `m / f^n`
where `m ∈ 𝓜 (n • d)`. -/
protected def Away.mk (n : ℕ) (m : M) (hm : m ∈ 𝓜 (n • d)) : Away 𝒜 𝓜 f :=
  HomogeneousLocalizedModule.mk
    ⟨n • d, ⟨m, hm⟩, ⟨f ^ n, SetLike.pow_mem_graded n hf⟩, n, rfl⟩

omit [SetLike.GradedSMul 𝒜 𝓜] in
@[simp]
lemma Away.val_mk (n : ℕ) (m : M) (hm : m ∈ 𝓜 (n • d)) :
    (Away.mk 𝒜 𝓜 hf n m hm).val =
    LocalizedModule.mk m
      ⟨f ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩ := rfl

lemma awayMap_Away_mk (n : ℕ) (m : M) (hm : m ∈ 𝓜 (n • d)) :
    (awayMap 𝒜 𝓜 hg hx (Away.mk 𝒜 𝓜 hf n m hm)).val =
    LocalizedModule.mk ((g ^ n : A) • m)
      ⟨x ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩ := by
  dsimp only [Away.mk, awayMap_mk, val_mk, awayMapNumDenSameDeg]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, ← mul_smul, hx, mul_pow]
  congr 1
  ring

lemma mapId_awayMap {P : Submonoid A} (h₁ : Submonoid.powers f ≤ P)
    (h₂ : Submonoid.powers x ≤ P) (a : Away 𝒜 𝓜 f) :
    mapId h₂ (awayMap 𝒜 𝓜 hg hx a) = mapId h₁ a := by
  induction a using Quotient.inductionOn' with
  | _ p =>
    simp only [awayMap_mk, mapId_mk]
    apply val_injective
    simp only [val_mk]
    dsimp [awayMapNumDenSameDeg]
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, ← mul_smul]

/-- Two `awayMap` double-compositions from the same source to the same target agree,
regardless of the intermediate factorization paths. This is the algebraic analogue
of `TopCat.restriction_comp_congr`: the two paths multiply by two degree-one elements
in different orders, and ring commutativity makes them equal. -/
theorem awayMap_comp_congr {e₁ e₂ e₃ e₄ : ι} {f g₁ g₂ g₃ g₄ : A}
    (hg₁ : g₁ ∈ 𝒜 e₁) (hg₂ : g₂ ∈ 𝒜 e₂)
    (hg₃ : g₃ ∈ 𝒜 e₃) (hg₄ : g₄ ∈ 𝒜 e₄)
    {x₁ x₂ t : A}
    (hx₁ : x₁ = f * g₁) (hx₂ : x₂ = f * g₃)
    (hy₁ : t = x₁ * g₂) (hy₂ : t = x₂ * g₄)
    (a : Away 𝒜 𝓜 f) :
    awayMap 𝒜 𝓜 hg₂ hy₁ (awayMap 𝒜 𝓜 hg₁ hx₁ a) =
    awayMap 𝒜 𝓜 hg₄ hy₂ (awayMap 𝒜 𝓜 hg₃ hx₂ a) := by
  induction a using Quotient.inductionOn' with
  | _ p =>
    simp only [awayMap_mk]
    apply val_injective
    simp only [val_mk]
    dsimp [awayMapNumDenSameDeg]
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, ← mul_smul]
    congr 1
    ring

/-- Variant of `awayMap_comp_congr` that handles a `cast` between
propositionally equal source localization types. -/
theorem awayMap_comp_congr_cast {e₁ e₂ e₃ e₄ : ι}
    {f₁ f₂ g₁ g₂ g₃ g₄ : A}
    (hg₁ : g₁ ∈ 𝒜 e₁) (hg₂ : g₂ ∈ 𝒜 e₂)
    (hg₃ : g₃ ∈ 𝒜 e₃) (hg₄ : g₄ ∈ 𝒜 e₄)
    {x₁ x₂ t : A}
    (hx₁ : x₁ = f₁ * g₁) (hx₂ : x₂ = f₂ * g₃)
    (hy₁ : t = x₁ * g₂) (hy₂ : t = x₂ * g₄)
    (hf : f₁ = f₂)
    (a : Away 𝒜 𝓜 f₁) :
    awayMap 𝒜 𝓜 hg₂ hy₁ (awayMap 𝒜 𝓜 hg₁ hx₁ a) =
    awayMap 𝒜 𝓜 hg₄ hy₂ (awayMap 𝒜 𝓜 hg₃ hx₂
      (cast (congrArg (Away 𝒜 𝓜) hf) a)) := by
  subst hf
  exact awayMap_comp_congr 𝒜 𝓜 hg₁ hg₂ hg₃ hg₄ hx₁ hx₂ hy₁ hy₂ a

/-- Variant of `awayMap_comp_congr` handling a `▸`-transport between
propositionally equal source localization types. The transport goes through
an auxiliary type `α` via a function `F : α → A`, allowing the `▸` to use
`Eq.rec` at the universe level of `α`. -/
theorem awayMap_comp_congr_subst {α : Sort*} {F : α → A}
    {s₁ s₂ : α}
    {e₁ e₂ e₃ e₄ : ι} {g₁ g₂ g₃ g₄ : A}
    (hg₁ : g₁ ∈ 𝒜 e₁) (hg₂ : g₂ ∈ 𝒜 e₂)
    (hg₃ : g₃ ∈ 𝒜 e₃) (hg₄ : g₄ ∈ 𝒜 e₄)
    {x₁ x₂ t : A}
    (hx₁ : x₁ = F s₁ * g₁) (hx₂ : x₂ = F s₂ * g₃)
    (hy₁ : t = x₁ * g₂) (hy₂ : t = x₂ * g₄)
    (hs : s₂ = s₁)
    (a : Away 𝒜 𝓜 (F s₁)) :
    awayMap 𝒜 𝓜 hg₂ hy₁ (awayMap 𝒜 𝓜 hg₁ hx₁ a) =
    awayMap 𝒜 𝓜 hg₄ hy₂ (awayMap 𝒜 𝓜 hg₃ hx₂ (hs ▸ a)) := by
  subst hs
  exact awayMap_comp_congr 𝒜 𝓜 hg₁ hg₂ hg₃ hg₄ hx₁ hx₂ hy₁ hy₂ a

end mapAway

end HomogeneousLocalizedModule
