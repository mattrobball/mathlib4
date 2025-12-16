import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Algebra.Hom
-- import Mathlib.Algebra.Algebra.Subalgebra.Basic

open scoped Classical
open scoped Polynomial


theorem AlgHom.comp_algebraMap_of_tower (R : Type*) {S A B: Type v}
    [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S]
    [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B] [IsScalarTower R S A]
    [IsScalarTower R S B] (f : A →ₐ[S] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B := sorry

-- Algebra instance for polynomials
noncomputable instance {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : Algebra R A[X] where
  smul_def' _ _ := sorry
  commutes' _ _ := sorry
  algebraMap := Polynomial.C.comp (algebraMap R A)

irreducible_def Polynomial.eval₂ {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (p : R[X]) : S :=
  p.sum fun e a => f a * x ^ e

def Polynomial.eval₂RingHom' {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (hf : ∀ (a : R), Commute (f a) x) : Polynomial R →+* S where
  toFun := eval₂ f x
  map_add' _ _ := sorry
  map_zero' := sorry
  map_mul' _ _ := sorry
  map_one' := sorry

def eval₂AlgHom' {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (b : B) (hf : ∀ a, Commute (f a) b) : A[X] →ₐ[R] B where
  toRingHom := Polynomial.eval₂RingHom' f b hf
  commutes' _ := sorry

def Polynomial.aeval {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) : R[X] →ₐ[R] A :=
  eval₂AlgHom' (Algebra.ofId _ _) x (Algebra.commutes · _)

def Polynomial.degree {R : Type*} [Semiring R] (p : R[X]) : WithBot ℕ :=
  p.support.max

theorem Polynomial.degree_lt_wf {R : Type*} [Semiring R] : WellFounded fun p q :
    R[X] => degree p < degree q := sorry

/-- `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. -/
def Polynomial.natDegree {R : Type*} [Semiring R] (p : R[X]) : ℕ :=
  (degree p).unbotD 0

def Polynomial.leadingCoeff {R : Type*} [Semiring R] (p : R[X]) : R :=
  Polynomial.coeff p (natDegree p)

/-- a polynomial is `Monic` if its leading coefficient is 1 -/
def Polynomial.Monic {R : Type*} [Semiring R] (p : R[X]) :=
  leadingCoeff p = (1 : R)

-- Copied from Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
def RingHom.IsIntegralElem {R A : Type*} [CommRing R] [Ring A] (f : R →+* A) (x : A) :=
  ∃ p : R[X], Polynomial.Monic p ∧ Polynomial.eval₂ f x p = 0

def IsIntegral (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x

-- Copied from Mathlib.RingTheory.Algebraic.Defs
def IsAlgebraic (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ Polynomial.aeval x p = 0

protected class Algebra.IsAlgebraic (R A : Type*) [CommRing R] [Ring A] [Algebra R A] : Prop where
  isAlgebraic : ∀ x : A, IsAlgebraic R x

-- Copied from Mathlib.FieldTheory.Minpoly.Basic
open scoped Classical in
noncomputable def minpoly (A : Type*) {B : Type*} [CommRing A] [Ring B] [Algebra A B] (x : B) : A[X] :=
  if hx : IsIntegral A x then Polynomial.degree_lt_wf.min _ hx else 0

namespace minpoly
variable {A B B' : Type*} [CommRing A] [Ring B] [Ring B'] [Algebra A B] [Algebra A B']

theorem algebraMap_eq {C} [CommRing C] [Algebra A C] [Algebra C B'] [IsScalarTower A C B']
    (h : Function.Injective (algebraMap C B')) (x : C) :
    minpoly A (algebraMap C B' x) = minpoly A x := by
  sorry

end minpoly

-- Copied from Mathlib.Algebra.Polynomial.Factors
namespace Polynomial
variable {R : Type*} [CommRing R]
def Splits (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})

noncomputable def map {R : Type*} [Semiring R] [Semiring S] (f : R →+* S): R[X] → S[X] :=
  eval₂ (C.comp f) X

theorem map_map {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
   (f : R →+* S) (g : S →+* T) (p : Polynomial R) : map g (map f p) = map (g.comp f) p := sorry

protected theorem Splits.map {f : R[X]} (hf : Splits f) {S : Type*} [CommRing S] (i : R →+* S) :
    Splits (map i f) := by
  sorry

section Roots
variable [IsDomain R] {p : R[X]}

theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : Monic q) :
    degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) <
    degree p := sorry

noncomputable def divModByMonicAux : ∀ (_p : R[X]) {q : R[X]}, Monic q → R[X] × R[X]
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p
  decreasing_by sorry

noncomputable def modByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

theorem modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p := sorry

noncomputable def decidableDvdMonic [DecidableEq R] (p : R[X]) (hq : Monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)

abbrev FiniteMultiplicity [Monoid α] (a b : α) : Prop := ∃ n : ℕ, ¬a ^ (n + 1) ∣ b

theorem finiteMultiplicity_X_sub_C (a : R) (h0 : p ≠ 0) : FiniteMultiplicity (X - C a) p := by sorry

theorem monic_X_sub_C {R : Type u} [Ring R] (x : R) : (X - C x).Monic := sorry

theorem Monic.pow {R : Type*} [Semiring R] {p : Polynomial R} (hp :
    p.Monic) (n : ℕ) : (p ^ n).Monic := sorry

noncomputable def rootMultiplicity (a : R) (p : R[X]) : ℕ :=
  letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := fun n =>
      have := decidableDvdMonic p ((monic_X_sub_C a).pow (n + 1))
      inferInstanceAs (Decidable ¬_)
    Nat.find (finiteMultiplicity_X_sub_C a h0)

theorem exists_multiset_roots {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {p : Polynomial R} :
    p ≠ 0 → ∃ (s : Multiset R), ↑s.card ≤ p.degree ∧ ∀ (a : R), Multiset.count a
    s = Polynomial.rootMultiplicity a p := sorry

noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)

end Roots

section aroots
variable {T : Type*} [CommRing T]

noncomputable abbrev aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Multiset S :=
  (p.map (algebraMap T S)).roots

def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.aroots S).toFinset

end aroots

end Polynomial

open Polynomial IsScalarTower

-- ===== COPIED INTERMEDIATE FIELD INFRASTRUCTURE =====

structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v
    extends Subsemiring A where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1

instance (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] :
    SetLike (Subalgebra R A) A where
  coe s := s.carrier
  coe_injective' p q h := sorry

variable (R : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

def Subalgebra.adjoin (s : Set A) : Subalgebra R A where
  toSubsemiring := Subsemiring.closure (Set.range (algebraMap R A) ∪ s)
  algebraMap_mem' := sorry

variable {R} in
protected def Subalgebra.copy (S : Subalgebra R A) (s : Set A) (hs : s = S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }

variable {R}

protected def Subalgebra.gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s sorry
  gc := sorry
  le_l_u S := sorry
  choice_eq _ _ := sorry

instance : CompleteLattice (Subalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice Subalgebra.gi
  bot := { toSubsemiring := Subsemiring.closure (Set.range (algebraMap R A))
           algebraMap_mem' := sorry }
  bot_le _ := sorry

def Algebra.adjoin (R : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (s : Set A) :
    Subalgebra R A :=
  { Subsemiring.closure (Set.range (algebraMap R A) ∪ s) with
    algebraMap_mem' := sorry }

protected def Algebra.gi {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
    GaloisInsertion (Algebra.adjoin R : Set A → Subalgebra R A) (↑) where
  choice s hs := (Algebra.adjoin R s).copy s sorry
  gc := sorry
  le_l_u S := sorry
  choice_eq _ _ := sorry

def _root_.AlgHom.range {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    (φ : A →ₐ[R] B) : Subalgebra R B :=
   { φ.toRingHom.rangeS with algebraMap_mem' := sorry }

instance {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : CompleteLattice (Subalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice Algebra.gi
  bot := (Algebra.ofId R A).range
  bot_le _S := sorry

instance Subalgebra.instSubsemiringClass {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
    SubsemiringClass (Subalgebra R A) A where
  add_mem {s} := sorry
  mul_mem {s} := sorry
  one_mem {s} := sorry
  zero_mem {s} := sorry

-- Field instance for IntermediateField
-- instance (S : IntermediateField K L) : Field S :=
--   Subfield.toField S.toSubfield

instance toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) :
    Semiring S :=
  S.toSubsemiring.toSemiring

instance toCommSemiring {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) :
    CommSemiring S :=
  S.toSubsemiring.toCommSemiring

-- instance toRing {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) : Ring S :=
--   S.toSubring.toRing
--
-- instance toCommRing {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
--     CommRing S :=
--   S.toSubring.toCommRing


def Subalgebra.toSubmodule {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
    Subalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := sorry }
      inj' := sorry }
  map_rel_iff' := sorry

instance (priority := low) Subalgebra.module' {R' R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    Module R' S :=
  S.toSubmodule.module'

instance {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) : Module R S :=
  S.module'

instance {R' R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    IsScalarTower R' R S := sorry

instance (priority := 500) algebra' {R' : Type u'}  {R : Type u}  {A : Type v}
  [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A)
  [CommSemiring R'] [SMul R' R] [Algebra R' A]  [IsScalarTower R' R A] :
    Algebra R' S where
  algebraMap := (algebraMap R' A).codRestrict S sorry
  commutes' := sorry
  smul_def' := sorry

instance Subalgebra.algebra {R : Type u}  {A : Type v} [CommSemiring R]
  [Semiring A] [Algebra R A] (S : Subalgebra R A) : Algebra R S := sorry

def Subalgebra.inclusion {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {S T : Subalgebra R A}  (h : S ≤ T) : S →ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := sorry
  map_add' _ _ := sorry
  map_mul' _ _ := sorry
  map_zero' := sorry
  commutes' _ := sorry

/-- `S : IntermediateField K L` is a subset of `L` such that there is a field tower `L / S / K`. -/
structure IntermediateField (K L : Type*) [Field K] [Field L] [Algebra K L] extends Subalgebra K L where
  inv_mem' : ∀ x ∈ toSubalgebra.toSubsemiring.carrier, x⁻¹ ∈ toSubalgebra.toSubsemiring.carrier

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance : SetLike (IntermediateField K L) L :=
  ⟨fun S => S.toSubalgebra.toSubsemiring.carrier, by rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; sorry⟩

def toSubfield (S : IntermediateField K L) : Subfield L where
  carrier := S.toSubalgebra.toSubsemiring.carrier
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry
  inv_mem' := sorry

instance : SubfieldClass (IntermediateField K L) L where
  add_mem {s} := sorry
  zero_mem {s} := sorry
  neg_mem {s} hx := sorry
  mul_mem {s} := sorry
  one_mem {s} := sorry
  inv_mem {s} := sorry

protected def copy (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : IntermediateField K L where
  toSubalgebra := S.toSubalgebra.copy s hs
  inv_mem' := sorry

theorem copy_eq (S : IntermediateField K L) (s : Set L) (hs : s = ↑S) : S.copy s hs = S := by
  sorry

-- adjoin function (K explicit for compatibility with theorem)
def adjoin (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) : IntermediateField K L where
  toSubalgebra := { toSubsemiring := (Subfield.closure (Set.range (algebraMap K L) ∪ S)).toSubring.toSubsemiring
                    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }
  inv_mem' := sorry

theorem adjoin_le_iff {K L : Type*} [Field K] [Field L] [Algebra K L] {S : Set L} {T : IntermediateField K L} :
    adjoin K S ≤ T ↔ S ⊆ T := by
  sorry

theorem gc {K L : Type*} [Field K] [Field L] [Algebra K L] :
    GaloisConnection (adjoin K : Set L → IntermediateField K L)
    (fun (x : IntermediateField K L) => (x : Set L)) := by
  sorry

def gi {K L : Type*} [Field K] [Field L] [Algebra K L] :
    GaloisInsertion (adjoin K : Set L → IntermediateField K L)
    (fun (x : IntermediateField K L) => (x : Set L)) where
  choice s hs := (adjoin K s).copy s <| le_antisymm (gc.le_u_l s) hs
  gc := sorry
  le_l_u S := sorry
  choice_eq _ _ := sorry

instance : CompleteLattice (IntermediateField K L) where
  __ := GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot := { toSubalgebra := ⊥
           inv_mem' := sorry }
  bot_le x := sorry


-- Algebra instances
instance (S : IntermediateField K L) : Algebra K S :=
  S.toSubalgebra.algebra

-- instance (S₁ S₂ : IntermediateField K L) : Algebra S₁ S₂ :=
--   Subalgebra.algebra (S₁.toSubalgebra.inclusion (by simp [SetLike.coe_subset_coe]))

-- instance (S : IntermediateField K L) : Algebra S L where
--   algebraMap := { toFun := fun x => x.val,
--                    map_one' := rfl,
--                    map_mul' := fun _ _ => rfl,
--                    map_zero' := rfl,
--                    map_add' := fun _ _ => rfl }
--   commutes' := sorry
--   smul_def' := sorry

-- IsScalarTower instances
-- instance (S : IntermediateField K L) : IsScalarTower K S L where
--   smul_assoc := sorry

-- inclusion function
def inclusion {E F : IntermediateField K L} (hEF : E ≤ F) : E →ₐ[K] F :=
  Subalgebra.inclusion hEF

end IntermediateField

namespace IntermediateField

end IntermediateField

-- ===== END COPIED INFRASTRUCTURE =====

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

-- Copy of Normal class from Mathlib.FieldTheory.Normal.Defs
class Normal : Prop extends Algebra.IsAlgebraic F K where
  splits' (x : K) : Splits ((minpoly F x).map (algebraMap F K))

theorem Normal.splits {F K : Type*} [Field F] [Field K] [Algebra F K] (_ : Normal F K) (x : K) :
    Splits ((minpoly F x).map (algebraMap F K)) := by
  sorry

variable {F}

namespace IntermediateField

-- Copied from Mathlib.FieldTheory.IntermediateField.Algebraic
theorem minpoly_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    {S : IntermediateField F E} (x : S) : minpoly F x = minpoly F (x : E) := by
  sorry

-- Copied from Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
theorem exists_finset_of_mem_supr'' {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι : Type*} {f : ι → IntermediateField F E}
    (h : ∀ i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
    ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, IntermediateField.adjoin F ((minpoly F (i.2 :)).rootSet E) := by
  sorry

set_option trace.profiler true in
theorem normal_iSup {F K : Type*} [Field F] [Field K] [Algebra F K]
    {ι : Type*} (t : ι → IntermediateField F K) [h : ∀ i,
  Normal F (t i)] (x : (⨆ i, t i : IntermediateField _ _)) :
    (Polynomial.map (algebraMap F ↥(⨆ i, t i)) (minpoly F x)).Splits := by
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (fun i => (h i).1) x.2
  let E : IntermediateField F K := ⨆ i ∈ s, adjoin F ((minpoly F i.2).rootSet K)
  have hF : Normal F E := by sorry
  have hE : E ≤ ⨆ i, t i := by sorry
  have := hF.splits ⟨x, hx⟩
  rw [minpoly_eq, Subtype.coe_mk, ← minpoly_eq] at this
  have := this.map (inclusion hE).toRingHom
  have that := this
  simp only [AlgHom.toRingHom_eq_coe, Polynomial.map_map] at this
  rwa [Splits.map_map] at that

end IntermediateField
