/-
Copyright (c) 2025 Matt Diamond. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Diamond
-/
import Mathlib.Topology.Sheaves.CechCochainComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Relative Simplex Cochain Complex

Given a finite set `V = Fin (n + 1)`, a subset `T ⊆ V`, and an abelian group `R`, we construct
the **relative simplex cochain complex** `K_T`. In degree `p`, the cochains are functions from
`(p + 1)`-element subsets of `V` containing `T` to `R`, with the alternating face differential.

The main result is that this complex is acyclic when `T` is nonempty and proper
(`∅ ⊊ T ⊊ V`), via an explicit contracting homotopy. This is the combinatorial core of the
computation of Čech cohomology for O(d) on projective space (Stacks 01XS).

## Main definitions

* `relSimplexCochain T R p`: cochains of the relative simplex complex.
* `relSimplexδ T R p`: the coboundary map.
* `relSimplexComplex T R`: the cochain complex.
* `relSimplexHomotopy T v hv R p`: the contracting homotopy for `v ∉ T`.

## Main results

* `relSimplexδ_comp_eq_zero`: `d² = 0`.
* `relSimplexHomotopy_eq`: the homotopy equation `δ ∘ h + h ∘ δ = id`.
* `relSimplexComplex_acyclic`: the complex is acyclic for `T.Nonempty` and `T ≠ Finset.univ`.
* `relSimplexComplex_empty_exactAt`: exact at positive degrees when `T = ∅`.
* `relSimplexComplex_univ_exactAt`: exact at degree `p ≠ n` when `T = Finset.univ`.

## References

* [Stacks Project, Tag 01XS](https://stacks.math.columbia.edu/tag/01XS)
-/

open Finset TopCat CategoryTheory CategoryTheory.Limits

variable {n p : ℕ}

/-! ### Cochains and differential -/

/-- Cochains of the relative simplex complex: functions from `(p + 1)`-element subsets
of `Fin (n + 1)` containing `T` to an abelian group `R`. -/
abbrev relSimplexCochain (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R] (p : ℕ) :=
  ∀ _S : { S : Finset (Fin (n + 1)) // S.card = p + 1 ∧ T ⊆ S }, R

/-- The coboundary map of the relative simplex complex: alternating signed face map,
restricted to faces containing `T`. -/
def relSimplexδ (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R] (p : ℕ)
    (f : relSimplexCochain T R p) : relSimplexCochain T R (p + 1) :=
  fun S =>
    ∑ j : Fin (p + 2),
      if h : T ⊆ (eraseNth S.1 S.2.1 j).1
      then (-1 : ℤ) ^ (j : ℕ) •
        f ⟨(eraseNth S.1 S.2.1 j).1, (eraseNth S.1 S.2.1 j).2, h⟩
      else 0

@[simp]
theorem relSimplexδ_apply (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R]
    (p : ℕ) (f : relSimplexCochain T R p)
    (S : { S : Finset (Fin (n + 1)) // S.card = p + 2 ∧ T ⊆ S }) :
    relSimplexδ T R p f S =
      ∑ j : Fin (p + 2),
        if h : T ⊆ (eraseNth S.1 S.2.1 j).1
        then (-1 : ℤ) ^ (j : ℕ) •
          f ⟨(eraseNth S.1 S.2.1 j).1, (eraseNth S.1 S.2.1 j).2, h⟩
        else 0 := rfl

theorem relSimplexδ_map_zero (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R]
    (p : ℕ) : relSimplexδ T R p 0 = 0 := by
  ext S
  simp only [relSimplexδ, Pi.zero_apply]
  exact Finset.sum_eq_zero (fun j _ => by split_ifs <;> simp)

theorem relSimplexδ_map_add (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R]
    (p : ℕ) (f g : relSimplexCochain T R p) :
    relSimplexδ T R p (f + g) = relSimplexδ T R p f + relSimplexδ T R p g := by
  ext S
  simp only [relSimplexδ, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1; ext j
  split_ifs with h
  · rw [smul_add]
  · rw [add_zero]

/-- The coboundary as a group homomorphism. -/
def relSimplexδHom (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R] (p : ℕ) :
    relSimplexCochain T R p →+ relSimplexCochain T R (p + 1) where
  toFun := relSimplexδ T R p
  map_zero' := relSimplexδ_map_zero T R p
  map_add' := relSimplexδ_map_add T R p

/-! ### d² = 0 -/

/-- The double-erased set is a subset of the single-erased set. -/
private theorem eraseNth_eraseNth_subset {W : Finset (Fin (n + 1))} {p : ℕ}
    (hW : W.card = p + 3) (j : Fin (p + 3)) (k : Fin (p + 2)) :
    (eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).1 ⊆ (eraseNth W hW j).1 := by
  simp only [eraseNth]; exact erase_subset _ _

/-- `d² = 0` for the relative simplex complex. -/
theorem relSimplexδ_comp_eq_zero (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R]
    (p : ℕ) (f : relSimplexCochain T R p) :
    relSimplexδ T R (p + 1) (relSimplexδ T R p f) = 0 := by
  funext ⟨W, hW, hT_W⟩
  simp only [Pi.zero_apply]
  -- Unfold relSimplexδ and simplify; no match issues since def avoids pattern matching
  show ∑ j : Fin (p + 3),
    (if h : T ⊆ (eraseNth W hW j).1
    then (-1 : ℤ) ^ j.val •
      ∑ k : Fin (p + 2),
        (if hk : T ⊆ (eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).1
        then (-1 : ℤ) ^ k.val •
          f ⟨(eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).1,
            (eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).2, hk⟩
        else 0)
    else 0) = 0
  -- Transform: distribute smul, merge outer dite, combine scalars
  have transform : ∀ j : Fin (p + 3),
      (if hj : T ⊆ (eraseNth W hW j).1 then
        (-1 : ℤ) ^ j.val •
          ∑ k : Fin (p + 2),
            (if hk : T ⊆ (eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).1
            then (-1 : ℤ) ^ k.val •
              f ⟨(eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).1,
                (eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).2, hk⟩
            else 0)
      else 0) =
      ∑ k : Fin (p + 2),
        (if hk : T ⊆ (eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).1
        then ((-1 : ℤ) ^ j.val * (-1 : ℤ) ^ k.val) •
          f ⟨(eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).1,
            (eraseNth (eraseNth W hW j).1 (eraseNth W hW j).2 k).2, hk⟩
        else 0) := fun j => by
    split_ifs with hj
    · rw [Finset.smul_sum]; congr 1; ext k
      split_ifs with hk
      · rw [smul_smul]
      · rw [smul_zero]
    · exact (Finset.sum_eq_zero fun k _ =>
        dif_neg fun hk => hj (hk.trans (eraseNth_eraseNth_subset hW j k))).symm
  rw [Finset.sum_congr rfl (fun j _ => transform j)]
  -- Convert double sum to sum over pairs
  rw [← Finset.sum_product']
  -- Apply sign-reversing involution
  apply Finset.sum_ninvolution (cechInvolution p)
  · -- Paired terms cancel
    intro jk
    have hval : (eraseNth (eraseNth W hW (cechInvolution p jk).1).1
          (eraseNth W hW (cechInvolution p jk).1).2 (cechInvolution p jk).2).1 =
        (eraseNth (eraseNth W hW jk.1).1 (eraseNth W hW jk.1).2 jk.2).1 :=
      eraseNth_eraseNth_involution p W hW jk
    rw [cechInvolution_sign]
    split_ifs with h1 h2 h2
    · -- Both branches active; f values agree since double-erased sets are equal
      have feq : f ⟨(eraseNth (eraseNth W hW (cechInvolution p jk).1).1
            (eraseNth W hW (cechInvolution p jk).1).2 (cechInvolution p jk).2).1,
          (eraseNth (eraseNth W hW (cechInvolution p jk).1).1
            (eraseNth W hW (cechInvolution p jk).1).2 (cechInvolution p jk).2).2, h2⟩ =
        f ⟨(eraseNth (eraseNth W hW jk.1).1
            (eraseNth W hW jk.1).2 jk.2).1,
          (eraseNth (eraseNth W hW jk.1).1
            (eraseNth W hW jk.1).2 jk.2).2, h1⟩ := by
        congr 1; exact Subtype.ext hval
      rw [neg_smul, feq, add_neg_cancel]
    · exact absurd (hval ▸ h1) h2
    · exact absurd (hval.symm ▸ h2) h1
    · simp
  · intro jk _; exact cechInvolution_ne p jk
  · intro _; exact Finset.mem_univ _
  · exact cechInvolution_involutive p

/-! ### The cochain complex -/

/-- The relative simplex cochain complex. In degree `p`, the cochains are functions from
`(p + 1)`-element subsets of `Fin (n + 1)` containing `T` to `R`. -/
def relSimplexComplex (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R] :
    CochainComplex AddCommGrp ℕ :=
  CochainComplex.of
    (fun p => AddCommGrp.of (relSimplexCochain T R p))
    (fun p => AddCommGrp.ofHom (relSimplexδHom T R p))
    (fun p => AddCommGrp.ext (relSimplexδ_comp_eq_zero T R p))

/-! ### Insertion infrastructure -/

/-- The position of `v` when inserted into a finset `U`: the number of
elements of `U` less than `v`. -/
def insertPos (U : Finset (Fin (n + 1))) (v : Fin (n + 1)) : ℕ :=
  (U.filter (· < v)).card

/-- `insertPos` is bounded by the cardinality of `U`. -/
theorem insertPos_le_card (U : Finset (Fin (n + 1))) (v : Fin (n + 1)) :
    insertPos U v ≤ U.card :=
  card_filter_le U _

/-- The position of `v` in a finset `S` containing `v`, via `orderIsoOfFin`. -/
def findPos (S : Finset (Fin (n + 1))) (hS : S.card = p + 1) (v : Fin (n + 1))
    (hv : v ∈ S) : Fin (p + 1) :=
  (S.orderIsoOfFin hS).symm ⟨v, hv⟩

theorem nthElem_findPos (S : Finset (Fin (n + 1))) (hS : S.card = p + 1)
    (v : Fin (n + 1)) (hv : v ∈ S) :
    nthElem S hS (findPos S hS v hv) = v := by
  simp only [findPos, nthElem]
  exact congr_arg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨v, hv⟩)

theorem eraseNth_findPos_val (S : Finset (Fin (n + 1))) (hS : S.card = p + 1)
    (v : Fin (n + 1)) (hv : v ∈ S) :
    (eraseNth S hS (findPos S hS v hv)).1 = S.erase v := by
  simp only [eraseNth, nthElem_findPos]

theorem v_not_mem_eraseNth_findPos (S : Finset (Fin (n + 1))) (hS : S.card = p + 1)
    (v : Fin (n + 1)) (hv : v ∈ S) :
    v ∉ (eraseNth S hS (findPos S hS v hv)).1 := by
  rw [eraseNth_findPos_val]; exact Finset.notMem_erase v S

/-- Inserting `v` into `eraseNth S j` gives `S` when `nthElem S j = v`. -/
theorem insert_eraseNth_eq {v : Fin (n + 1)} (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 1) (j : Fin (p + 1)) (hv : nthElem S hS j = v) :
    insert v (eraseNth S hS j).1 = S := by
  simp only [eraseNth, ← hv]; exact insert_erase (nthElem_mem S hS j)

/-- `v` is not in `eraseNth S j` when `nthElem S j = v`. -/
theorem v_not_mem_eraseNth_of_nthElem {v : Fin (n + 1)} (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 1) (j : Fin (p + 1)) (hv : nthElem S hS j = v) :
    v ∉ (eraseNth S hS j).1 := by
  simp only [eraseNth, ← hv]; exact Finset.notMem_erase _ _

/-- When `v ∈ S` and we erase `j ≠ findPos v`, then `v` is still in the result. -/
theorem v_mem_eraseNth_of_ne_findPos (S : Finset (Fin (n + 1))) (hS : S.card = p + 2)
    (v : Fin (n + 1)) (hv : v ∈ S) (j : Fin (p + 2))
    (hj : j ≠ findPos S hS v hv) : v ∈ (eraseNth S hS j).1 := by
  simp only [eraseNth]
  refine mem_erase_of_ne_of_mem ?_ hv
  intro heq
  apply hj
  have h1 : nthElem S hS j = v := heq.symm
  have h2 : nthElem S hS (findPos S hS v hv) = v := nthElem_findPos S hS v hv
  exact (S.orderIsoOfFin hS).injective (Subtype.val_injective (h1.trans h2.symm))

/-- `T ⊆ S.erase v` when `T ⊆ S` and `v ∉ T`. -/
theorem subset_erase_of_not_mem {T S : Finset (Fin (n + 1))} {v : Fin (n + 1)}
    (hTS : T ⊆ S) (hv : v ∉ T) : T ⊆ S.erase v :=
  fun _ hx => mem_erase_of_ne_of_mem (ne_of_mem_of_not_mem hx hv) (hTS hx)

/-- `insertPos (S.erase v) v = (findPos S hS v hv).val`: the number of elements of `S`
less than `v` equals the sorted position of `v` in `S`. -/
theorem insertPos_erase_eq_findPos_val (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 1) (v : Fin (n + 1)) (hv : v ∈ S) :
    insertPos (S.erase v) v = (findPos S hS v hv).val := by
  simp only [insertPos, findPos]
  -- Elements of S.erase v that are < v equal elements of S that are < v
  have filter_eq : (S.erase v).filter (· < v) = S.filter (· < v) := by
    ext x; simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hxS⟩, hxv⟩; exact ⟨hxS, hxv⟩
    · rintro ⟨hxS, hxv⟩; exact ⟨⟨ne_of_lt hxv, hxS⟩, hxv⟩
  rw [filter_eq]
  -- The number of elements of S less than v = position of v in sorted S
  -- Use orderIsoOfFin.symm as a bijection from S.filter (· < v) to Finset.range i
  set φ := S.orderIsoOfFin hS
  set i := φ.symm ⟨v, hv⟩
  suffices (S.filter (· < v)).card = (Finset.range i.val).card by
    rwa [Finset.card_range] at this
  apply Finset.card_bij (fun x hx => (φ.symm ⟨x, (mem_filter.mp hx).1⟩).val)
  · -- x ∈ S.filter (· < v) implies φ.symm(x) ∈ range i
    intro x hx
    simp only [mem_filter, Finset.mem_range] at hx ⊢
    exact φ.symm.strictMono (show (⟨x, hx.1⟩ : ↥S) < ⟨v, hv⟩ from hx.2)
  · -- injective
    intro x₁ hx₁ x₂ hx₂ h
    exact congrArg Subtype.val
      (φ.symm.injective (Fin.val_injective h))
  · -- surjective: for j ∈ range i, (φ j).val ∈ S.filter (· < v)
    intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨(φ ⟨j, by omega⟩).val, ?_, ?_⟩
    · simp only [mem_filter]
      refine ⟨(φ ⟨j, by omega⟩).property, ?_⟩
      have h1 : (⟨j, by omega⟩ : Fin (p + 1)) < i := hj
      have h2 := φ.strictMono h1
      rwa [φ.apply_symm_apply] at h2
    · simp [OrderIso.symm_apply_apply]

/-! ### The contracting homotopy -/

/-- The contracting homotopy for the relative simplex complex.
Fix `v ∉ T`. For a `(p + 1)`-cochain `f` and a `p`-cochain position `U` with `T ⊆ U`:
* `(h f)_U = (-1)^{insertPos U v} • f_{U ∪ {v}}` when `v ∉ U`
* `(h f)_U = 0` when `v ∈ U` -/
def relSimplexHomotopy (T : Finset (Fin (n + 1))) (v : Fin (n + 1)) (_hv : v ∉ T)
    (R : Type*) [AddCommGroup R] (p : ℕ)
    (f : relSimplexCochain T R (p + 1)) : relSimplexCochain T R p :=
  fun ⟨U, hU_card, hT_U⟩ =>
    if hv_U : v ∈ U then 0
    else
      have hIns : (insert v U).card = p + 2 := by
        rw [Finset.card_insert_of_notMem hv_U, hU_card]
      have hT_ins : T ⊆ insert v U := hT_U.trans (subset_insert v U)
      (-1 : ℤ) ^ insertPos U v • f ⟨insert v U, hIns, hT_ins⟩

theorem relSimplexHomotopy_map_zero (T : Finset (Fin (n + 1))) (v : Fin (n + 1))
    (hv : v ∉ T) (R : Type*) [AddCommGroup R] (p : ℕ) :
    relSimplexHomotopy T v hv R p 0 = 0 := by
  ext ⟨U, hU_card, hT_U⟩
  simp only [relSimplexHomotopy, Pi.zero_apply]
  split_ifs <;> simp

theorem relSimplexHomotopy_map_add (T : Finset (Fin (n + 1))) (v : Fin (n + 1))
    (hv : v ∉ T) (R : Type*) [AddCommGroup R] (p : ℕ)
    (f g : relSimplexCochain T R (p + 1)) :
    relSimplexHomotopy T v hv R p (f + g) =
      relSimplexHomotopy T v hv R p f + relSimplexHomotopy T v hv R p g := by
  ext ⟨U, hU_card, hT_U⟩
  simp only [relSimplexHomotopy, Pi.add_apply]
  split_ifs with hv_U
  · simp
  · rw [smul_add]

/-- The contracting homotopy as a group homomorphism. -/
def relSimplexHomotopyHom (T : Finset (Fin (n + 1))) (v : Fin (n + 1)) (hv : v ∉ T)
    (R : Type*) [AddCommGroup R] (p : ℕ) :
    relSimplexCochain T R (p + 1) →+ relSimplexCochain T R p where
  toFun := relSimplexHomotopy T v hv R p
  map_zero' := relSimplexHomotopy_map_zero T v hv R p
  map_add' := relSimplexHomotopy_map_add T v hv R p

/-! ### Helper lemmas for the homotopy equation -/

/-- `v` is not in `eraseNth S j` when `v ∉ S`. -/
private theorem v_not_mem_eraseNth_of_not_mem (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 2) (v : Fin (n + 1)) (hv : v ∉ S) (j : Fin (p + 2)) :
    v ∉ (eraseNth S hS j).1 :=
  fun h => hv (erase_subset _ _ h)

/-- `nthElem` depends only on the finset, not on the card proof. -/
private theorem nthElem_congr {S₁ S₂ : Finset (Fin (n + 1))} {m : ℕ}
    {h₁ : S₁.card = m} {h₂ : S₂.card = m} (heq : S₁ = S₂) (k : Fin m) :
    nthElem S₁ h₁ k = nthElem S₂ h₂ k := by subst heq; rfl

/-- `nthElem` of `insert v S` at a `succAbove`-shifted position equals `nthElem` of `S`. -/
private theorem nthElem_insert_succAbove (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 2) (v : Fin (n + 1)) (hv : v ∉ S)
    (hS' : (insert v S).card = p + 3)
    (l : Fin (p + 3)) (hl : nthElem (insert v S) hS' l = v)
    (j : Fin (p + 2)) :
    nthElem (insert v S) hS' (l.succAbove j) = nthElem S hS j := by
  have h_el : (eraseNth (insert v S) hS' l).1 = S := by
    simp only [eraseNth, hl]; exact Finset.erase_insert hv
  have h_nth : ∀ k : Fin (p + 2),
      nthElem (eraseNth (insert v S) hS' l).1 (eraseNth (insert v S) hS' l).2 k =
      nthElem S hS k :=
    fun k => nthElem_congr h_el k
  by_cases hjl : j.val < l.val
  · -- j < l: succAbove gives castSucc
    have h := nthElem_eraseNth_lt (insert v S) hS' l j hjl
    rw [← h_nth j, h]; congr 1
    exact Fin.ext (by simp [Fin.succAbove,
      show j.castSucc < l from by exact_mod_cast hjl])
  · -- j ≥ l: succAbove gives succ
    push_neg at hjl
    have h := nthElem_eraseNth_ge (insert v S) hS' l j hjl
    rw [← h_nth j, h]; congr 1
    exact Fin.ext (by simp [Fin.succAbove,
      show ¬(j.castSucc < l) from by exact_mod_cast not_lt.mpr hjl])

/-- `eraseNth` of `insert v S` at a `succAbove`-shifted position gives
`insert v (eraseNth S j)`. -/
private theorem eraseNth_insert_succAbove (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 2) (v : Fin (n + 1)) (hv : v ∉ S)
    (hS' : (insert v S).card = p + 3)
    (l : Fin (p + 3)) (hl : nthElem (insert v S) hS' l = v)
    (j : Fin (p + 2)) :
    (eraseNth (insert v S) hS' (l.succAbove j)).1 = insert v (eraseNth S hS j).1 := by
  simp only [eraseNth, nthElem_insert_succAbove S hS v hv hS' l hl j]
  have hne : nthElem S hS j ≠ v := fun h => hv (h ▸ nthElem_mem S hS j)
  exact Finset.erase_insert_of_ne hne.symm


/-- `insertPos` of `eraseNth S j` when `nthElem S j < v`. -/
private theorem insertPos_eraseNth_lt (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 2) (v : Fin (n + 1)) (_hv : v ∉ S)
    (j : Fin (p + 2)) (hjv : nthElem S hS j < v) :
    insertPos (eraseNth S hS j).1 v = insertPos S v - 1 := by
  simp only [insertPos, eraseNth]
  rw [Finset.filter_erase, Finset.card_erase_of_mem]
  exact mem_filter.mpr ⟨nthElem_mem S hS j, hjv⟩

/-- `insertPos` of `eraseNth S j` when `v < nthElem S j`. -/
private theorem insertPos_eraseNth_ge (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 2) (v : Fin (n + 1)) (_hv : v ∉ S)
    (j : Fin (p + 2)) (hjv : v < nthElem S hS j) :
    insertPos (eraseNth S hS j).1 v = insertPos S v := by
  simp only [insertPos, eraseNth]
  rw [Finset.filter_erase]
  have hmem : nthElem S hS j ∉ S.filter (· < v) :=
    fun h => not_lt.mpr (le_of_lt hjv) (mem_filter.mp h).2
  rw [Finset.erase_eq_of_notMem hmem]

/-- `nthElem S j < v` when `j.val < insertPos S v` and `v ∉ S`. -/
private theorem nthElem_lt_of_lt_insertPos (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 2) (v : Fin (n + 1)) (hv : v ∉ S)
    (j : Fin (p + 2)) (hj : j.val < insertPos S v) :
    nthElem S hS j < v := by
  by_contra h; push_neg at h
  have hne : v ≠ nthElem S hS j := fun heq => hv (heq ▸ nthElem_mem S hS j)
  have hvj : v < nthElem S hS j := lt_of_le_of_ne h hne
  -- Elements at positions ≥ j are ≥ nthElem S j > v, so not in S.filter (· < v)
  -- Thus S.filter (· < v) ⊆ image of {k | k < j} under nthElem, giving ≤ j elements
  suffices insertPos S v ≤ j.val by omega
  set φ := S.orderIsoOfFin hS
  show (S.filter (· < v)).card ≤ j.val
  calc (S.filter (· < v)).card
      ≤ ((Finset.Iio j).image (fun k => (φ k).val)).card := by
        apply Finset.card_le_card; intro x hx
        obtain ⟨hxS, hxv⟩ := Finset.mem_filter.mp hx
        rw [Finset.mem_image]
        refine ⟨φ.symm ⟨x, hxS⟩, Finset.mem_Iio.mpr ?_, ?_⟩
        · by_contra hge; push_neg at hge
          have h1 := φ.monotone hge
          rw [φ.apply_symm_apply] at h1
          exact absurd hxv (not_lt.mpr (le_trans (le_of_lt hvj) h1))
        · exact congrArg Subtype.val (φ.apply_symm_apply ⟨x, hxS⟩)
    _ ≤ (Finset.Iio j).card := Finset.card_image_le
    _ = j.val := Fin.card_Iio j

/-- `v < nthElem S j` when `insertPos S v ≤ j.val` and `v ∉ S`. -/
private theorem nthElem_gt_of_ge_insertPos (S : Finset (Fin (n + 1)))
    (hS : S.card = p + 2) (v : Fin (n + 1)) (hv : v ∉ S)
    (j : Fin (p + 2)) (hj : insertPos S v ≤ j.val) :
    v < nthElem S hS j := by
  by_contra h; push_neg at h
  have hne : nthElem S hS j ≠ v := fun heq => hv (heq ▸ nthElem_mem S hS j)
  have hjv : nthElem S hS j < v := lt_of_le_of_ne h hne
  -- Elements at positions ≤ j are ≤ nthElem S j < v, giving j+1 elements in S.filter (· < v)
  suffices j.val < insertPos S v by omega
  set φ := S.orderIsoOfFin hS
  show j.val + 1 ≤ (S.filter (· < v)).card
  calc j.val + 1 = (Finset.Iic j).card := (Fin.card_Iic j).symm
    _ = ((Finset.Iic j).image (fun k => (φ k).val)).card := by
        rw [Finset.card_image_of_injOn]; intro k₁ _ k₂ _ heq
        exact φ.injective (Subtype.val_injective heq)
    _ ≤ (S.filter (· < v)).card := by
        apply Finset.card_le_card; intro x hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨(φ k).property,
          lt_of_le_of_lt (φ.monotone (Finset.mem_Iic.mp hk)) hjv⟩

/-! ### The homotopy equation: δ ∘ h + h ∘ δ = id -/

/-- The homotopy equation `δ ∘ h + h ∘ δ = id` for the relative simplex complex.

For `v ∉ T`, the contracting homotopy `h` and coboundary `δ` satisfy
`δ_{p-1} ∘ h_p + h_{p+1} ∘ δ_p = id` on `p`-cochains. -/
theorem relSimplexHomotopy_eq (T : Finset (Fin (n + 1))) (v : Fin (n + 1)) (hv : v ∉ T)
    (R : Type*) [AddCommGroup R] (p : ℕ)
    (f : relSimplexCochain T R (p + 1))
    (S : { S : Finset (Fin (n + 1)) // S.card = p + 2 ∧ T ⊆ S }) :
    relSimplexδ T R p (relSimplexHomotopy T v hv R p f) S +
    relSimplexHomotopy T v hv R (p + 1) (relSimplexδ T R (p + 1) f) S =
    f S := by
  obtain ⟨S, hS, hT_S⟩ := S
  by_cases hv_S : v ∈ S
  · -- Case v ∈ S: (hδ)(f)_S = 0 since v ∈ S, and (δh)(f)_S = f_S
    -- The (hδ) term vanishes because v ∈ S
    have hd_zero : relSimplexHomotopy T v hv R (p + 1) (relSimplexδ T R (p + 1) f)
        ⟨S, hS, hT_S⟩ = 0 :=
      dif_pos hv_S
    rw [hd_zero, add_zero]
    -- (δh)(f)_S: unfold δ to a sum, then pick out the unique nonzero term
    set j₀ := findPos S hS v hv_S
    show relSimplexδ T R p (relSimplexHomotopy T v hv R p f) ⟨S, hS, hT_S⟩ = f ⟨S, hS, hT_S⟩
    rw [show (⟨S, hS, hT_S⟩ : { S : Finset (Fin (n + 1)) // S.card = p + 2 ∧ T ⊆ S }) =
      ⟨S, ⟨hS, hT_S⟩⟩ from rfl]
    rw [relSimplexδ_apply]
    -- Sum over faces: only j₀ = findPos(S, v) survives. First prove vanishing.
    have h_vanish : ∀ j : Fin (p + 2), j ≠ j₀ →
        (if h : T ⊆ (eraseNth S hS j).1
        then (-1 : ℤ) ^ j.val •
          relSimplexHomotopy T v hv R p f
            ⟨(eraseNth S hS j).1, (eraseNth S hS j).2, h⟩
        else 0) = 0 := by
      intro j hj
      have hv_ej : v ∈ (eraseNth S hS j).1 :=
        v_mem_eraseNth_of_ne_findPos S hS v hv_S j hj
      split_ifs with hT_ej
      · show (-1 : ℤ) ^ j.val •
          relSimplexHomotopy T v hv R p f
            ⟨(eraseNth S hS j).1, (eraseNth S hS j).2, hT_ej⟩ = 0
        simp only [relSimplexHomotopy, dif_pos hv_ej, smul_zero]
      · rfl
    rw [Fintype.sum_eq_single j₀ h_vanish]
    -- The j₀ term equals f_S
    have hv_ej₀ : v ∉ (eraseNth S hS j₀).1 := v_not_mem_eraseNth_findPos S hS v hv_S
    have hT_ej₀ : T ⊆ (eraseNth S hS j₀).1 := by
      rw [eraseNth_findPos_val]; exact subset_erase_of_not_mem hT_S hv
    rw [dif_pos hT_ej₀]
    show (-1 : ℤ) ^ j₀.val •
      relSimplexHomotopy T v hv R p f
        ⟨(eraseNth S hS j₀).1, (eraseNth S hS j₀).2, hT_ej₀⟩ = f ⟨S, hS, hT_S⟩
    simp only [relSimplexHomotopy, dif_neg hv_ej₀]
    have h_ins : insert v (eraseNth S hS j₀).1 = S :=
      insert_eraseNth_eq S hS j₀ (nthElem_findPos S hS v hv_S)
    have h_pos : insertPos (eraseNth S hS j₀).1 v = j₀.val := by
      rw [eraseNth_findPos_val]; exact insertPos_erase_eq_findPos_val S hS v hv_S
    rw [smul_smul, ← pow_add, h_pos, show j₀.val + j₀.val = 2 * j₀.val from by omega,
      pow_mul, neg_one_sq, one_pow, one_smul]
    congr 1; exact Subtype.ext h_ins
  · -- Case v ∉ S: both terms contribute and combine to give f_S.
    -- Setup: S' = insert v S, l = position of v in S'
    have hS'c : (insert v S).card = p + 3 := by
      rw [Finset.card_insert_of_notMem hv_S]; omega
    have hl_v := nthElem_findPos (insert v S) hS'c v (mem_insert_self v S)
    set l := findPos (insert v S) hS'c v (mem_insert_self v S) with hl_def
    have hl : insertPos S v = l.val := by
      rw [hl_def, ← insertPos_erase_eq_findPos_val (insert v S) hS'c v (mem_insert_self v S)]
      congr 1; exact (Finset.erase_insert hv_S).symm
    have h_el : (eraseNth (insert v S) hS'c l).1 = S := by
      simp only [eraseNth, hl_v]; exact Finset.erase_insert hv_S
    have hT_el : T ⊆ (eraseNth (insert v S) hS'c l).1 := by rw [h_el]; exact hT_S
    have hT_ins : T ⊆ insert v S := hT_S.trans (subset_insert v S)
    -- v ∉ any face of S
    have hv_ej : ∀ j, v ∉ (eraseNth S hS j).1 :=
      v_not_mem_eraseNth_of_not_mem S hS v hv_S
    -- Structural identity: eraseNth(S', l.succAbove j) = insert v (eraseNth S j)
    have h_struct : ∀ j : Fin (p + 2),
        (eraseNth (insert v S) hS'c (l.succAbove j)).1 =
        insert v (eraseNth S hS j).1 :=
      fun j => eraseNth_insert_succAbove S hS v hv_S hS'c l hl_v j
    -- T-subset transfers across the structural identity
    have h_T_iff : ∀ j : Fin (p + 2),
        T ⊆ (eraseNth (insert v S) hS'c (l.succAbove j)).1 ↔
        T ⊆ (eraseNth S hS j).1 := by
      intro j; rw [h_struct]; exact Finset.subset_insert_iff_of_notMem hv
    -- card proof for insert v (eraseNth S j)
    have h_card : ∀ j : Fin (p + 2),
        (insert v (eraseNth S hS j).1).card = p + 2 := by
      intro j; rw [Finset.card_insert_of_notMem (hv_ej j), (eraseNth S hS j).2]
    -- T ⊆ insert v (eraseNth S j).1 ↔ T ⊆ (eraseNth S j).1
    have h_T_ins_ej : ∀ j : Fin (p + 2),
        T ⊆ insert v (eraseNth S hS j).1 ↔ T ⊆ (eraseNth S hS j).1 :=
      fun j => Finset.subset_insert_iff_of_notMem hv
    -- Compute δh(f)_S: expand δ and h
    have h_δh : relSimplexδ T R p (relSimplexHomotopy T v hv R p f) ⟨S, hS, hT_S⟩ =
        ∑ j : Fin (p + 2),
          if hT : T ⊆ (eraseNth S hS j).1
          then (-1 : ℤ) ^ (j.val + insertPos (eraseNth S hS j).1 v) •
            f ⟨insert v (eraseNth S hS j).1, h_card j, (h_T_ins_ej j).mpr hT⟩
          else 0 := by
      simp only [relSimplexδ_apply, relSimplexHomotopy, dif_neg (hv_ej _)]
      congr 1; ext j; split_ifs with hT
      · rw [smul_smul, ← pow_add]
      · rfl
    -- Compute hδ(f)_S: since v ∉ S, insert v then take δ
    have h_hδ : relSimplexHomotopy T v hv R (p + 1) (relSimplexδ T R (p + 1) f)
        ⟨S, hS, hT_S⟩ =
        (-1 : ℤ) ^ l.val •
          ∑ k : Fin (p + 3),
            if hT : T ⊆ (eraseNth (insert v S) hS'c k).1
            then (-1 : ℤ) ^ k.val •
              f ⟨(eraseNth (insert v S) hS'c k).1,
                (eraseNth (insert v S) hS'c k).2, hT⟩
            else 0 := by
      simp only [relSimplexHomotopy, dif_neg hv_S, relSimplexδ_apply, ← hl]
    -- Local version of Fin.sum_univ_succAbove (avoiding import of BigOperators.Fin)
    have sum_succAbove : ∀ {m : ℕ}
        (g : Fin (m + 1) → R) (x : Fin (m + 1)),
        ∑ i, g i = g x + ∑ i : Fin m, g (x.succAbove i) :=
      fun g x => by rw [Fin.univ_succAbove _ x, Finset.sum_cons, Finset.sum_map,
        Fin.coe_succAboveEmb]
    -- Split the inner sum of hδ at l, then distribute the smul
    have h_inner := sum_succAbove (fun k : Fin (p + 3) =>
      if hT : T ⊆ (eraseNth (insert v S) hS'c k).1
      then (-1 : ℤ) ^ k.val •
        f ⟨(eraseNth (insert v S) hS'c k).1, (eraseNth (insert v S) hS'c k).2, hT⟩
      else 0) l
    rw [h_δh, h_hδ, h_inner, smul_add, Finset.smul_sum]
    -- The l-th term gives f_S
    have h_l_term : (-1 : ℤ) ^ l.val •
        (if hT : T ⊆ (eraseNth (insert v S) hS'c l).1
        then (-1 : ℤ) ^ l.val •
          f ⟨(eraseNth (insert v S) hS'c l).1,
            (eraseNth (insert v S) hS'c l).2, hT⟩
        else 0) = f ⟨S, hS, hT_S⟩ := by
      rw [dif_pos hT_el, smul_smul, ← pow_add,
        show l.val + l.val = 2 * l.val from by omega,
        pow_mul, neg_one_sq, one_pow, one_smul]
      congr 1; exact Subtype.ext h_el
    -- Rearrange: f_S + (δh + remaining hδ) = f_S, so need δh + remaining = 0
    rw [h_l_term, ← add_assoc, add_comm (∑ _, _) (f _), add_assoc]
    suffices h_cancel :
        (∑ j : Fin (p + 2),
          if hT : T ⊆ (eraseNth S hS j).1
          then (-1 : ℤ) ^ (j.val + insertPos (eraseNth S hS j).1 v) •
            f ⟨insert v (eraseNth S hS j).1, h_card j, (h_T_ins_ej j).mpr hT⟩
          else 0) +
        (∑ j : Fin (p + 2),
          (-1 : ℤ) ^ l.val •
            (if hT : T ⊆ (eraseNth (insert v S) hS'c (l.succAbove j)).1
            then (-1 : ℤ) ^ (l.succAbove j).val •
              f ⟨(eraseNth (insert v S) hS'c (l.succAbove j)).1,
                (eraseNth (insert v S) hS'c (l.succAbove j)).2, hT⟩
            else 0)) = 0 by
      rw [h_cancel, add_zero]
    -- Combine into a single sum and show each term cancels
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro j _
    -- Case split on T ⊆ eraseNth S j
    by_cases hT_ej : T ⊆ (eraseNth S hS j).1
    · -- Both dif conditions are true
      have hT' : T ⊆ (eraseNth (insert v S) hS'c (l.succAbove j)).1 :=
        (h_T_iff j).mpr hT_ej
      rw [dif_pos hT_ej, dif_pos hT']
      -- The f values are equal via the structural identity
      have hf_eq : f ⟨(eraseNth (insert v S) hS'c (l.succAbove j)).1,
          (eraseNth (insert v S) hS'c (l.succAbove j)).2, hT'⟩ =
        f ⟨insert v (eraseNth S hS j).1, h_card j, (h_T_ins_ej j).mpr hT_ej⟩ :=
        congrArg f (Subtype.ext (h_struct j))
      rw [smul_smul, hf_eq, ← add_smul, ← pow_add]
      -- Signs cancel: exponents differ by 1
      suffices (-1 : ℤ) ^ (j.val + insertPos (eraseNth S hS j).1 v) +
          (-1 : ℤ) ^ (l.val + (l.succAbove j).val) = 0 by
        rw [this, zero_smul]
      have hne : nthElem S hS j ≠ v := fun h => hv_S (h ▸ nthElem_mem S hS j)
      rcases lt_or_gt_of_ne hne with hjv | hjv
      · -- nthElem S j < v: insertPos drops by 1, succAbove gives castSucc
        have hj_lt_l : j.val < l.val := by
          rw [← hl]; by_contra h_bad; push_neg at h_bad
          exact absurd hjv (not_lt.mpr (le_of_lt
            (nthElem_gt_of_ge_insertPos S hS v hv_S j h_bad)))
        rw [insertPos_eraseNth_lt S hS v hv_S j hjv,
          Fin.succAbove_of_castSucc_lt l j
            (by have := Fin.coe_castSucc j; omega),
          Fin.coe_castSucc j, ← hl,
          show insertPos S v + j.val = j.val + (insertPos S v - 1) + 1 from by omega,
          pow_succ, mul_neg_one, add_neg_cancel]
      · -- v < nthElem S j: insertPos unchanged, succAbove gives succ
        have hl_le_j : l.val ≤ j.val := by
          rw [← hl]; by_contra h_bad; push_neg at h_bad
          exact absurd hjv (not_lt.mpr (le_of_lt
            (nthElem_lt_of_lt_insertPos S hS v hv_S j h_bad)))
        rw [insertPos_eraseNth_ge S hS v hv_S j hjv,
          Fin.succAbove_of_le_castSucc l j
            (by have := Fin.coe_castSucc j; omega),
          Fin.val_succ, ← hl,
          show insertPos S v + (j.val + 1) = j.val + insertPos S v + 1 from by omega,
          pow_succ, mul_neg_one, add_neg_cancel]
    · -- Both dif conditions are false
      have hT' : ¬(T ⊆ (eraseNth (insert v S) hS'c (l.succAbove j)).1) :=
        fun h => hT_ej ((h_T_iff j).mp h)
      rw [dif_neg hT_ej, dif_neg hT', smul_zero, add_zero]

/-! ### Degree-0 homotopy equation -/

/-- The degree-0 homotopy equation: `h₁ ∘ δ₀ = id` on degree-0 cochains.
At degree 0, every 1-element subset containing `T` equals `T` itself (since `T` is nonempty),
and `v ∉ T` means the homotopy has a single surviving term. -/
private theorem relSimplexHomotopy_eq_zero (T : Finset (Fin (n + 1))) (v : Fin (n + 1))
    (hv : v ∉ T) (R : Type*) [AddCommGroup R] (hT_ne : T.Nonempty)
    (f : relSimplexCochain T R 0)
    (S : { S : Finset (Fin (n + 1)) // S.card = 1 ∧ T ⊆ S }) :
    relSimplexHomotopy T v hv R 0 (relSimplexδ T R 0 f) S = f S := by
  obtain ⟨S, hS, hT_S⟩ := S
  -- S has card 1 and T ⊆ S with T nonempty, so T = S and v ∉ S
  have hT_card : T.card = 1 := by
    have h1 := Finset.card_le_card hT_S
    have h2 := hT_ne.card_pos
    omega
  have hT_eq_S : T = S :=
    Finset.eq_of_subset_of_card_le hT_S (by omega)
  have hv_S : v ∉ S := hT_eq_S ▸ hv
  -- Expand the homotopy (v ∉ S case)
  simp only [relSimplexHomotopy, dif_neg hv_S]
  -- insert v S has card 2
  have hIns : (insert v S).card = 2 := by rw [Finset.card_insert_of_notMem hv_S, hS]
  have hT_ins : T ⊆ insert v S := hT_S.trans (subset_insert v S)
  -- Position of v in insert v S
  set l := findPos (insert v S) hIns v (mem_insert_self v S)
  have hl : insertPos S v = l.val := by
    rw [← insertPos_erase_eq_findPos_val (insert v S) hIns v (mem_insert_self v S)]
    congr 1; exact (Finset.erase_insert hv_S).symm
  have hl_v := nthElem_findPos (insert v S) hIns v (mem_insert_self v S)
  -- Expand δ: sum over Fin 2, only the term erasing v survives
  show (-1 : ℤ) ^ insertPos S v •
    (∑ j : Fin 2, if h : T ⊆ (eraseNth (insert v S) hIns j).1
      then (-1 : ℤ) ^ j.val •
        f ⟨(eraseNth (insert v S) hIns j).1, (eraseNth (insert v S) hIns j).2, h⟩
      else 0) = f ⟨S, hS, hT_S⟩
  -- The term at j = l erases v, giving S ⊇ T
  have h_el : (eraseNth (insert v S) hIns l).1 = S := by
    simp only [eraseNth]; rw [hl_v]; exact Finset.erase_insert hv_S
  have hT_el : T ⊆ (eraseNth (insert v S) hIns l).1 := by rw [h_el]; exact hT_S
  -- The term at j ≠ l erases some element of S, giving {v}, and T ⊄ {v}
  have h_vanish : ∀ j : Fin 2, j ≠ l →
      (if h : T ⊆ (eraseNth (insert v S) hIns j).1
      then (-1 : ℤ) ^ j.val •
        f ⟨(eraseNth (insert v S) hIns j).1, (eraseNth (insert v S) hIns j).2, h⟩
      else 0) = 0 := by
    intro j hj
    have hv_ej : v ∈ (eraseNth (insert v S) hIns j).1 :=
      v_mem_eraseNth_of_ne_findPos (insert v S) hIns v (mem_insert_self v S) j hj
    have hcard1 : (eraseNth (insert v S) hIns j).1.card = 1 :=
      (eraseNth (insert v S) hIns j).2
    have hv_only : (eraseNth (insert v S) hIns j).1 = {v} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hv_ej, fun x hx => Finset.card_le_one_iff.mp (le_of_eq hcard1) hx hv_ej⟩
    have hT_not : ¬(T ⊆ (eraseNth (insert v S) hIns j).1) := by
      rw [hv_only]; intro h
      exact hv (Finset.mem_singleton.mp (h hT_ne.choose_spec) ▸ hT_ne.choose_spec)
    exact dif_neg hT_not
  rw [Fintype.sum_eq_single l h_vanish, dif_pos hT_el, smul_smul, ← pow_add, ← hl,
    show insertPos S v + insertPos S v = 2 * insertPos S v from by omega,
    pow_mul, neg_one_sq, one_pow, one_smul]
  congr 1; exact Subtype.ext h_el

/-! ### Acyclicity -/

/-- An object `X` in a preadditive category is zero iff `𝟙 X = 0`. -/
private theorem isZero_of_id_eq_zero {C : Type*} [Category C] [Preadditive C] {X : C}
    (h : 𝟙 X = 0) : CategoryTheory.Limits.IsZero X where
  unique_to Y :=
    ⟨{ default := 0
       uniq := fun f => by rw [← Category.id_comp f, h, Limits.zero_comp] }⟩
  unique_from Y :=
    ⟨{ default := 0
       uniq := fun f => by rw [← Category.comp_id f, h, Limits.comp_zero] }⟩

/-- The relative simplex cochain complex is acyclic when `T` is nonempty and proper.

The hypothesis `hT_ne : T.Nonempty` ensures the complex is nontrivial, and
`hT_ne' : T ≠ Finset.univ` provides an element `v ∉ T` for the contracting homotopy. -/
theorem relSimplexComplex_acyclic (T : Finset (Fin (n + 1))) (R : Type*) [AddCommGroup R]
    (hT_ne : T.Nonempty) (hT_ne' : T ≠ Finset.univ) :
    (relSimplexComplex T R).Acyclic := by
  -- Obtain v ∉ T from the hypothesis that T is proper
  have ⟨v, hv⟩ : ∃ v, v ∉ T := by
    by_contra h; push_neg at h; exact hT_ne' (eq_univ_of_forall h)
  set K := relSimplexComplex T R
  -- Define the homotopy data
  let homData : ∀ i j, (ComplexShape.up ℕ).Rel j i → (K.X i ⟶ K.X j) :=
    fun i j hij =>
      eqToHom (show K.X i = K.X (j + 1) from congr_arg K.X hij.symm) ≫
      AddCommGrp.ofHom (relSimplexHomotopyHom T v hv R j)
  -- Show 𝟙 K = nullHomotopicMap' homData
  suffices hEq : 𝟙 K = Homotopy.nullHomotopicMap' homData by
    -- Transport the null-homotopy to get Homotopy (𝟙 K) 0
    have hNull : Homotopy (𝟙 K) 0 := hEq ▸ Homotopy.nullHomotopy' homData
    -- Derive acyclicity from the null-homotopy
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply isZero_of_id_eq_zero
    have := hNull.homologyMap_eq i
    rwa [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at this
  -- Prove 𝟙 K = nullHomotopicMap' homData degree by degree
  -- Helper: K.d unfolds via CochainComplex.of_d
  have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom (relSimplexδHom T R j) :=
    fun j => by simp [K, relSimplexComplex]
  ext i : 1
  induction i with
  | zero =>
    simp only [HomologicalComplex.id_f]
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      (fun l hl => by simp [ComplexShape.up'_Rel] at hl)]
    -- Goal: 𝟙 (K.X 0) = K.d 0 1 ≫ homData 1 0 _
    -- Unfold homData; eqToHom is 𝟙 since K.X 1 = K.X (0+1) definitionally
    simp only [homData, eqToHom_refl, Category.id_comp]
    rw [hKd, ← AddCommGrp.ofHom_comp, ← AddCommGrp.ofHom_id]
    congr 1; ext f; funext S
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, relSimplexδHom,
      relSimplexHomotopyHom, AddMonoidHom.mk'_apply]
    exact (relSimplexHomotopy_eq_zero T v hv R hT_ne f S).symm
  | succ p _ =>
    simp only [HomologicalComplex.id_f]
    rw [Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (p + 1) (p + 2) from rfl)]
    -- Unfold homData; eqToHom is 𝟙 definitionally
    simp only [homData, eqToHom_refl, Category.id_comp]
    rw [hKd, hKd, ← AddCommGrp.ofHom_comp, ← AddCommGrp.ofHom_comp,
      ← AddCommGrp.ofHom_id]
    congr 1; ext f; funext S
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, AddMonoidHom.id_apply,
      relSimplexδHom, relSimplexHomotopyHom, AddMonoidHom.mk'_apply]
    rw [add_comm]
    exact (relSimplexHomotopy_eq T v hv R p f S).symm

/-! ### Boundary cases: T = ∅ and T = Finset.univ -/

/-- When `T = ∅`, the relative simplex complex is exact at all positive degrees.
Every subset contains `∅`, so the homotopy equation applies for any `v`. -/
theorem relSimplexComplex_empty_exactAt (R : Type*) [AddCommGroup R] (p : ℕ) :
    (relSimplexComplex (∅ : Finset (Fin (n + 1))) R).ExactAt (p + 1) := by
  set K := relSimplexComplex (∅ : Finset (Fin (n + 1))) R
  have hv : (0 : Fin (n + 1)) ∉ (∅ : Finset (Fin (n + 1))) := Finset.notMem_empty _
  have hKd : ∀ j, K.d j (j + 1) = AddCommGrp.ofHom (relSimplexδHom ∅ R j) :=
    fun j => by simp [K, relSimplexComplex]
  rw [HomologicalComplex.exactAt_iff' K p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro f hf
  have hg : (K.sc' p (p + 1) (p + 2)).g = K.d (p + 1) (p + 2) := rfl
  have hfi : (K.sc' p (p + 1) (p + 2)).f = K.d p (p + 1) := rfl
  have hf' : relSimplexδ ∅ R (p + 1) f = 0 := by
    rw [hg, hKd] at hf; exact hf
  have goal' : relSimplexδ ∅ R p (relSimplexHomotopy ∅ 0 hv R p f) = f := by
    ext S
    have key := relSimplexHomotopy_eq ∅ 0 hv R p f S
    rw [hf', relSimplexHomotopy_map_zero, Pi.zero_apply, add_zero] at key
    exact key
  exact ⟨relSimplexHomotopy ∅ 0 hv R p f, by rw [hfi, hKd]; exact goal'⟩

/-- When `T = Finset.univ`, the only subset of `Fin (n + 1)` with `(p + 1)` elements
containing all of `Fin (n + 1)` is `Finset.univ` itself, requiring `p + 1 = n + 1`. -/
theorem relSimplexCochain_univ_isEmpty (hp : p + 1 ≠ n + 1) :
    IsEmpty { S : Finset (Fin (n + 1)) // S.card = p + 1 ∧ Finset.univ ⊆ S } := by
  constructor; rintro ⟨S, hcard, huniv⟩
  have hS : S = Finset.univ := le_antisymm (Finset.subset_univ S) huniv
  exact hp (by rw [← hcard, hS, Finset.card_univ, Fintype.card_fin])

/-- When `T = Finset.univ` and `p ≠ n`, the cochain group at degree `p` is zero. -/
theorem relSimplexComplex_univ_isZero_X (R : Type*) [AddCommGroup R] (hp : p ≠ n) :
    IsZero ((relSimplexComplex (Finset.univ : Finset (Fin (n + 1))) R).X p) := by
  have hempty := relSimplexCochain_univ_isEmpty (show p + 1 ≠ n + 1 by omega)
  have hsub : Subsingleton (relSimplexCochain (Finset.univ : Finset (Fin (n + 1))) R p) :=
    ⟨fun f g => funext fun x => hempty.elim x⟩
  exact @AddCommGrp.isZero_of_subsingleton _ hsub

/-- When `T = Finset.univ` and `p ≠ n`, the complex is exact at degree `p`. -/
theorem relSimplexComplex_univ_exactAt (R : Type*) [AddCommGroup R] (hp : p ≠ n) :
    (relSimplexComplex (Finset.univ : Finset (Fin (n + 1))) R).ExactAt p := by
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ (relSimplexComplex_univ_isZero_X R hp)

/-- When `T = Finset.univ`, the unique `(n + 1)`-element subset of `Fin (n + 1)` containing
all elements is `Finset.univ` itself. -/
instance relSimplexCochain_univ_unique :
    Unique { S : Finset (Fin (n + 1)) // S.card = n + 1 ∧
      (Finset.univ : Finset (Fin (n + 1))) ⊆ S } where
  default := ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin], subset_refl _⟩
  uniq := fun ⟨S, _, huniv⟩ =>
    Subtype.ext (Finset.eq_univ_of_forall (fun a => huniv (Finset.mem_univ a)))
