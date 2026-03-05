/-
Copyright (c) 2025 Matt Diamond. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Diamond
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.Fintype.BigOperators

/-!
# Čech Cochain Complex

Given a sheaf `F` of abelian groups on a topological space `X` and a finite indexed open cover
`U : ι → Opens X`, we construct the **ordered Čech cochain complex**.

## Main definitions

* `TopCat.cechCoverInf U S`: the intersection `⨅ i ∈ S, U i` for a finset `S`.
* `TopCat.cechObj F U p`: the `p`-th cochain group `∏_{|S|=p+1} F(U_S)`.
* `TopCat.cechδ F U p`: the coboundary map `d^p : C^p → C^{p+1}`.
* `TopCat.cechComplex F U`: the Čech cochain complex.

## References

* [Hartshorne, *Algebraic Geometry*, III.4]
* [Stacks Project, Tag 01ED](https://stacks.math.columbia.edu/tag/01ED)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite Finset

namespace TopCat

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
variable {X : TopCat}

/-! ### Intersection of opens -/

/-- The intersection of opens indexed by a finset `S`. -/
def cechCoverInf (U : ι → Opens X) (S : Finset ι) : Opens X :=
  ⨅ i ∈ S, U i

omit [Fintype ι] [LinearOrder ι] [DecidableEq ι] in
theorem cechCoverInf_mono (U : ι → Opens X) {S T : Finset ι} (h : S ⊆ T) :
    cechCoverInf U T ≤ cechCoverInf U S :=
  iInf_le_iInf_of_subset h

/-! ### Cochain groups -/

variable (F : Sheaf AddCommGrpCat X) (U : ι → Opens X)

/-- The `p`-th Čech cochain group: the product of `F(U_S)` over all subsets `S ⊆ ι` with
`|S| = p + 1`. When `p + 1 > |ι|`, the index type is empty and this is the trivial group. -/
def cechObj (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (∀ S : {S : Finset ι // S.card = p + 1},
    F.1.obj (op (cechCoverInf U S.1)))

/-! ### Face maps and coboundary -/

/-- The `j`-th element of `T` in the linear order, via `Finset.orderIsoOfFin`. -/
def nthElem {n : ℕ} (T : Finset ι) (hT : T.card = n) (j : Fin n) : ι :=
  (T.orderIsoOfFin hT j).1

omit [Fintype ι] [DecidableEq ι] in
theorem nthElem_mem {n : ℕ} (T : Finset ι) (hT : T.card = n) (j : Fin n) :
    nthElem T hT j ∈ T :=
  (T.orderIsoOfFin hT j).2

/-- Erase the `j`-th element of `T`; the result has cardinality `n`. -/
def eraseNth {n : ℕ} (T : Finset ι) (hT : T.card = n + 1) (j : Fin (n + 1)) :
    {S : Finset ι // S.card = n} :=
  ⟨T.erase (nthElem T hT j), by
    rw [card_erase_of_mem (nthElem_mem T hT j), hT]; omega⟩

/-- The coboundary map `d^p : C^p → C^{p+1}` of the Čech complex.

For `T` with `|T| = p + 2`, the coboundary sends a cochain `f` to:
`(d f)_T = ∑_{j=0}^{p+1} (-1)^j · res(f_{T \ {t_j}})`,
where `t_j` is the `j`-th smallest element of `T`. -/
def cechδ (p : ℕ) : cechObj F U p ⟶ cechObj F U (p + 1) :=
  AddCommGrpCat.ofHom
    { toFun := fun f ⟨T, hT⟩ =>
        ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
          (F.1.map (homOfLE (cechCoverInf_mono U (erase_subset _ _))).op
            (f (eraseNth T hT j)))
      map_zero' := by
        ext ⟨T, hT⟩
        simp only [Pi.zero_apply, map_zero, smul_zero, sum_const_zero]
      map_add' := fun f g => by
        ext ⟨T, hT⟩
        simp only [Pi.add_apply, map_add, smul_add, sum_add_distrib] }

/-! ### d² = 0 -/

/-- The involution on `Fin (p + 3) × Fin (p + 2)` used in the d² = 0 proof.

For `(j, k)`, maps to `(k, j - 1)` when `k < j` and to `(k + 1, j)` when `k ≥ j`.
This pairs terms in the double sum whose signs cancel. -/
def cechInvolution (p : ℕ) (jk : Fin (p + 3) × Fin (p + 2)) :
    Fin (p + 3) × Fin (p + 2) :=
  if h : jk.2.val < jk.1.val then
    (⟨jk.2.val, by omega⟩, ⟨jk.1.val - 1, by omega⟩)
  else
    (⟨jk.2.val + 1, by omega⟩, ⟨jk.1.val, by omega⟩)

theorem cechInvolution_involutive (p : ℕ) (jk : Fin (p + 3) × Fin (p + 2)) :
    cechInvolution p (cechInvolution p jk) = jk := by
  obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := jk
  unfold cechInvolution
  simp only [Prod.fst, Prod.snd, Fin.val_mk]
  by_cases h : k < j
  · simp only [dif_pos h, Prod.fst, Prod.snd, Fin.val_mk]
    simp only [dif_neg (show ¬ (j - 1 < k) by omega), Fin.val_mk]
    ext <;> simp only [Prod.fst, Prod.snd, Fin.val_mk]; omega
  · simp only [dif_neg h, Prod.fst, Prod.snd, Fin.val_mk]
    simp only [dif_pos (show j < k + 1 by omega), Fin.val_mk]
    ext <;> simp only [Prod.fst, Prod.snd, Fin.val_mk]; omega

theorem cechInvolution_ne (p : ℕ) (jk : Fin (p + 3) × Fin (p + 2)) :
    cechInvolution p jk ≠ jk := by
  obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := jk
  unfold cechInvolution
  simp only [Prod.fst, Prod.snd, Fin.val_mk]
  split_ifs with h <;>
    (intro heq; have := (Prod.mk.inj heq).1; simp only [Fin.mk.injEq] at this; omega)

theorem cechInvolution_sign (p : ℕ) (jk : Fin (p + 3) × Fin (p + 2)) :
    (-1 : ℤ) ^ (cechInvolution p jk).1.val * (-1 : ℤ) ^ (cechInvolution p jk).2.val =
      -((-1 : ℤ) ^ jk.1.val * (-1 : ℤ) ^ jk.2.val) := by
  obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := jk
  unfold cechInvolution
  simp only [Prod.fst, Prod.snd, Fin.val_mk, ← pow_add]
  split_ifs with h
  · rw [show k + (j - 1) = (j + k) - 1 from by omega,
      show j + k = (j + k - 1) + 1 from by omega]
    simp [pow_succ, neg_mul]
  · rw [show (k + 1) + j = (j + k) + 1 from by omega]
    simp [pow_succ, neg_mul]

/-! ### Sorted list helpers for the d² = 0 proof -/

omit [Fintype ι] [DecidableEq ι] in
/-- `nthElem` equals the corresponding element of the sorted list. -/
theorem nthElem_eq_sort_getElem {n : ℕ} (T : Finset ι) (hT : T.card = n) (j : Fin n) :
    nthElem T hT j = (T.sort (· ≤ ·))[j.val]'(by rw [length_sort]; omega) := by
  simp [nthElem, coe_orderIsoOfFin_apply, orderEmbOfFin_apply]

omit [Fintype ι] in
/-- The sorted list of `T.erase (nthElem T hT j)` equals `(T.sort).eraseIdx j`. -/
theorem sort_erase_nthElem {n : ℕ} (T : Finset ι) (hT : T.card = n + 1)
    (j : Fin (n + 1)) :
    (T.erase (nthElem T hT j)).sort (· ≤ ·) =
      (T.sort (· ≤ ·)).eraseIdx j.val := by
  have h_nth : nthElem T hT j = (T.sort (· ≤ ·))[j.val]'(by rw [length_sort]; omega) :=
    nthElem_eq_sort_getElem T hT j
  rw [h_nth, ← (T.sort_nodup (· ≤ ·)).erase_getElem j.val (by rw [length_sort]; omega)]
  refine List.Perm.eq_of_pairwise' ((T.erase _).pairwise_sort (· ≤ ·))
    ((T.pairwise_sort (· ≤ ·)).sublist List.erase_sublist) ?_
  rw [List.perm_ext_iff_of_nodup ((T.erase _).sort_nodup _) ((T.sort_nodup _).erase _)]
  intro x
  simp only [(T.sort_nodup _).mem_erase_iff, mem_sort, mem_erase]

omit [Fintype ι] in
/-- The `k`-th element of `T` after erasing the `j`-th element, when `k < j`. -/
theorem nthElem_eraseNth_lt {n : ℕ} (T : Finset ι) (hT : T.card = n + 2)
    (j : Fin (n + 2)) (k : Fin (n + 1)) (hkj : k.val < j.val) :
    nthElem (eraseNth T hT j).1 (eraseNth T hT j).2 k =
      nthElem T hT ⟨k.val, by omega⟩ := by
  rw [nthElem_eq_sort_getElem, nthElem_eq_sort_getElem]
  dsimp only [eraseNth]
  rw [getElem_congr_coll (sort_erase_nthElem T hT j)]
  have hbound : k.val < ((T.sort (· ≤ ·)).eraseIdx j.val).length := by
    rw [List.length_eraseIdx_of_lt (by rw [length_sort]; omega)]; rw [length_sort]; omega
  exact List.getElem_eraseIdx_of_lt hbound hkj

omit [Fintype ι] in
/-- The `k`-th element of `T` after erasing the `j`-th element, when `k ≥ j`. -/
theorem nthElem_eraseNth_ge {n : ℕ} (T : Finset ι) (hT : T.card = n + 2)
    (j : Fin (n + 2)) (k : Fin (n + 1)) (hkj : j.val ≤ k.val) :
    nthElem (eraseNth T hT j).1 (eraseNth T hT j).2 k =
      nthElem T hT ⟨k.val + 1, by omega⟩ := by
  rw [nthElem_eq_sort_getElem, nthElem_eq_sort_getElem]
  dsimp only [eraseNth]
  rw [getElem_congr_coll (sort_erase_nthElem T hT j)]
  have hbound : k.val < ((T.sort (· ≤ ·)).eraseIdx j.val).length := by
    rw [List.length_eraseIdx_of_lt (by rw [length_sort]; omega)]; rw [length_sort]; omega
  exact List.getElem_eraseIdx_of_ge hbound (by omega)

omit [Fintype ι] in
/-- Double erasure: erasing elements at positions `j` then `k` from `T` gives the set
`T \ {nthElem T j, nthElem T (succAbove j k)}`. -/
theorem eraseNth_eraseNth_eq {n : ℕ} (T : Finset ι) (hT : T.card = n + 2)
    (j : Fin (n + 2)) (k : Fin (n + 1)) :
    (eraseNth (eraseNth T hT j).1 (eraseNth T hT j).2 k).1 =
      (T.erase (nthElem T hT j)).erase
        (nthElem T hT (if h : k.val < j.val then ⟨k.val, by omega⟩
          else ⟨k.val + 1, by omega⟩)) := by
  simp only [eraseNth]
  congr 1
  split
  · exact nthElem_eraseNth_lt T hT j k ‹_›
  · exact nthElem_eraseNth_ge T hT j k (by omega)

omit [Fintype ι] in
/-- The key combinatorial fact: erasing the `j`-th element of `T` and then the `k`-th element
of the result gives the same finset for paired indices under the involution. -/
theorem eraseNth_eraseNth_involution (p : ℕ) (T : Finset ι) (hT : T.card = p + 3)
    (jk : Fin (p + 3) × Fin (p + 2)) :
    let jk' := cechInvolution p jk
    (eraseNth (eraseNth T hT jk'.1).1 (eraseNth T hT jk'.1).2 jk'.2).1 =
      (eraseNth (eraseNth T hT jk.1).1 (eraseNth T hT jk.1).2 jk.2).1 := by
  obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := jk
  simp only [cechInvolution, Prod.fst, Prod.snd, Fin.val_mk]
  rw [eraseNth_eraseNth_eq, eraseNth_eraseNth_eq]
  by_cases h : k < j
  · -- σ(j,k) = (k, j-1). LHS erases t_k then t_j. RHS erases t_j then t_k.
    simp only [dif_pos h, Fin.val_mk]
    simp only [dif_neg (show ¬ (j - 1 < k) by omega), Fin.val_mk,
      show j - 1 + 1 = j by omega]
    exact erase_right_comm ..
  · -- σ(j,k) = (k+1, j). LHS erases t_{k+1} then t_j. RHS erases t_j then t_{k+1}.
    simp only [dif_neg h, Fin.val_mk]
    simp only [dif_pos (show j < k + 1 by omega), Fin.val_mk]
    exact erase_right_comm ..

omit [Fintype ι] in
/-- Two restriction-map compositions with the same target through different intermediates,
applied to `f S₁` and `f S₂` respectively, agree when `S₁ = S₂`. This handles the
dependent type issue where `rw` cannot directly rewrite `f S₁` to `f S₂`. -/
theorem restriction_comp_congr {p : ℕ} {T : Finset ι} (hT : T.card = p + 3)
    (f : cechObj F U p) {S₁ S₂ : {S : Finset ι // S.card = p + 1}} (heq : S₁ = S₂)
    (j₁ j₂ : Fin (p + 3))
    (h₁ : S₁.1 ⊆ (eraseNth T hT j₁).1) (h₂ : S₂.1 ⊆ (eraseNth T hT j₂).1) :
    (F.val.map (homOfLE (cechCoverInf_mono U (erase_subset _ T))).op)
      ((F.val.map (homOfLE (cechCoverInf_mono U h₁)).op) (f S₁)) =
    (F.val.map (homOfLE (cechCoverInf_mono U (erase_subset _ T))).op)
      ((F.val.map (homOfLE (cechCoverInf_mono U h₂)).op) (f S₂)) := by
  subst heq
  suffices h : (F.val.map (homOfLE (cechCoverInf_mono U h₁)).op ≫
      F.val.map (homOfLE (cechCoverInf_mono U (erase_subset _ T))).op) (f S₁) =
    (F.val.map (homOfLE (cechCoverInf_mono U h₂)).op ≫
      F.val.map (homOfLE (cechCoverInf_mono U (erase_subset _ T))).op) (f S₁) by
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  simp only [← F.val.map_comp]
  exact congrArg (fun m => (F.val.map m) (f S₁)) (Subsingleton.elim _ _)

omit [Fintype ι] in
theorem cechδ_comp_cechδ (p : ℕ) : cechδ F U p ≫ cechδ F U (p + 1) = 0 := by
  ext f
  funext ⟨T, hT⟩
  change (cechδ F U (p + 1) (cechδ F U p f)) ⟨T, hT⟩ = 0
  -- Unfold cechδ to expose the double sum, leaving restriction maps as morphisms
  change ∑ j : Fin (p + 3), ((-1 : ℤ) ^ j.val) •
    F.1.map (homOfLE (cechCoverInf_mono U (erase_subset _ _))).op
      (∑ k : Fin (p + 2), ((-1 : ℤ) ^ k.val) •
        F.1.map (homOfLE (cechCoverInf_mono U (erase_subset _ _))).op
          (f (eraseNth (eraseNth T hT j).1 (eraseNth T hT j).2 k))) = 0
  -- Distribute restriction maps over sums and scalars, then combine scalars
  simp_rw [map_sum, map_zsmul]
  -- Now have: ∑ j, (-1)^j • ∑ k, (-1)^k • res_j(res_jk(f(...))) = 0
  -- Distribute (-1)^j over the inner sum and combine scalars
  conv_lhs => arg 2; ext j; rw [Finset.smul_sum]; arg 2; ext k; rw [smul_smul]
  -- Convert double sum to single sum over pairs
  rw [← Finset.sum_product']
  -- Apply sign-reversing involution to show the sum is zero
  apply Finset.sum_ninvolution (cechInvolution p)
  · -- Paired terms sum to zero: a(σ(jk)) + a(jk) = 0
    intro jk
    -- The double-erased finsets agree under the involution
    have hval : (eraseNth (eraseNth T hT (cechInvolution p jk).1).1
        (eraseNth T hT (cechInvolution p jk).1).2 (cechInvolution p jk).2) =
      (eraseNth (eraseNth T hT jk.1).1 (eraseNth T hT jk.1).2 jk.2) :=
      Subtype.ext (eraseNth_eraseNth_involution p T hT jk)
    rw [cechInvolution_sign, neg_smul, add_neg_eq_zero]
    congr 1
    exact restriction_comp_congr F U hT f hval.symm jk.1 (cechInvolution p jk).1
      (erase_subset _ _) (erase_subset _ _)
  · intro jk _; exact cechInvolution_ne p jk
  · intro _; exact Finset.mem_univ _
  · exact cechInvolution_involutive p

/-! ### The Čech cochain complex -/

/-- The Čech cochain complex of a sheaf `F` with respect to a finite open cover `U`.
In degree `p`, it is the product `∏_{|S|=p+1} F(⋂_{i∈S} U_i)` with alternating-sign
coboundary. -/
def cechComplex : CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (cechObj F U) (cechδ F U) (cechδ_comp_cechδ F U)

end TopCat
