/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.Topology.Sheaves.RelativeSimplexComplex

/-!
# Čech cohomology computations for the relative simplex complex

This file computes the degree-zero homology `H^0(K_∅) ≅ R` of the relative simplex
cochain complex for the empty subset. Since `∅ ⊆ S` holds for all `S`, the complex
`K_∅` has cochains on **all** subsets of the right cardinality. The kernel of the
degree-zero differential consists precisely of the constant cochains, giving
`H^0(K_∅) ≅ R`.

Together with the previously established results:
- `H^p(K_∅) = 0` for `p > 0` (`relSimplexComplex_empty_isZero_homology`)
- `H^n(K_univ) ≅ R` (`relSimplexComplex_univ_homologyIso`)
- `H^p(K_T) = 0` for all `p` when `T` is nonempty proper (`relSimplexComplex_acyclic`)

this gives a complete description of the homology of all `K_T` complexes.

## Main results

* `relSimplexComplex_empty_homologyIso`: `H^0(K_∅) ≅ R`

## References

* [Stacks Project, Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS)
-/

open CategoryTheory Finset

variable {n : ℕ}

namespace TopCat

/-! ### Constant cochains and the kernel of d⁰ for K_∅ -/

/-- The constant cochain embedding as an `AddMonoidHom`: sends `r : R` to the cochain
that assigns `r` to every singleton. -/
def relSimplexConstCochainHom (R : Type*) [AddCommGroup R] :
    R →+ relSimplexCochain (∅ : Finset (Fin (n + 1))) R 0 where
  toFun r _ := r
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- The differential kills constant cochains: `d⁰(const r) = 0`.
The alternating sum `∑ (-1)^j · r` over `Fin 2` gives `r + (-r) = 0`. -/
theorem relSimplexδ_constCochain_eq_zero (R : Type*) [AddCommGroup R] (r : R) :
    relSimplexδHom (∅ : Finset (Fin (n + 1))) R 0 (relSimplexConstCochainHom R r) = 0 := by
  ext ⟨S, hS, _⟩
  simp only [relSimplexδHom, relSimplexδ_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    relSimplexConstCochainHom, Pi.zero_apply, dif_pos (Finset.empty_subset _)]
  rw [Fin.sum_univ_two]
  simp [pow_succ, neg_one_smul, add_neg_cancel]

/-- The evaluation map: evaluates a 0-cochain at the singleton `{i}`. -/
def relSimplexEvalSingleton (R : Type*) [AddCommGroup R] (i : Fin (n + 1)) :
    relSimplexCochain (∅ : Finset (Fin (n + 1))) R 0 →+ R where
  toFun f := f ⟨{i}, Finset.card_singleton _, Finset.empty_subset _⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Two elements of a 2-element finset that are mapped from distinct `Fin 2` indices
by `nthElem` are distinct. -/
private theorem nthElem_pair_ne {S : Finset (Fin (n + 1))} (hS : S.card = 2) :
    nthElem S hS (0 : Fin 2) ≠ nthElem S hS (1 : Fin 2) := by
  intro h
  exact absurd ((S.orderIsoOfFin hS).injective (Subtype.ext h))
    (by omega : (0 : Fin 2) ≠ 1)

/-- Key constancy lemma: if `d⁰ f = 0` and `a ≠ b`, then `f({a}) = f({b})`.

We evaluate `d⁰ f` at the pair `{a, b}`: since `T = ∅`, all `dif` conditions hold, and
the alternating sum gives `f(face₀) - f(face₁) = 0`. A case split on which face is `{a}`
and which is `{b}` shows `f({a}) = f({b})`. -/
private theorem relSimplexδ_ker_values_eq (R : Type*) [AddCommGroup R]
    (f : relSimplexCochain (∅ : Finset (Fin (n + 1))) R 0)
    (hf : relSimplexδHom (∅ : Finset (Fin (n + 1))) R 0 f = 0)
    (a b : Fin (n + 1)) (hab : a ≠ b) :
    relSimplexEvalSingleton R a f = relSimplexEvalSingleton R b f := by
  -- Evaluate d⁰ f at the pair {a, b}
  have hcard : ({a, b} : Finset (Fin (n + 1))).card = 2 := Finset.card_pair hab
  have heval := congr_fun hf ⟨{a, b}, hcard, Finset.empty_subset _⟩
  simp only [relSimplexδHom, relSimplexδ_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Pi.zero_apply, dif_pos (Finset.empty_subset _)] at heval
  rw [Fin.sum_univ_two] at heval
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_succ, pow_zero, one_mul,
    neg_one_smul] at heval
  -- heval : f(eraseNth 0) + (-f(eraseNth 1)) = 0, so they're equal
  rw [add_neg_eq_zero] at heval
  -- Case analysis on nthElem membership
  have h0mem := nthElem_mem ({a, b} : Finset (Fin (n + 1))) hcard (0 : Fin 2)
  have h1mem := nthElem_mem ({a, b} : Finset (Fin (n + 1))) hcard (1 : Fin 2)
  have hne := nthElem_pair_ne hcard
  rw [Finset.mem_insert, Finset.mem_singleton] at h0mem h1mem
  simp only [relSimplexEvalSingleton, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rcases h0mem with h0 | h0
  · -- nthElem 0 = a
    have h1 : nthElem ({a, b} : Finset (Fin (n + 1))) hcard (1 : Fin 2) = b := by
      rcases h1mem with h | h
      · exact absurd (h0.trans h.symm) hne
      · exact h
    have he0 :
        (eraseNth ({a, b} : Finset (Fin (n + 1))) hcard (0 : Fin 2)).1 = {b} := by
      show ({a, b} : Finset (Fin (n + 1))).erase (nthElem _ hcard 0) = {b}
      rw [h0, Finset.erase_insert (Finset.notMem_singleton.mpr hab)]
    have he1 :
        (eraseNth ({a, b} : Finset (Fin (n + 1))) hcard (1 : Fin 2)).1 = {a} := by
      show ({a, b} : Finset (Fin (n + 1))).erase (nthElem _ hcard 1) = {a}
      rw [h1, Finset.erase_insert_of_ne hab, Finset.erase_singleton,
        Finset.insert_empty]
    -- f({a}) = f(eraseNth 1) = f(eraseNth 0) = f({b})
    convert heval.symm using 1 <;> (congr 1; ext1) <;> [exact he1.symm; exact he0.symm]
  · -- nthElem 0 = b
    have h1 : nthElem ({a, b} : Finset (Fin (n + 1))) hcard (1 : Fin 2) = a := by
      rcases h1mem with h | h
      · exact h
      · exact absurd (h0.trans h.symm) hne
    have he0 :
        (eraseNth ({a, b} : Finset (Fin (n + 1))) hcard (0 : Fin 2)).1 = {a} := by
      show ({a, b} : Finset (Fin (n + 1))).erase (nthElem _ hcard 0) = {a}
      rw [h0, Finset.erase_insert_of_ne hab, Finset.erase_singleton,
        Finset.insert_empty]
    have he1 :
        (eraseNth ({a, b} : Finset (Fin (n + 1))) hcard (1 : Fin 2)).1 = {b} := by
      show ({a, b} : Finset (Fin (n + 1))).erase (nthElem _ hcard 1) = {b}
      rw [h1, Finset.erase_insert (Finset.notMem_singleton.mpr hab)]
    -- f({a}) = f(eraseNth 0) = f(eraseNth 1) = f({b})
    convert heval using 1 <;> (congr 1; ext1) <;> [exact he0.symm; exact he1.symm]

/-- Any element of `ker(d⁰)` is a constant cochain: there exists `r : R` such that
`f(S) = r` for all singletons `S`. -/
theorem relSimplexCochain_empty_ker_const (R : Type*) [AddCommGroup R]
    (f : relSimplexCochain (∅ : Finset (Fin (n + 1))) R 0)
    (hf : relSimplexδHom (∅ : Finset (Fin (n + 1))) R 0 f = 0) :
    f = relSimplexConstCochainHom R (relSimplexEvalSingleton R (0 : Fin (n + 1)) f) := by
  ext ⟨S, hcard, _⟩
  simp only [relSimplexConstCochainHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  -- S has card 1, so S = {i} for some i
  rw [Finset.card_eq_one] at hcard
  obtain ⟨i, rfl⟩ := hcard
  -- Show f({i}) = f({0})
  show f ⟨{i}, Finset.card_singleton _, Finset.empty_subset _⟩ =
    f ⟨{(0 : Fin (n + 1))}, Finset.card_singleton _, Finset.empty_subset _⟩
  by_cases hi : i = (0 : Fin (n + 1))
  · subst hi; rfl
  · exact relSimplexδ_ker_values_eq R f hf i 0 hi

/-- The `AddEquiv` between the kernel of `d⁰` for `K_∅` and `R`.
The forward map evaluates at `{0}`, the inverse sends `r` to the constant cochain. -/
def relSimplexKerδ_equiv (R : Type*) [AddCommGroup R] :
    AddMonoidHom.ker (relSimplexδHom (∅ : Finset (Fin (n + 1))) R 0) ≃+ R where
  toFun x := relSimplexEvalSingleton R (0 : Fin (n + 1)) x.1
  invFun r := ⟨relSimplexConstCochainHom R r,
    show relSimplexδHom _ R 0 (relSimplexConstCochainHom R r) = 0 from
      relSimplexδ_constCochain_eq_zero R r⟩
  left_inv := fun ⟨f, hf⟩ => by
    ext1
    exact (relSimplexCochain_empty_ker_const R f hf).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

/-! ### H⁰(K_∅) ≅ R -/

/-- `H^0(K_∅) ≅ R`: the degree-zero homology of the relative simplex complex for
`T = ∅` is isomorphic to `R`. -/
noncomputable def relSimplexComplex_empty_homologyIso (R : Type*) [AddCommGroup R] :
    (relSimplexComplex (∅ : Finset (Fin (n + 1))) R).homology 0 ≅
      AddCommGrp.of R := by
  set K := relSimplexComplex (∅ : Finset (Fin (n + 1))) R
  -- Step 1: Use homologyIsoSc' to work with concrete indices, avoiding Classical.choose
  -- in ComplexShape.next/prev
  have hk : (ComplexShape.up ℕ).next 0 = 1 := (ComplexShape.up ℕ).next_eq' rfl
  refine K.homologyIsoSc' _ 0 1 rfl hk ≪≫ ?_
  set S := K.sc' ((ComplexShape.up ℕ).prev 0) 0 1
  -- Step 2: S.homology ≅ ker(g.hom) / range(abToCycles) via abHomologyIso
  refine S.abHomologyIso ≪≫ ?_
  -- Step 3: The incoming map f is zero (no degree -1 for ℕ-indexed complex)
  have hf : S.f = 0 := K.shape _ _ (by simp [ComplexShape.up_Rel])
  -- Step 4: abToCycles = 0 when f = 0, so range = ⊥
  have habToCycles_zero : S.abToCycles = 0 := by
    ext x : 1
    refine Subtype.ext ?_
    change (S.f x : S.X₂) = 0
    simp [hf]
  have hrange_bot : AddMonoidHom.range S.abToCycles = ⊥ := by
    rw [habToCycles_zero]; exact AddMonoidHom.range_zero
  -- Step 5: S.g = K.d 0 1 which is the concrete differential by CochainComplex.of_d
  have hg : S.g = AddCommGrp.ofHom (relSimplexδHom (∅ : Finset (Fin (n + 1))) R 0) := by
    show K.d 0 1 = _
    exact CochainComplex.of_d _ _ _ 0
  have hg_hom : S.g.hom = relSimplexδHom (∅ : Finset (Fin (n + 1))) R 0 := by
    rw [hg]; rfl
  -- Step 6: Build the composite equivalence (ker g.hom ⧸ range abToCycles) ≃+ R
  have kerEquiv : AddMonoidHom.ker S.g.hom ≃+ R := by
    rw [hg_hom]; exact relSimplexKerδ_equiv R
  have totalEquiv :
      (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) ≃+ R :=
    (QuotientAddGroup.quotientAddEquivOfEq hrange_bot).trans
      (QuotientAddGroup.quotientBot.trans kerEquiv)
  -- Step 7: Convert to categorical isomorphism
  exact totalEquiv.toAddCommGrpIso

end TopCat
