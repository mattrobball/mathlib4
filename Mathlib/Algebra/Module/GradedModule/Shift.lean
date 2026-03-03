/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Graded Module Shift

For a grading `𝓜 : ι → σ` indexed by an additive monoid, the **shifted grading**
`GradedModule.shift 𝓜 d` is defined by `(GradedModule.shift 𝓜 d) n = 𝓜 (n + d)`.

This operation is fundamental in algebraic geometry, where the twisting sheaf `𝒪(d)` on
projective space is defined via shifting the grading of the coordinate ring.

Note that the shifted *algebra* `A(d)` is a graded *module* over `A`, not a graded ring,
since `𝓐(i + d) * 𝓐(j + d) ⊆ 𝓐((i + j) + 2d)`, not `𝓐((i + j) + d)`.

## Main definitions

* `GradedModule.shift`: The shifted grading function.
* `GradedModule.shift.gradedSMul`: If `𝓐` and `𝓜` satisfy `SetLike.GradedSMul`, then so do
  `𝓐` and `GradedModule.shift 𝓜 d`.
* `GradedModule.shift.decomposition`: If `𝓜` has a `DirectSum.Decomposition`, so does
  `GradedModule.shift 𝓜 d` (requires additive group structure on the index).

## References

* [Stacks Project, Modules of homogeneous elements](https://stacks.math.columbia.edu/tag/01M3)

## Tags

graded module, shift, twist
-/

noncomputable section

namespace GradedModule

variable {ι : Type*}

section Basic

variable {σ : Type*} [Add ι]

/-- The shifted grading: `(shift 𝓜 d) n = 𝓜 (n + d)`.

For a graded module `M = ⨁ₙ 𝓜 n`, the Serre twist `M(d)` has grading
`M(d)ₙ = M_{n+d}`, obtained by applying this function to the grading. -/
abbrev shift (𝓜 : ι → σ) (d : ι) : ι → σ := fun n => 𝓜 (n + d)

@[simp]
theorem shift_apply (𝓜 : ι → σ) (d : ι) (n : ι) : shift 𝓜 d n = 𝓜 (n + d) := rfl

end Basic

section ShiftZero

variable {σ : Type*} [AddZeroClass ι]

@[simp]
theorem shift_zero (𝓜 : ι → σ) : shift 𝓜 0 = 𝓜 := by
  ext n; simp [shift]

end ShiftZero

section ShiftAdd

variable {σ : Type*} [AddSemigroup ι]

theorem shift_add (𝓜 : ι → σ) (d₁ d₂ : ι) :
    shift (shift 𝓜 d₁) d₂ = shift 𝓜 (d₂ + d₁) := by
  ext n; simp [shift, add_assoc]

end ShiftAdd

section ShiftAddComm

variable {σ : Type*} [AddCommMonoid ι]

theorem shift_comm (𝓜 : ι → σ) (d₁ d₂ : ι) :
    shift (shift 𝓜 d₁) d₂ = shift (shift 𝓜 d₂) d₁ := by
  rw [shift_add, shift_add, add_comm]

end ShiftAddComm

section ShiftNeg

variable {σ : Type*} [AddGroup ι]

@[simp]
theorem shift_neg_shift (𝓜 : ι → σ) (d : ι) : shift (shift 𝓜 d) (-d) = 𝓜 := by
  rw [shift_add, neg_add_cancel, shift_zero]

@[simp]
theorem shift_shift_neg (𝓜 : ι → σ) (d : ι) : shift (shift 𝓜 (-d)) d = 𝓜 := by
  rw [shift_add, add_neg_cancel, shift_zero]

/-- Shifting is an equivalence on grading functions. -/
def shiftEquiv (σ : Type*) (d : ι) : (ι → σ) ≃ (ι → σ) where
  toFun 𝓜 := shift 𝓜 d
  invFun 𝓜 := shift 𝓜 (-d)
  left_inv 𝓜 := show shift (shift 𝓜 d) (-d) = 𝓜 from shift_neg_shift 𝓜 d
  right_inv 𝓜 := show shift (shift 𝓜 (-d)) d = 𝓜 from shift_shift_neg 𝓜 d

end ShiftNeg

section GradedSMul

variable {R A M : Type*} {σ σ' : Type*}
variable [SetLike σ M] [SetLike σ' A] [SMul A M]
variable [AddMonoid ι]

/-- If `𝓐` and `𝓜` satisfy `SetLike.GradedSMul`, then so do `𝓐` and `shift 𝓜 d`.

The key compatibility is `i +ᵥ (j + d) = (i +ᵥ j) + d`, which holds because the canonical
`VAdd ι ι` satisfies `(+ᵥ) = (+)`, so this reduces to associativity of addition. -/
instance shift.gradedSMul (𝓐 : ι → σ') (𝓜 : ι → σ) (d : ι)
    [h : SetLike.GradedSMul 𝓐 𝓜] :
    SetLike.GradedSMul 𝓐 (shift 𝓜 d) where
  smul_mem {i j} {_a _b} hai hbj := by
    show _a • _b ∈ 𝓜 ((i +ᵥ j) + d)
    rw [show (i +ᵥ j) + d = i +ᵥ (j + d) from by simp [vadd_eq_add, add_assoc]]
    exact h.smul_mem hai hbj

end GradedSMul

section Decomposition

open scoped DirectSum

variable {M : Type*} {σ : Type*}
variable [AddCommGroup ι] [DecidableEq ι]
variable [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]

/-- Reindexing a direct sum via `comapDomain'` preserves the coercion sum.

This is the key lemma: reindexing `⨁ᵢ 𝓜 i` along `n ↦ n + d` and then summing
the components (via `coeAddMonoidHom`) gives the same result as summing directly. -/
private lemma coe_comapDomain'_eq_coe (𝓜 : ι → σ) (d : ι) (g : ⨁ i, 𝓜 i) :
    DirectSum.coeAddMonoidHom (shift 𝓜 d)
      (DFinsupp.comapDomain' (· + d) (h' := (· + (-d)))
        (fun k => add_neg_cancel_right k d) g) =
    DirectSum.coeAddMonoidHom 𝓜 g := by
  induction g using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    simp only [DirectSum.coeAddMonoidHom_of]
    obtain ⟨j, rfl⟩ : ∃ j, j + d = i := ⟨i + -d, by abel⟩
    rw [show (DirectSum.of (fun i => ↥(𝓜 i)) (j + d) x : ⨁ i, 𝓜 i) =
      DFinsupp.single (j + d) x from rfl,
      DFinsupp.comapDomain'_single]
    exact DirectSum.coeAddMonoidHom_of (shift 𝓜 d) j x
  | add x y hx hy =>
    rw [DFinsupp.comapDomain'_add, map_add, map_add, hx, hy]

/-- The shifted grading inherits a decomposition from the original grading.

Given a decomposition `M ≅ ⨁ₙ 𝓜 n`, we obtain `M ≅ ⨁ₙ 𝓜 (n + d)` by
reindexing the decomposition along `n ↦ n + d`: the degree-`n` component of the shifted
decomposition is the degree-`(n+d)` component of the original. -/
instance shift.decomposition (𝓜 : ι → σ) (d : ι)
    [DirectSum.Decomposition 𝓜] :
    DirectSum.Decomposition (shift 𝓜 d) where
  decompose' m :=
    DFinsupp.comapDomain' (· + d) (h' := (· + (-d)))
      (fun k => add_neg_cancel_right k d) (DirectSum.decompose 𝓜 m)
  left_inv m :=
    (coe_comapDomain'_eq_coe 𝓜 d (DirectSum.decompose 𝓜 m)).trans
      (DirectSum.Decomposition.left_inv m)
  right_inv f := by
    induction f using DirectSum.induction_on with
    | zero => simp
    | of k x =>
      simp only [DirectSum.coeAddMonoidHom_of, DirectSum.decompose_coe]
      exact @DFinsupp.comapDomain'_single ι (fun i => ↥(𝓜 i)) ι _ _ _
        (· + d) (· + (-d)) (fun k => add_neg_cancel_right k d) k x
    | add x y hx hy =>
      dsimp only at hx hy ⊢
      rw [map_add, DirectSum.decompose_add, DFinsupp.comapDomain'_add, hx, hy]

end Decomposition

/-! ### Integer shift for ℕ-graded modules -/

section IntShift

variable {σ : Type*} [Bot σ]

/-- Integer shift of an `ℕ`-graded type by `d : ℤ`. When `(n : ℤ) + d ≥ 0`, the degree-`n`
component is `𝓜 ((n : ℤ) + d).toNat`; otherwise it is `⊥`.

This extends `shift` to negative `d`: for `d ≥ 0`, `intShift 𝓜 d = shift 𝓜 d.toNat`.
The typical use case is `𝓜 = 𝒜` (the homogeneous submodules of a polynomial ring), where
`intShift 𝒜 d` represents the grading of the twisted sheaf `𝒪(d)` for any `d ∈ ℤ`. -/
def intShift (𝓜 : ℕ → σ) (d : ℤ) : ℕ → σ :=
  fun n => if 0 ≤ (n : ℤ) + d then 𝓜 ((n : ℤ) + d).toNat else ⊥

@[simp]
theorem intShift_apply_of_nonneg (𝓜 : ℕ → σ) (d : ℤ) (n : ℕ)
    (h : 0 ≤ (n : ℤ) + d) : intShift 𝓜 d n = 𝓜 ((n : ℤ) + d).toNat := by
  simp [intShift, h]

@[simp]
theorem intShift_apply_of_neg (𝓜 : ℕ → σ) (d : ℤ) (n : ℕ)
    (h : (n : ℤ) + d < 0) : intShift 𝓜 d n = ⊥ := by
  simp [intShift, not_le.mpr h]

/-- For `d ≥ 0`, `intShift` agrees with `shift`: `(n : ℤ) + d ≥ 0` always holds and
`((n : ℤ) + d).toNat = n + d.toNat`. -/
theorem intShift_eq_shift (𝓜 : ℕ → σ) (d : ℤ) (hd : 0 ≤ d) :
    intShift 𝓜 d = shift 𝓜 d.toNat := by
  ext n
  show (if 0 ≤ (n : ℤ) + d then 𝓜 ((n : ℤ) + d).toNat else ⊥) = 𝓜 (n + d.toNat)
  rw [if_pos (add_nonneg (Nat.cast_nonneg n) hd)]
  congr 1; omega

@[simp]
theorem intShift_zero (𝓜 : ℕ → σ) : intShift 𝓜 0 = 𝓜 := by
  ext n; simp [intShift]

end IntShift

end GradedModule
