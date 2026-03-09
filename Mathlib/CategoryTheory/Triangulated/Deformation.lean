/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.StabilityCondition
import Mathlib.CategoryTheory.Triangulated.StabilityFunction
import Mathlib.CategoryTheory.Triangulated.IntervalCategory
import Mathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian

set_option linter.style.longFile 3400

/-!
# Deformation of Stability Conditions

This file implements infrastructure for the deformation theorem (§7 of Bridgeland's
paper), which is the key technical ingredient for Theorem 1.2. Given a stability
condition `σ = (Z, P)` and a small perturbation `W` of the central charge `Z`, we
construct a new slicing `Q` such that `τ = (W, Q)` is a stability condition with
`d(P, Q)` small.

## Main definitions

* `CategoryTheory.Triangulated.StabilityCondition.exists_epsilon0`: extraction of `ε₀`
  from the local finiteness axiom (**Node 7.0**)

## Main results

* `CategoryTheory.Triangulated.intervalProp_of_semistable_near`: a `τ`-semistable object
  lies in the `σ`-interval `P((φ - ε, φ + ε))` when `d(P, Q) < ε`
* `CategoryTheory.Triangulated.phiPlus_phiMinus_in_interval`: intrinsic phase bounds
  from interval membership

## References

* Bridgeland, "Stability conditions on triangulated categories", §7
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Node 7.0: ε₀ extraction from local finiteness -/

/-- **Node 7.0: Extraction of ε₀**. Given a stability condition `σ`, extract a positive
real `ε₀ < 1/8` such that for all `t`, every object in `P((t - 4ε₀, t + 4ε₀))` has
well-founded subobject lattice. The width `8ε₀` is chosen to fit inside the local
finiteness parameter `2η`. -/
theorem StabilityCondition.exists_epsilon0 (σ : StabilityCondition C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 8 ∧
      ∀ t : ℝ, ∀ (E : C),
        σ.slicing.intervalProp C (t - 4 * ε₀) (t + 4 * ε₀) E →
          Finite (Subobject E) := by
  obtain ⟨η, hη, hlf⟩ := σ.locallyFinite
  refine ⟨min (η / 4) (1 / 16), by positivity,
    by linarith [min_le_right (η / 4) (1 / 16 : ℝ)],
    fun t E hI ↦ ?_⟩
  exact σ.slicing.intervalFiniteLength C hI (η := η)
    (by have h := min_le_left (η / 4) (1 / 16 : ℝ); linarith) hlf

/-- Variant of ε₀ extraction providing 2ε₀-intervals for the sector bound. -/
theorem StabilityCondition.exists_epsilon0_sector (σ : StabilityCondition C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧
      ∀ t : ℝ, ∀ (E : C),
        σ.slicing.intervalProp C (t - 2 * ε₀) (t + 2 * ε₀) E →
          Finite (Subobject E) := by
  obtain ⟨η, hη, hlf⟩ := σ.locallyFinite
  refine ⟨min (η / 2) (1 / 8), by positivity,
    by linarith [min_le_right (η / 2) (1 / 8 : ℝ)],
    fun t E hI ↦ ?_⟩
  exact σ.slicing.intervalFiniteLength C hI (η := η)
    (by have h := min_le_left (η / 2) (1 / 8 : ℝ); linarith) hlf

/-! ### Phase confinement for nearby stability conditions -/

/-- **Phase confinement**. If `d(σ.P, τ.P) < ε` and `E` is `τ`-semistable of phase `φ`,
then `E` lies in the `σ`-interval subcategory `P((φ - ε, φ + ε))`. This is the
fundamental input for the deformation construction. -/
theorem intervalProp_of_semistable_near (σ τ : StabilityCondition C) {E : C} {φ ε : ℝ}
    (hE : ¬IsZero E) (hτ : (τ.slicing.P φ) E)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε) :
    σ.slicing.intervalProp C (φ - ε) (φ + ε) E := by
  have hbds := intervalProp_of_semistable_slicingDist C σ.slicing τ.slicing hE hτ hd
  right
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  refine ⟨F, fun i ↦ ?_⟩
  have hP_bds := hbds.1
  have hM_bds := hbds.2
  rw [Set.mem_Ioo] at hP_bds hM_bds
  constructor
  · calc φ - ε < σ.slicing.phiMinus C E hE := hM_bds.1
      _ = F.φ ⟨F.n - 1, by omega⟩ := σ.slicing.phiMinus_eq C E hE F hn hlast
      _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
  · calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
      _ = σ.slicing.phiPlus C E hE :=
          (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
      _ < φ + ε := hP_bds.2

/-- Embedding an interval in a wider one centered at the same point. -/
theorem intervalProp_widen (s : Slicing C) {E : C} {φ ε ε' : ℝ}
    (hI : s.intervalProp C (φ - ε) (φ + ε) E) (hle : ε ≤ ε') :
    s.intervalProp C (φ - ε') (φ + ε') E :=
  s.intervalProp_mono C (by linarith) (by linarith) hI

/-! ### Intrinsic phase bounds from interval membership -/

/-- If `E ∈ P((φ - ε, φ + ε))` and `E` is nonzero, then both `φ⁺(E)` and `φ⁻(E)` lie
in `(φ - ε, φ + ε)`. This uses the existing `phiPlus/phiMinus_gt/lt_of_intervalProp`
lemmas. -/
theorem phiPlus_phiMinus_in_interval (s : Slicing C) {E : C} (hE : ¬IsZero E)
    {φ ε : ℝ} (hI : s.intervalProp C (φ - ε) (φ + ε) E) :
    φ - ε < s.phiPlus C E hE ∧ s.phiPlus C E hE < φ + ε ∧
    φ - ε < s.phiMinus C E hE ∧ s.phiMinus C E hE < φ + ε :=
  ⟨s.phiPlus_gt_of_intervalProp C hE hI, s.phiPlus_lt_of_intervalProp C hE hI,
   s.phiMinus_gt_of_intervalProp C hE hI, s.phiMinus_lt_of_intervalProp C hE hI⟩

/-- If `d(P, Q) < ε` and `E` is `τ`-semistable of phase `φ`, then both `σ.φ⁺(E)` and
`σ.φ⁻(E)` lie in `(φ - ε, φ + ε)`. -/
theorem phiPlus_phiMinus_near (σ τ : StabilityCondition C) {E : C} {φ ε : ℝ}
    (hE : ¬IsZero E) (hτ : (τ.slicing.P φ) E)
    (hd : slicingDist C σ.slicing τ.slicing < ENNReal.ofReal ε) :
    φ - ε < σ.slicing.phiPlus C E hE ∧ σ.slicing.phiPlus C E hE < φ + ε ∧
    φ - ε < σ.slicing.phiMinus C E hE ∧ σ.slicing.phiMinus C E hE < φ + ε :=
  phiPlus_phiMinus_in_interval C σ.slicing hE
    (intervalProp_of_semistable_near C σ τ hE hτ hd)

/-! ### Distance bound infrastructure -/

/-- If `σ` and `τ` have pointwise phase bounds, then `d(P, Q) ≤ ε`. -/
theorem StabilityCondition.slicingDist_le_of_near (σ τ : StabilityCondition C)
    {ε : ℝ}
    (hP : ∀ (E : C) (hE : ¬IsZero E),
      |σ.slicing.phiPlus C E hE - τ.slicing.phiPlus C E hE| ≤ ε)
    (hM : ∀ (E : C) (hE : ¬IsZero E),
      |σ.slicing.phiMinus C E hE - τ.slicing.phiMinus C E hE| ≤ ε) :
    slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε :=
  slicingDist_le_of_phase_bounds C σ.slicing τ.slicing hP hM

/-! ### Node 7.2a: W restricts to a skewed stability function -/

/-- **W-nonvanishing**. If the seminorm `‖W - Z‖_σ < 1`, then `W([E]) ≠ 0` for every
nonzero `σ`-semistable object `E`. The proof uses the triangle inequality:
`‖W([E])‖ ≥ ‖Z([E])‖ - ‖(W-Z)([E])‖ ≥ (1 - M) · ‖Z([E])‖ > 0`. -/
theorem StabilityCondition.W_ne_zero_of_seminorm_lt_one (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    W (K₀.of C E) ≠ 0 := by
  have hfin : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hW
  set M := (stabSeminorm C σ (W - σ.Z)).toReal
  have hM1 : M < 1 := by
    rw [show (1 : ℝ) = (ENNReal.ofReal 1).toReal from
      (ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1)).symm]
    exact (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hW
  -- Z([E]) = m · exp(iπφ) with m > 0, so ‖Z([E])‖ = m > 0
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  have hZ_pos : (0 : ℝ) < ‖σ.Z (K₀.of C E)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  -- ‖(W - Z)([E])‖ ≤ M · ‖Z([E])‖
  have hbd := stabSeminorm_bound_real C σ (W - σ.Z) hfin hP hE
  -- If W([E]) = 0, then (W - Z)([E]) = -Z([E]), so ‖(W-Z)([E])‖ = ‖Z([E])‖
  -- But ‖(W-Z)([E])‖ ≤ M · ‖Z([E])‖ with M < 1, contradicting ‖Z([E])‖ > 0
  intro hw0
  have hWZ : (W - σ.Z) (K₀.of C E) = W (K₀.of C E) - σ.Z (K₀.of C E) :=
    AddMonoidHom.sub_apply W σ.Z (K₀.of C E)
  rw [hWZ, hw0, zero_sub, norm_neg] at hbd
  nlinarith

/-- **Node 7.2a**. Given a stability condition `σ` and a group homomorphism `W` with
`‖W - Z‖_σ < 1`, `W` restricts to a `SkewedStabilityFunction` on any interval `(a, b)`
with `a < b`. The skewing parameter is `(a + b) / 2`. -/
def StabilityCondition.skewedStabilityFunction_of_near (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hab : a < b) :
    SkewedStabilityFunction C σ.slicing a b where
  W := W
  α := (a + b) / 2
  hα_mem := ⟨by linarith, by linarith⟩
  nonzero := fun E φ _ _ hP hE ↦
    σ.W_ne_zero_of_seminorm_lt_one C W hW hP hE

/-! ### Z-nonvanishing for interval objects -/

/-- **Z-nonvanishing for interval objects**. For a nonzero object `E` in a thin interval
`P((a, b))` with `b - a < 1`, the central charge satisfies `‖Z([E])‖ > 0`. The proof
decomposes `E` via its HN filtration and applies the sector estimate
`norm_sum_exp_ge_cos_mul_sum` to bound `‖Z(E)‖` from below. -/
theorem StabilityCondition.norm_Z_pos_of_intervalProp (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E) {a b : ℝ} (hab : b - a < 1)
    (hI : σ.slicing.intervalProp C a b E) :
    0 < ‖σ.Z (K₀.of C E)‖ := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  -- All HN phases are in (a, b)
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := by
    intro i
    constructor
    · calc a < σ.slicing.phiMinus C E hE :=
            σ.slicing.phiMinus_gt_of_intervalProp C hE hI
        _ = F.φ ⟨F.n - 1, by omega⟩ :=
            σ.slicing.phiMinus_eq C E hE F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
    · calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = σ.slicing.phiPlus C E hE :=
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI
  set P := F.toPostnikovTower
  -- K₀ decomposition: Z(E) = Σ Z(Fᵢ) = Σ ‖Z(Fᵢ)‖ * exp(iπφᵢ)
  have hZE : σ.Z (K₀.of C E) =
      ∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  have hZi : ∀ i : Fin F.n,
      σ.Z (K₀.of C (P.factor i)) =
      ↑(‖σ.Z (K₀.of C (P.factor i))‖) *
        Complex.exp (↑(Real.pi * F.φ i) * Complex.I) := by
    intro i
    by_cases hi : IsZero (P.factor i)
    · simp [K₀.of_isZero C hi]
    · obtain ⟨m, hm, hmZ⟩ :=
        σ.compat (F.φ i) (P.factor i) (F.semistable i) hi
      rw [hmZ]; congr 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  -- Derive a < b from existence of phases
  have hab_pos : 0 < b - a := by
    linarith [(hphases ⟨0, hn⟩).1, (hphases ⟨0, hn⟩).2]
  -- Sector estimate setup
  have hw : Real.pi * (b - a) < Real.pi := by
    nlinarith [Real.pi_pos]
  have hw0 : 0 ≤ Real.pi * (b - a) :=
    mul_nonneg Real.pi_pos.le hab_pos.le
  have hθ : ∀ i : Fin F.n,
      Real.pi * F.φ i ∈ Set.Icc (Real.pi * a)
        (Real.pi * a + Real.pi * (b - a)) := by
    intro i; simp only [Set.mem_Icc]
    exact ⟨mul_le_mul_of_nonneg_left (hphases i).1.le Real.pi_pos.le,
      by nlinarith [(hphases i).2.le, Real.pi_pos]⟩
  -- Apply sector estimate
  have hsector :
      Real.cos (Real.pi * (b - a) / 2) *
        ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖ ≤
      ‖σ.Z (K₀.of C E)‖ := by
    calc Real.cos (Real.pi * (b - a) / 2) *
            ∑ i : Fin F.n, ‖σ.Z (K₀.of C (P.factor i))‖
        ≤ ‖∑ i : Fin F.n,
            ↑(‖σ.Z (K₀.of C (P.factor i))‖) *
              Complex.exp (↑(Real.pi * F.φ i) * Complex.I)‖ :=
          norm_sum_exp_ge_cos_mul_sum
            (fun i _ ↦ norm_nonneg _) hw0 hw (fun i _ ↦ hθ i)
      _ = ‖∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i))‖ := by
          congr 1; exact Finset.sum_congr rfl (fun i _ ↦ (hZi i).symm)
      _ = ‖σ.Z (K₀.of C E)‖ := by rw [← hZE]
  -- First factor is nonzero, so ‖Z(F₀)‖ > 0
  have hfactor_pos :
      0 < ‖σ.Z (K₀.of C (P.factor ⟨0, hn⟩))‖ := by
    obtain ⟨m, hm, hmZ⟩ :=
      σ.compat _ _ (F.semistable ⟨0, hn⟩) hfirst
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hm
  have hcos_pos : 0 < Real.cos (Real.pi * (b - a) / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hsum_pos : 0 < ∑ i : Fin F.n,
      ‖σ.Z (K₀.of C (P.factor i))‖ := by
    apply lt_of_lt_of_le hfactor_pos
    exact Finset.single_le_sum
      (f := fun i ↦ ‖σ.Z (K₀.of C (P.factor i))‖)
      (fun i _ ↦ norm_nonneg _)
      (Finset.mem_univ (⟨0, hn⟩ : Fin F.n))
  exact lt_of_lt_of_le (mul_pos hcos_pos hsum_pos) hsector

/-- **W-nonvanishing for interval objects**. If `‖W - Z‖_σ < cos(π(b-a)/2)` and `E` is
a nonzero object in `P((a, b))` with `b - a < 1`, then `W([E]) ≠ 0`. The proof combines
the Z-nonvanishing bound with the sector bound on `W - Z`. -/
theorem StabilityCondition.W_ne_zero_of_intervalProp (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) {a b : ℝ} (hab : b - a < 1)
    (hsmall : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * (b - a) / 2)))
    {E : C} (hE : ¬IsZero E) (hI : σ.slicing.intervalProp C a b E) :
    W (K₀.of C E) ≠ 0 := by
  -- Derive a < b
  have hab_pos : 0 < b - a := by
    rcases hI with hZ | ⟨F, hF⟩
    · exact absurd hZ hE
    · have hn : 0 < F.n := by
        by_contra h; exact hE (F.toPostnikovTower.zero_isZero (by omega))
      linarith [(hF ⟨0, hn⟩).1, (hF ⟨0, hn⟩).2]
  have hcos_pos : 0 < Real.cos (Real.pi * (b - a) / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hfin : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hsmall
  set M := (stabSeminorm C σ (W - σ.Z)).toReal
  have hM_lt : M < Real.cos (Real.pi * (b - a) / 2) := by
    rw [show Real.cos _ = (ENNReal.ofReal (Real.cos _)).toReal from
      (ENNReal.toReal_ofReal hcos_pos.le).symm]
    exact (ENNReal.toReal_lt_toReal hfin
      ENNReal.ofReal_ne_top).mpr hsmall
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  -- Z(E) ≠ 0
  have hZ_pos := σ.norm_Z_pos_of_intervalProp C hE hab hI
  -- ‖(W-Z)(E)‖ ≤ M / cos(π(b-a)/2) · ‖Z(E)‖ via sector bound
  have hwidth : σ.slicing.phiPlus C E hE -
      σ.slicing.phiMinus C E hE ≤ b - a := by
    have hP := σ.slicing.phiPlus_lt_of_intervalProp C hE hI
    have hM := σ.slicing.phiMinus_gt_of_intervalProp C hE hI
    linarith
  have hWZ_bound : ‖(W - σ.Z) (K₀.of C E)‖ ≤
      M / Real.cos (Real.pi * (b - a) / 2) *
        ‖σ.Z (K₀.of C E)‖ :=
    sector_bound' C σ (W - σ.Z) hE hab_pos.le
      hab hwidth hM0
      (fun A φ hP hA ↦ stabSeminorm_bound_real C σ _ hfin hP hA)
  -- M / cos < 1, so ‖(W-Z)(E)‖ < ‖Z(E)‖
  have hrat : M / Real.cos (Real.pi * (b - a) / 2) < 1 :=
    (div_lt_one hcos_pos).mpr hM_lt
  -- If W(E) = 0, then ‖(W-Z)(E)‖ = ‖Z(E)‖, contradicting the bound
  intro hw0
  have hWZ : (W - σ.Z) (K₀.of C E) =
      W (K₀.of C E) - σ.Z (K₀.of C E) :=
    AddMonoidHom.sub_apply W σ.Z (K₀.of C E)
  rw [hWZ, hw0, zero_sub, norm_neg] at hWZ_bound
  nlinarith

/-! ### W-phase definition -/

/-- The **W-phase** of a complex number `w ≠ 0` relative to a skewing parameter `α`.
Defined as `α + arg(w · exp(-iπα)) / π`, which gives ψ ∈ (α - 1, α + 1] satisfying
`w = ‖w‖ · exp(iπψ)`. -/
noncomputable def wPhaseOf (w : ℂ) (α : ℝ) : ℝ :=
  α + Complex.arg (w * Complex.exp (-(↑(Real.pi * α) * Complex.I))) /
    Real.pi

/-- The W-phase lies in `(α - 1, α + 1]`. -/
theorem wPhaseOf_mem_Ioc (w : ℂ) (α : ℝ) :
    wPhaseOf w α ∈ Set.Ioc (α - 1) (α + 1) := by
  have hπ := Real.pi_pos
  set z := w * Complex.exp (-(↑(Real.pi * α) * Complex.I))
  refine ⟨?_, ?_⟩
  · -- α - 1 < α + arg(z)/π
    suffices -1 < Complex.arg z / Real.pi by
      change α - 1 < α + Complex.arg z / Real.pi; linarith
    rw [lt_div_iff₀ hπ]
    linarith [Complex.neg_pi_lt_arg z]
  · -- α + arg(z)/π ≤ α + 1
    suffices Complex.arg z / Real.pi ≤ 1 by
      change α + Complex.arg z / Real.pi ≤ α + 1; linarith
    rw [div_le_iff₀ hπ, one_mul]
    exact Complex.arg_le_pi z

/-- **Polar compatibility**. A nonzero complex number `w` equals
`‖w‖ * exp(iπ · wPhaseOf w α)`. -/
theorem wPhaseOf_compat (w : ℂ) (α : ℝ) :
    w = ↑‖w‖ * Complex.exp (↑(Real.pi * wPhaseOf w α) * Complex.I) := by
  set z := w * Complex.exp (-(↑(Real.pi * α) * Complex.I)) with hz_def
  -- Step 1: w = z * exp(iπα)
  have hw_eq : w = z * Complex.exp (↑(Real.pi * α) * Complex.I) := by
    rw [hz_def, mul_assoc, ← Complex.exp_add]
    simp [neg_add_cancel]
  -- Step 2: polar decomposition of z
  have polar := Complex.norm_mul_exp_arg_mul_I z
  -- Step 3: ‖z‖ = ‖w‖
  have hnorm : (‖z‖ : ℝ) = ‖w‖ := by
    rw [hz_def, norm_mul]
    have : -(↑(Real.pi * α) * Complex.I) =
        ↑(-(Real.pi * α)) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
  -- Step 4: arg z + πα = π * wPhaseOf w α
  have hphase : ↑(Complex.arg z) * Complex.I +
      ↑(Real.pi * α) * Complex.I =
      ↑(Real.pi * wPhaseOf w α) * Complex.I := by
    have h : Complex.arg z + Real.pi * α = Real.pi * wPhaseOf w α := by
      change z.arg + Real.pi * α = Real.pi * (α + z.arg / Real.pi)
      field_simp; ring
    rw [← h]; push_cast; ring
  calc w = z * Complex.exp (↑(Real.pi * α) * Complex.I) := hw_eq
    _ = ↑‖z‖ * Complex.exp (↑(Complex.arg z) * Complex.I) *
          Complex.exp (↑(Real.pi * α) * Complex.I) := by
        rw [polar]
    _ = ↑‖z‖ * (Complex.exp (↑(Complex.arg z) * Complex.I) *
          Complex.exp (↑(Real.pi * α) * Complex.I)) := by
        rw [mul_assoc]
    _ = ↑‖z‖ * Complex.exp (↑(Real.pi * wPhaseOf w α) *
          Complex.I) := by
        rw [← Complex.exp_add, hphase]
    _ = ↑‖w‖ * Complex.exp (↑(Real.pi * wPhaseOf w α) *
          Complex.I) := by
        rw [hnorm]

/-- The W-phase of `m * exp(iπφ)` with `m > 0` and `φ ∈ (α - 1, α + 1]` equals `φ`. -/
theorem wPhaseOf_of_exp {m φ α : ℝ} (hm : 0 < m)
    (hφ : φ ∈ Set.Ioc (α - 1) (α + 1)) :
    wPhaseOf (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)) α = φ := by
  unfold wPhaseOf
  suffices h : Complex.arg (↑m * Complex.exp (↑(Real.pi * φ) *
      Complex.I) * Complex.exp (-(↑(Real.pi * α) * Complex.I))) =
      Real.pi * (φ - α) by
    rw [h]; field_simp; ring
  -- Simplify: m * exp(iπφ) * exp(-iπα) = m * exp(iπ(φ-α))
  have hexp : ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) *
      Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      ↑m * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hexp, Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I,
    toIocMod_eq_self]
  exact ⟨by nlinarith [Real.pi_pos, hφ.1], by nlinarith [Real.pi_pos, hφ.2]⟩

/-- **W-phase of zero.** `wPhaseOf(0, α) = α` since `arg(0) = 0`. -/
@[simp]
theorem wPhaseOf_zero (α : ℝ) : wPhaseOf 0 α = α := by
  simp [wPhaseOf, Complex.arg_zero]

/-- **Negation shifts W-phase by 1.** For nonzero `w`, `wPhaseOf(-w, α+1) = wPhaseOf(w, α) + 1`.
Since `exp(iπ) = -1`, negating `w` shifts the argument by π, hence the phase by 1. -/
theorem wPhaseOf_neg {w : ℂ} (hw : w ≠ 0) (α : ℝ) :
    wPhaseOf (-w) (α + 1) = wPhaseOf w α + 1 := by
  set φ := wPhaseOf w α
  have hm : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hpolar := wPhaseOf_compat w α
  -- -w = ‖w‖ · exp(iπ(φ + 1)) since exp(iπ) = -1
  -- Use wPhaseOf_of_exp on -w = ‖w‖ · exp(iπ(φ+1))
  -- φ + 1 ∈ ((α+1) - 1, (α+1) + 1] = (α, α + 2]
  have hmem : φ + 1 ∈ Set.Ioc ((α + 1) - 1) ((α + 1) + 1) := by
    have := wPhaseOf_mem_Ioc w α
    constructor <;> linarith [this.1, this.2]
  -- wPhaseOf(-w, α+1) = wPhaseOf(‖w‖ · exp(iπ(φ+1)), α+1) = φ+1
  -- First establish: -w = ‖w‖ · exp(iπ(φ+1))
  suffices hneg : -w = ↑‖w‖ * Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I) by
    calc wPhaseOf (-w) (α + 1)
        = wPhaseOf (↑‖w‖ * Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I))
            (α + 1) := by rw [← hneg]
      _ = φ + 1 := wPhaseOf_of_exp hm hmem
  -- Prove -w = ‖w‖ · exp(iπ(φ+1))
  calc -w = -(↑‖w‖ * Complex.exp (↑(Real.pi * φ) * Complex.I)) := by
        rw [← hpolar]
    _ = ↑‖w‖ * (-Complex.exp (↑(Real.pi * φ) * Complex.I)) := by ring
    _ = ↑‖w‖ * (Complex.exp (↑Real.pi * Complex.I) *
          Complex.exp (↑(Real.pi * φ) * Complex.I)) := by
        rw [Complex.exp_pi_mul_I]; ring
    _ = ↑‖w‖ * Complex.exp (↑Real.pi * Complex.I +
          ↑(Real.pi * φ) * Complex.I) := by
        rw [Complex.exp_add]
    _ = ↑‖w‖ * Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I) := by
        congr 1; congr 1; push_cast; ring

/-- **Shifting α by 2 shifts wPhaseOf by 2.** For nonzero `w`,
`wPhaseOf w (α + 2) = wPhaseOf w α + 2`. Derived by applying `wPhaseOf_neg` twice. -/
theorem wPhaseOf_add_two {w : ℂ} (hw : w ≠ 0) (α : ℝ) :
    wPhaseOf w (α + 2) = wPhaseOf w α + 2 := by
  have h1 := wPhaseOf_neg hw α
  have h2 := wPhaseOf_neg (neg_ne_zero.mpr hw) (α + 1)
  rw [neg_neg, show (α + 1 : ℝ) + 1 = α + 2 from by ring] at h2
  linarith

/-! ### W-semistability in interval categories -/

/-- **W-semistability**. An object `E` in `P((a, b))` is *W-semistable* of W-phase `ψ` if:
1. `E` is in the interval `P((a, b))` and is nonzero,
2. `W([E]) ≠ 0` (so the W-phase is well-defined),
3. The W-phase of `E` equals `ψ`,
4. For every distinguished triangle `K → E → Q → K[1]` with both `K, Q ∈ P((a, b))`
   and `K` nonzero, the W-phase of `K` is at most `ψ`.

A "strict subobject" of `E` in `P((a,b))` corresponds to a monomorphism in the abelian
heart `P((a, a+1])` whose cokernel also lies in `P((a, b))`, which in turn gives a
distinguished triangle with all vertices in the interval. -/
def SkewedStabilityFunction.Semistable {s : Slicing C} {a b : ℝ}
    (ssf : SkewedStabilityFunction C s a b) (E : C) (ψ : ℝ) : Prop :=
  s.intervalProp C a b E ∧ ¬IsZero E ∧
  ssf.W (K₀.of C E) ≠ 0 ∧
  wPhaseOf (ssf.W (K₀.of C E)) ssf.α = ψ ∧
  ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ E⦄ ⦃f₂ : E ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
    Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
    s.intervalProp C a b K → s.intervalProp C a b Q →
    ¬IsZero K →
    wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤ ψ

/-- **α-independence of wPhaseOf.** For a nonzero complex number `w`, if
`wPhaseOf w α₁ ∈ (α₂ - 1, α₂ + 1]`, then `wPhaseOf w α₁ = wPhaseOf w α₂`.
This shows the W-phase is intrinsic (independent of the skewing parameter),
provided the branch cuts are compatible. -/
theorem wPhaseOf_indep {w : ℂ} (hw : w ≠ 0) (α₁ α₂ : ℝ)
    (h : wPhaseOf w α₁ ∈ Set.Ioc (α₂ - 1) (α₂ + 1)) :
    wPhaseOf w α₁ = wPhaseOf w α₂ := by
  set φ := wPhaseOf w α₁
  have hw_polar := wPhaseOf_compat w α₁
  have hm : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : wPhaseOf (↑‖w‖ * Complex.exp (↑(Real.pi * φ) * Complex.I)) α₂ = φ :=
    wPhaseOf_of_exp hm h
  rw [← hw_polar] at h1; exact h1.symm

/-- The W-phase of a W-semistable object is in `(α - 1, α + 1]`. -/
lemma SkewedStabilityFunction.Semistable.phase_mem_Ioc
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b} {E : C} {ψ : ℝ}
    (h : ssf.Semistable C E ψ) :
    ψ ∈ Set.Ioc (ssf.α - 1) (ssf.α + 1) :=
  h.2.2.2.1 ▸ wPhaseOf_mem_Ioc _ _

/-- The W-value of a W-semistable object satisfies the polar decomposition. -/
lemma SkewedStabilityFunction.Semistable.polar
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b} {E : C} {ψ : ℝ}
    (h : ssf.Semistable C E ψ) :
    ssf.W (K₀.of C E) = ↑‖ssf.W (K₀.of C E)‖ *
      Complex.exp (↑(Real.pi * ψ) * Complex.I) :=
  h.2.2.2.1 ▸ wPhaseOf_compat _ _

/-! ### Phase perturbation estimates -/

section PhasePerturbation

/-- **Core geometric inequality**. For any complex number `z`, `z.im² ≤ ‖z‖² · ‖z - 1‖²`.
Equivalently, the perpendicular distance from `1` to the line through `0` and `z` is at most
`‖z - 1‖`. The proof uses the algebraic identity
`‖z‖² · ‖z - 1‖² - z.im² = (‖z‖² - z.re)² ≥ 0`. -/
theorem im_sq_le_norm_sq_mul (z : ℂ) :
    z.im ^ 2 ≤ ‖z - 1‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm (z - 1), Complex.sq_norm z]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [sq_nonneg (z.re * z.re + z.im * z.im - z.re)]

/-- For any nonzero `z : ℂ`, `|sin(arg z)| ≤ ‖z - 1‖`. This is the law-of-sines bound: the
side `|z - 1|` opposite the angle `arg z` at `0` in the triangle `0-1-z` satisfies
`|z - 1| ≥ sin(arg z)` since the circumradius is at least `1/2`. -/
theorem abs_sin_arg_le_norm_sub_one {z : ℂ} (hz : z ≠ 0) :
    |Real.sin (Complex.arg z)| ≤ ‖z - 1‖ := by
  rw [Complex.sin_arg, abs_div, abs_of_pos (norm_pos_iff.mpr hz),
    div_le_iff₀ (norm_pos_iff.mpr hz)]
  exact le_of_sq_le_sq (by rw [sq_abs, mul_pow]; exact im_sq_le_norm_sq_mul z) (by positivity)

/-- `sin(|x|) = |sin(x)|` for `|x| < π/2`. -/
theorem sin_abs_eq_abs_sin {x : ℝ} (hx : |x| < Real.pi / 2) :
    Real.sin |x| = |Real.sin x| := by
  rcases le_or_gt 0 x with h | h
  · have hx' : x < Real.pi / 2 := by rwa [abs_of_nonneg h] at hx
    rw [abs_of_nonneg h, abs_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]))]
  · have hx' : -x < Real.pi / 2 := by rwa [abs_of_neg h] at hx
    have hsin : Real.sin x < 0 := by
      have : 0 < Real.sin (-x) :=
        Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h) (by linarith [Real.pi_pos])
      linarith [Real.sin_neg x]
    rw [abs_of_neg h, Real.sin_neg, abs_of_neg hsin]

/-- **Phase bound for near-identity perturbation**. If `‖u‖ < sin(πε)` with `0 < ε ≤ 1/2`,
then `|arg(1 + u)| < πε`. The proof combines `abs_sin_arg_le_norm_sub_one` (the law-of-sines
bound) with strict monotonicity of sine on `[0, π/2]`. -/
theorem abs_arg_one_add_lt {u : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hu : ‖u‖ < Real.sin (Real.pi * ε)) :
    |Complex.arg (1 + u)| < Real.pi * ε := by
  have hπ := Real.pi_pos
  have hπε2 : Real.pi * ε ≤ Real.pi / 2 := by nlinarith
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  -- 1 + u ≠ 0
  have hz : (1 : ℂ) + u ≠ 0 := by
    intro h
    have h1 : (1 : ℂ) = -u := eq_neg_of_add_eq_zero_left h
    have h2 : ‖(1 : ℂ)‖ = ‖u‖ := by rw [h1, norm_neg]
    rw [norm_one] at h2; linarith
  -- Re(1+u) > 0 ⟹ |arg(1+u)| < π/2
  have hre : 0 < ((1 : ℂ) + u).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_le_of_abs_le (Complex.abs_re_le_norm u)]
  have harg_lt : |Complex.arg ((1 : ℂ) + u)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  -- sin(|arg(1+u)|) = |sin(arg(1+u))| ≤ ‖u‖ < sin(πε)
  have hsin_le : |Real.sin (Complex.arg ((1 : ℂ) + u))| ≤ ‖u‖ := by
    calc |Real.sin (Complex.arg ((1 : ℂ) + u))| ≤ ‖(1 : ℂ) + u - 1‖ :=
          abs_sin_arg_le_norm_sub_one hz
      _ = ‖u‖ := by congr 1; ring
  have hsin_abs := sin_abs_eq_abs_sin harg_lt
  -- By strict monotonicity of sin: |arg(1+u)| < πε
  by_contra h
  push_neg at h
  have hmono : Real.sin (Real.pi * ε) ≤ Real.sin (|Complex.arg ((1 : ℂ) + u)|) :=
    Real.monotoneOn_sin ⟨by nlinarith [mul_pos hπ hε], hπε2⟩
      ⟨by linarith [abs_nonneg (Complex.arg ((1 : ℂ) + u)), hπ], harg_lt.le⟩ h
  linarith [hsin_abs]

/-- **Generic phase perturbation bound**. If `w = m · exp(iπφ) · (1 + u)` with `m > 0`,
`φ ∈ (α - 1/2, α + 1/2)`, and `‖u‖ < sin(πε)` with `0 < ε ≤ 1/2`, then
`|wPhaseOf(w, α) - φ| < ε`. The proof splits `arg` of the product using `arg_mul`,
computes `arg(m · exp(iπ(φ-α))) = π(φ-α)`, and bounds `|arg(1+u)| < πε`. -/
theorem wPhaseOf_perturbation_generic {m φ α ε : ℝ} {u : ℂ}
    (hm : 0 < m) (hφ : φ ∈ Set.Ioo (α - 1 / 2) (α + 1 / 2))
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : ‖u‖ < Real.sin (Real.pi * ε)) :
    |wPhaseOf (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) *
      ((1 : ℂ) + u)) α - φ| < ε := by
  have hπ := Real.pi_pos
  have hπε2 : Real.pi * ε ≤ Real.pi / 2 := by nlinarith
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  -- 1 + u ≠ 0
  have hz2 : (1 : ℂ) + u ≠ 0 := by
    intro h; have h1 : (1 : ℂ) = -u := eq_neg_of_add_eq_zero_left h
    have h2 : ‖(1 : ℂ)‖ = ‖u‖ := by rw [h1, norm_neg]
    rw [norm_one] at h2; linarith
  -- Step 1: |arg(1+u)| < πε
  have harg_u : |Complex.arg ((1 : ℂ) + u)| < Real.pi * ε :=
    abs_arg_one_add_lt hε hε2 hu
  -- Step 2: Reassemble w · exp(-iπα) = (m · exp(iπ(φ-α))) · (1+u)
  have hexp_combine : Complex.exp (↑(Real.pi * φ) * Complex.I) *
      Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      Complex.exp (↑(Real.pi * (φ - α)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hreassoc : ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) *
      ((1 : ℂ) + u) * Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      (↑m * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)) *
        ((1 : ℂ) + u) := by
    have h := hexp_combine
    calc _ = ↑m * (Complex.exp (↑(Real.pi * φ) * Complex.I) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I))) * ((1 : ℂ) + u) := by ring
      _ = _ := by rw [h]
  -- Step 3: arg of z₁ = m · exp(iπ(φ-α))
  set z₁ := (↑m : ℂ) * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)
  have hz1 : z₁ ≠ 0 := mul_ne_zero
    (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)
  have hφα : |φ - α| < 1 / 2 := abs_lt.mpr ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have harg1 : Complex.arg z₁ = Real.pi * (φ - α) := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    exact ⟨by nlinarith [mul_pos hπ (show (0 : ℝ) < 1 + (φ - α) from by linarith [hφ.1])],
           by nlinarith [mul_pos hπ (show (0 : ℝ) < 1 - (φ - α) from by linarith [hφ.2])]⟩
  -- Step 4: arg(z₁) + arg(z₂) ∈ Ioc(-π, π), apply arg_mul
  set z₂ := (1 : ℂ) + u
  have hsum_mem : Complex.arg z₁ + Complex.arg z₂ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [harg1]
    have h1 := (abs_lt.mp harg_u).1
    have h2 := (abs_lt.mp harg_u).2
    constructor
    · -- -π < π(φ-α) + arg(z₂)
      have : -(Real.pi / 2) < Real.pi * (φ - α) := by
        nlinarith [mul_pos hπ (show (0 : ℝ) < 1 / 2 + (φ - α) from by linarith [hφ.1])]
      linarith
    · -- π(φ-α) + arg(z₂) ≤ π
      have : Real.pi * (φ - α) < Real.pi / 2 := by
        nlinarith [mul_pos hπ (show (0 : ℝ) < 1 / 2 - (φ - α) from by linarith [hφ.2])]
      linarith
  have harg_prod : Complex.arg (z₁ * z₂) = Complex.arg z₁ + Complex.arg z₂ :=
    Complex.arg_mul hz1 hz2 hsum_mem
  -- Step 5: Compute wPhaseOf
  unfold wPhaseOf
  rw [hreassoc, harg_prod, harg1]
  -- α + (π(φ-α) + arg(z₂)) / π - φ = arg(z₂) / π
  have hsimpl : α + (Real.pi * (φ - α) + Complex.arg z₂) / Real.pi - φ =
      Complex.arg z₂ / Real.pi := by field_simp; ring
  rw [hsimpl, abs_div, abs_of_pos hπ, div_lt_iff₀ hπ]
  linarith [harg_u]

end PhasePerturbation

/-! ### Arg convexity for finite sums -/

section ArgConvexity

open Complex

/-- A Finset sum of upper half-plane vectors is in the upper half-plane union. -/
theorem sum_mem_upperHalfPlane {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion) :
    ∑ i ∈ s, f i ∈ upperHalfPlaneUnion := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simpa using hf j (Finset.mem_singleton_self j)
  | cons j s hjs hs ih =>
    rw [Finset.sum_cons]
    exact mem_upperHalfPlaneUnion_of_add
      (hf j (Finset.mem_cons_self j s))
      (ih (fun i hi ↦ hf i (Finset.mem_cons.mpr (Or.inr hi))))

/-- **Arg upper bound for Finset sums**. If every `f i` is in the upper half-plane union,
then `arg(∑ i ∈ s, f i) ≤ s.sup' hs (arg ∘ f)`. This extends `arg_add_le_max` from two
summands to finitely many by induction. -/
theorem arg_sum_le_sup'_of_upperHalfPlane {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion) :
    arg (∑ i ∈ s, f i) ≤ s.sup' hs (arg ∘ f) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hjs hs ih =>
    rw [Finset.sum_cons]
    have hfj : f j ∈ upperHalfPlaneUnion := hf j (Finset.mem_cons_self j s)
    have hfs : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion :=
      fun i hi ↦ hf i (Finset.mem_cons.mpr (Or.inr hi))
    calc arg (f j + ∑ i ∈ s, f i)
        ≤ max (arg (f j)) (arg (∑ i ∈ s, f i)) :=
          arg_add_le_max hfj (sum_mem_upperHalfPlane hs hfs)
      _ ≤ max (arg (f j)) (s.sup' hs (arg ∘ f)) :=
          max_le_max_left _ (ih hfs)
      _ = max ((arg ∘ f) j) (s.sup' hs (arg ∘ f)) := rfl
      _ ≤ (Finset.cons j s hjs).sup' ⟨j, Finset.mem_cons_self j s⟩ (arg ∘ f) := by
          rw [Finset.sup'_cons hs]

/-- **Arg lower bound for Finset sums**. If every `f i` is in the upper half-plane union,
then `s.inf' hs (arg ∘ f) ≤ arg(∑ i ∈ s, f i)`. Dual of `arg_sum_le_sup'_of_upperHalfPlane`. -/
theorem inf'_le_arg_sum_of_upperHalfPlane {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion) :
    s.inf' hs (arg ∘ f) ≤ arg (∑ i ∈ s, f i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hjs hs ih =>
    rw [Finset.sum_cons]
    have hfj : f j ∈ upperHalfPlaneUnion := hf j (Finset.mem_cons_self j s)
    have hfs : ∀ i ∈ s, f i ∈ upperHalfPlaneUnion :=
      fun i hi ↦ hf i (Finset.mem_cons.mpr (Or.inr hi))
    calc (Finset.cons j s hjs).inf' ⟨j, Finset.mem_cons_self j s⟩ (arg ∘ f)
        = min ((arg ∘ f) j) (s.inf' hs (arg ∘ f)) := by
          rw [Finset.inf'_cons hs]
      _ = min (arg (f j)) (s.inf' hs (arg ∘ f)) := rfl
      _ ≤ min (arg (f j)) (arg (∑ i ∈ s, f i)) :=
          min_le_min_left _ (ih hfs)
      _ ≤ arg (f j + ∑ i ∈ s, f i) :=
          min_arg_le_arg_add hfj (sum_mem_upperHalfPlane hs hfs)

end ArgConvexity

/-! ### Phase perturbation bound -/

/-- **Coarse phase perturbation bound**. If `E` is σ-semistable of phase `φ ∈ (α-1, α+1]`,
then `wPhaseOf(Z(E), α) = φ`. This is the inverse direction of `wPhaseOf_of_exp`. -/
theorem wPhaseOf_Z_eq (σ : StabilityCondition C) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) {α : ℝ}
    (hφ : φ ∈ Set.Ioc (α - 1) (α + 1)) :
    wPhaseOf (σ.Z (K₀.of C E)) α = φ := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  rw [hmZ]; exact wPhaseOf_of_exp hm hφ

/-- **Phase perturbation for σ-semistable objects**. If `E` is σ-semistable of phase `φ`
with `φ ∈ (α - 1/2, α + 1/2)`, and `‖(W-Z)(E)‖ / ‖Z(E)‖ < sin(πε)` with `0 < ε ≤ 1/2`,
then `|wPhaseOf(W(E), α) - φ| < ε`. This is the key quantitative bound for the
deformation theorem. -/
theorem wPhaseOf_perturbation (σ : StabilityCondition C)
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {α ε : ℝ}
    (hφα : φ ∈ Set.Ioo (α - 1 / 2) (α + 1 / 2))
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hbd : ‖(W - σ.Z) (K₀.of C E)‖ <
      Real.sin (Real.pi * ε) * ‖σ.Z (K₀.of C E)‖) :
    |wPhaseOf (W (K₀.of C E)) α - φ| < ε := by
  -- Z(E) = m · exp(iπφ) with m > 0
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  -- Set u = (W-Z)(E) / Z(E)
  set δ := (W - σ.Z) (K₀.of C E)
  have hWZ : δ = W (K₀.of C E) - σ.Z (K₀.of C E) := AddMonoidHom.sub_apply W σ.Z _
  have hZ_norm : ‖σ.Z (K₀.of C E)‖ = m := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hm_pos : (0 : ℝ) < m := hm
  -- W(E) = Z(E) + δ = m · exp(iπφ) · (1 + δ/(m · exp(iπφ)))
  set u := δ / (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I))
  have hZ_ne : (↑m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)
  have hW_eq : W (K₀.of C E) =
      ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I) * ((1 : ℂ) + u) := by
    rw [show u = δ / (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)) from rfl]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hZ_ne]
    rw [hWZ, ← hmZ]; ring
  -- ‖u‖ < sin(πε)
  have hu : ‖u‖ < Real.sin (Real.pi * ε) := by
    rw [show u = δ / (↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)) from rfl,
      norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      Complex.norm_exp_ofReal_mul_I, mul_one, div_lt_iff₀ hm]
    rwa [hZ_norm] at hbd
  rw [hW_eq]
  exact wPhaseOf_perturbation_generic hm hφα hε hε2 hu

/-- **Phase perturbation from stabSeminorm.** If `‖W - Z‖_σ < sin(πε₀)` and `b - a < 1`,
then for every nonzero `σ`-semistable object `F` with phase `φ ∈ (a, b)`, the W-phase
lies within `ε₀` of `φ`. This bridges the global stabSeminorm bound to the pointwise
hperturb condition needed by phase confinement. -/
theorem hperturb_of_stabSeminorm (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b : ℝ} (hthin : b - a < 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F → a < φ → φ < b →
      φ - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
      wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < φ + ε₀ := by
  intro F φ hP hFne haφ hφb
  have hfin : stabSeminorm C σ (W - σ.Z) ≠ ⊤ := ne_top_of_lt hW
  set M := (stabSeminorm C σ (W - σ.Z)).toReal
  -- M < sin(πε₀)
  have hM_sin : M < Real.sin (Real.pi * ε₀) := by
    have hsin_pos : 0 < Real.sin (Real.pi * ε₀) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · exact mul_pos Real.pi_pos hε₀
      · calc Real.pi * ε₀ ≤ Real.pi * (1 / 2) := by nlinarith [Real.pi_pos]
          _ = Real.pi / 2 := by ring
          _ < Real.pi := by linarith [Real.pi_pos]
    rw [show (Real.sin (Real.pi * ε₀) : ℝ) =
      (ENNReal.ofReal (Real.sin (Real.pi * ε₀))).toReal from
      (ENNReal.toReal_ofReal (le_of_lt hsin_pos)).symm]
    exact (ENNReal.toReal_lt_toReal hfin
      (ENNReal.ofReal_ne_top)).mpr hsin
  -- ‖(W-Z)(F)‖ ≤ M * ‖Z(F)‖
  have hbd := stabSeminorm_bound_real C σ (W - σ.Z) hfin hP hFne
  -- Z(F) ≠ 0 (from compatibility)
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ F hP hFne
  have hZ_pos : (0 : ℝ) < ‖σ.Z (K₀.of C F)‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      Complex.norm_exp_ofReal_mul_I, mul_one]; exact hm
  -- ‖(W-Z)(F)‖ < sin(πε₀) * ‖Z(F)‖
  have hbd_strict : ‖(W - σ.Z) (K₀.of C F)‖ <
      Real.sin (Real.pi * ε₀) * ‖σ.Z (K₀.of C F)‖ :=
    lt_of_le_of_lt hbd (by nlinarith)
  -- φ ∈ ((a+b)/2 - 1/2, (a+b)/2 + 1/2) since b - a < 1
  have hφα : φ ∈ Set.Ioo ((a + b) / 2 - 1 / 2) ((a + b) / 2 + 1 / 2) :=
    ⟨by linarith, by linarith⟩
  -- Apply wPhaseOf_perturbation
  have h := wPhaseOf_perturbation C σ hP hFne W hφα hε₀
    (hε₀2.le.trans (by norm_num)) hbd_strict
  exact ⟨by linarith [abs_lt.mp h], by linarith [abs_lt.mp h]⟩

/-! ### Upper half-plane membership from positive argument -/

/-- A nonzero complex number with positive argument lies in the upper half-plane union. -/
lemma mem_upperHalfPlaneUnion_of_arg_pos {z : ℂ}
    (h : 0 < Complex.arg z) : z ∈ upperHalfPlaneUnion := by
  by_cases him : 0 < z.im
  · exact Or.inl him
  · right
    push_neg at him
    have him' : z.im = 0 := le_antisymm him (Complex.arg_nonneg_iff.mp h.le)
    exact ⟨him', by
      by_contra hre
      push_neg at hre
      have : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hre, him'⟩
      linarith⟩

/-! ### W-phase bounds for sums (Node 7.3 infrastructure) -/

/-- **wPhaseOf characterizes UHP membership.** `wPhaseOf(w, ψ) > ψ` if and only if
`w · exp(-iπψ)` lies in the upper half-plane union (i.e., has positive argument).
This is the forward direction: UHP membership implies wPhaseOf > ψ. -/
theorem wPhaseOf_gt_of_mem_upperHalfPlaneUnion {w : ℂ} {ψ : ℝ}
    (h : w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) ∈
      CategoryTheory.upperHalfPlaneUnion) :
    ψ < wPhaseOf w ψ := by
  have harg := CategoryTheory.arg_pos_of_mem_upperHalfPlaneUnion h
  unfold wPhaseOf
  linarith [div_pos harg Real.pi_pos]

/-- **UHP membership from wPhaseOf bound.** If `ψ < wPhaseOf(w, ψ)`, then
`w · exp(-iπψ)` lies in the upper half-plane union. -/
theorem mem_upperHalfPlaneUnion_of_wPhaseOf_gt {w : ℂ} {ψ : ℝ}
    (h : ψ < wPhaseOf w ψ) :
    w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) ∈
      CategoryTheory.upperHalfPlaneUnion := by
  apply mem_upperHalfPlaneUnion_of_arg_pos
  unfold wPhaseOf at h
  have hπ := Real.pi_pos
  have : 0 < Complex.arg (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))) /
    Real.pi := by linarith
  exact (div_pos_iff.mp this).elim (fun h ↦ h.1)
    (fun h ↦ absurd h.2 (not_lt.mpr hπ.le))

/-- **W-phase lower bound for sums**. If complex numbers `w₁, ..., wₙ` all have
`wPhaseOf(wⱼ, ψ) > ψ` (i.e., are "above" ψ in phase), then their sum satisfies
`wPhaseOf(Σ wⱼ, ψ) > ψ`. The sum is automatically nonzero since UHP is closed under
addition.

The proof rotates by `exp(-iπψ)`, observes all vectors lie in the upper half-plane (since
wPhaseOf > ψ), uses closure of UHP under sums, and converts back. -/
theorem wPhaseOf_sum_gt {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℂ} {ψ : ℝ}
    (hf_phase : ∀ i ∈ s, ψ < wPhaseOf (f i) ψ) :
    ψ < wPhaseOf (∑ i ∈ s, f i) ψ := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  -- Each f(i) * rot is in UHP
  have huhp : ∀ i ∈ s, f i * rot ∈ CategoryTheory.upperHalfPlaneUnion :=
    fun i hi ↦ mem_upperHalfPlaneUnion_of_wPhaseOf_gt (hf_phase i hi)
  -- Sum is in UHP
  have hsum_uhp : (∑ i ∈ s, f i) * rot ∈ CategoryTheory.upperHalfPlaneUnion := by
    rw [Finset.sum_mul]
    exact sum_mem_upperHalfPlane hs huhp
  exact wPhaseOf_gt_of_mem_upperHalfPlaneUnion hsum_uhp

/-- **Imaginary part bound for phases above ψ**. If `w = m · exp(iπφ)` with `m > 0` and
`φ ∈ (ψ, ψ + 1)`, then `Im(w · exp(-iπψ)) > 0`. -/
theorem im_pos_of_phase_above {w : ℂ} {m φ ψ : ℝ} (hm : 0 < m)
    (hw : w = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I))
    (hlo : ψ < φ) (hhi : φ < ψ + 1) :
    0 < (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  rw [hw, mul_assoc, ← Complex.exp_add]
  have harg : ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (φ - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero]
  exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

/-- **Imaginary part positivity for sums of phase-above vectors.** If complex numbers
`w₁, ..., wₙ` all satisfy `Im(wⱼ · exp(-iπψ)) > 0`, then so does their sum. This is
immediate from additivity of Im. -/
theorem im_sum_pos_of_all_pos {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℂ} {ψ : ℝ}
    (hf : ∀ i ∈ s, 0 < (f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im) :
    0 < (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  rw [show (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im =
      ∑ i ∈ s, (f i *
        Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im from
    map_sum Complex.imAddGroupHom _ _]
  exact Finset.sum_pos hf hs

/-- **wPhaseOf bound from imaginary part.** If `Im(w · exp(-iπψ)) > 0` and
`wPhaseOf(w, α) ∈ (ψ - 1, ψ + 1)` (which rules out the wrapping branch), then
`wPhaseOf(w, α) > ψ`. -/
theorem wPhaseOf_gt_of_im_pos {w : ℂ} {α ψ : ℝ}
    (him : 0 < (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im)
    (hrange : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < wPhaseOf w α := by
  -- w = ‖w‖ · exp(iπ · wPhaseOf(w, α)), so
  -- w · exp(-iπψ) = ‖w‖ · exp(iπ(wPhaseOf(w, α) - ψ))
  -- Im = ‖w‖ · sin(π(wPhaseOf(w, α) - ψ))
  -- If sin > 0, then π(wPhaseOf(w, α) - ψ) ∈ (0, π) ∪ (-2π, -π), i.e.,
  -- wPhaseOf - ψ ∈ (0, 1) ∪ (-2, -1). The range condition rules out (-2, -1).
  by_contra h
  push_neg at h -- h : wPhaseOf w α ≤ ψ
  -- wPhaseOf(w, α) ∈ (ψ - 1, ψ], so wPhaseOf - ψ ∈ (-1, 0]
  -- sin(π(wPhaseOf - ψ)) ≤ 0 on (-1, 0] (since π · (-1, 0] = (-π, 0])
  have hd : wPhaseOf w α - ψ ∈ Set.Ioc (-1) 0 :=
    ⟨by linarith [hrange.1], by linarith⟩
  have hsin : Real.sin (Real.pi * (wPhaseOf w α - ψ)) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos, hd.2])
      (by nlinarith [Real.pi_pos, hd.1])
  -- But Im = ‖w‖ · sin(...) > 0 and ‖w‖ ≥ 0, so sin > 0. Contradiction.
  have hw := wPhaseOf_compat w α
  rw [hw] at him
  rw [mul_assoc, ← Complex.exp_add] at him
  have harg : ↑(Real.pi * wPhaseOf w α) * Complex.I +
      -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (wPhaseOf w α - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w) hsin]

/-! ### Dual im/wPhaseOf infrastructure (for lower bound arguments) -/

/-- **Imaginary part negativity for below-phase vectors.** If `w = m · exp(iπφ)` with `m > 0`
and `φ ∈ (ψ - 1, ψ)`, then `Im(w · exp(-iπψ)) < 0`. Dual of `im_pos_of_phase_above`. -/
theorem im_neg_of_phase_below {w : ℂ} {m φ ψ : ℝ} (hm : 0 < m)
    (hw : w = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I))
    (hlo : ψ - 1 < φ) (hhi : φ < ψ) :
    (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0 := by
  rw [hw, mul_assoc, ← Complex.exp_add]
  have harg : ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (φ - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero]
  exact mul_neg_of_pos_of_neg hm (Real.sin_neg_of_neg_of_neg_pi_lt
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

/-- **Imaginary part negativity for sums of phase-below vectors.** If complex numbers
`w₁, ..., wₙ` all satisfy `Im(wⱼ · exp(-iπψ)) < 0`, then so does their sum.
Dual of `im_sum_pos_of_all_pos`. -/
theorem im_sum_neg_of_all_neg {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℂ} {ψ : ℝ}
    (hf : ∀ i ∈ s, (f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0) :
    (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0 := by
  rw [show (∑ i ∈ s, f i *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im =
      ∑ i ∈ s, (f i *
        Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im from
    map_sum Complex.imAddGroupHom _ _]
  exact Finset.sum_neg hf hs

/-- **wPhaseOf bound from negative imaginary part.** If `Im(w · exp(-iπψ)) < 0` and
`wPhaseOf(w, α) ∈ (ψ - 1, ψ + 1)`, then `wPhaseOf(w, α) < ψ`.
Dual of `wPhaseOf_gt_of_im_pos`. -/
theorem wPhaseOf_lt_of_im_neg {w : ℂ} {α ψ : ℝ}
    (him : (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0)
    (hrange : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w α < ψ := by
  by_contra h
  push_neg at h -- h : ψ ≤ wPhaseOf w α
  -- wPhaseOf(w, α) ∈ [ψ, ψ + 1), so wPhaseOf - ψ ∈ [0, 1)
  -- sin(π(wPhaseOf - ψ)) ≥ 0 on [0, 1) (since π · [0, 1) = [0, π))
  have hd : wPhaseOf w α - ψ ∈ Set.Ico 0 1 :=
    ⟨by linarith, by linarith [hrange.2]⟩
  have hsin : 0 ≤ Real.sin (Real.pi * (wPhaseOf w α - ψ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos, hd.1])
      (by nlinarith [Real.pi_pos, hd.2])
  -- But Im = ‖w‖ · sin(...) < 0 and ‖w‖ ≥ 0, so sin < 0. Contradiction.
  have hw := wPhaseOf_compat w α
  rw [hw] at him
  rw [mul_assoc, ← Complex.exp_add] at him
  have harg : ↑(Real.pi * wPhaseOf w α) * Complex.I +
      -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (wPhaseOf w α - ψ)) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him
  linarith [mul_nonneg (norm_nonneg w) hsin]

/-- **Imaginary part vanishes at exact phase.** If `wPhaseOf(w, α) = ψ`, then
`Im(w · exp(-iπψ)) = 0` (and in fact `w · exp(-iπψ) = ‖w‖`). -/
theorem im_eq_zero_of_wPhaseOf_eq {w : ℂ} {α ψ : ℝ}
    (h : wPhaseOf w α = ψ) :
    (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im = 0 := by
  have hw := wPhaseOf_compat w α
  rw [hw, h, mul_assoc, ← Complex.exp_add]
  have harg : ↑(Real.pi * ψ) * Complex.I +
      -(↑(Real.pi * ψ) * Complex.I) = 0 := by ring
  rw [harg, Complex.exp_zero, mul_one, Complex.ofReal_im]

/-- **Imaginary part sign decomposition.** If `w₁ + w₂ = w` and
`Im(w · exp(-iπψ)) = 0` and `Im(w₂ · exp(-iπψ)) < 0`, then
`Im(w₁ · exp(-iπψ)) > 0`. -/
theorem im_pos_of_sum_zero_and_neg {w₁ w₂ w : ℂ} {ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hw : (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im = 0)
    (h₂ : (w₂ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0) :
    0 < (w₁ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  have : (w₁ + w₂) * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) =
      w₁ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) +
      w₂ * Complex.exp (-(↑(Real.pi * ψ) * Complex.I)) := add_mul _ _ _
  rw [hsum] at this
  have him := congr_arg Complex.im this
  simp only [Complex.add_im] at him
  linarith

/-! ### Phase see-saw lemma -/

/-- **Phase see-saw**: if `w = w₁ + w₂` with `wPhaseOf(w, α) = ψ`,
`wPhaseOf(w₁, α) ∈ (ψ - 1, ψ]` (i.e., w₁ has phase ≤ ψ in the correct range),
and `w₂ ≠ 0` with `wPhaseOf(w₂, α) ∈ (ψ - 1, ψ + 1)`, then `wPhaseOf(w₂, α) ≥ ψ`.

The proof uses the imaginary-part sign argument: `Im(w · rot) = 0` (from phase = ψ),
`Im(w₁ · rot) ≤ 0` (from phase ≤ ψ in (-1, 0] range), and if `Im(w₂ · rot) < 0`
(from phase < ψ), then `Im(w · rot) < 0`, contradiction. -/
theorem wPhaseOf_seesaw {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : wPhaseOf w α = ψ)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioc (ψ - 1) ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ ≤ wPhaseOf w₂ α := by
  by_contra h
  push_neg at h
  -- w₂ has phase < ψ in (ψ-1, ψ), so Im(w₂ · rot) < 0
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  -- Im(w₁ · rot) ≤ 0
  have him_w₁ : (w₁ * rot).im ≤ 0 := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w₁)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw₁_range.2])
        (by nlinarith [Real.pi_pos, hw₁_range.1]))
  -- Im(w₂ · rot) < 0
  have him_w₂ : (w₂ * rot).im < 0 := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  -- Contradiction: Im(w · rot) = Im(w₁ · rot) + Im(w₂ · rot) < 0
  have hsum_im : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
    rw [← hsum, add_mul, Complex.add_im]
  linarith

/-- **Strict phase see-saw**: if `w = w₁ + w₂` with `wPhaseOf(w, α) = ψ`,
`wPhaseOf(w₂, α) < ψ` with `wPhaseOf(w₂, α) ∈ (ψ - 1, ψ + 1)`, `w₂ ≠ 0`,
and `wPhaseOf(w₁, α) ∈ (ψ - 1, ψ + 1)`, then `wPhaseOf(w₁, α) > ψ`.

This is the dual of `wPhaseOf_seesaw` with roles swapped. -/
theorem wPhaseOf_seesaw_strict {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : wPhaseOf w α = ψ)
    (hw₂_lt : wPhaseOf w₂ α < ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < wPhaseOf w₁ α := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  -- Im(w₂ · rot) < 0
  have him_w₂ : (w₂ * rot).im < 0 := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hw₂_lt])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  -- Im(w₁ · rot) > 0
  have him_w₁ : 0 < (w₁ * rot).im := by
    have hsum_im : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
      rw [← hsum, add_mul, Complex.add_im]
    linarith
  -- Conclude phase(w₁) > ψ
  exact wPhaseOf_gt_of_im_pos him_w₁ hw₁_range

/-! ### K₀ decomposition of imaginary parts -/

/-- **Im positivity from HN factors.** If `E ∈ P((a, b))` is nonzero and every nonzero
σ-semistable factor of an HN filtration has `Im(W(Fⱼ) · exp(-iπψ)) ≥ 0`, with at least
one factor giving strict positivity, then `Im(W(E) · exp(-iπψ)) > 0`.

The proof decomposes `W([E]) = ∑ W([Fⱼ])` via K₀ additivity and extracts Im through
the sum using the additivity of the imaginary part. -/
theorem im_W_pos_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {ψ : ℝ}
    {a b : ℝ} (hI : σ.slicing.intervalProp C a b E)
    (him_pos : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        0 < (W (K₀.of C F) *
          Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im) :
    0 < (W (K₀.of C E) *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
  -- Get HN filtration with nonzero first and last factors
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  -- All phases in (a, b) — use uniqueness to relate to intrinsic phases
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := by
    intro i
    exact ⟨by calc a < σ.slicing.phiMinus C E hE :=
              σ.slicing.phiMinus_gt_of_intervalProp C hE hI
            _ = F.φ ⟨F.n - 1, by omega⟩ :=
              σ.slicing.phiMinus_eq C E hE F hn hlast
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i
            ≤ F.φ ⟨0, hn⟩ :=
              F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C E hE :=
              (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
            _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI⟩
  -- K₀ decomposition: W(E) = Σ W(Fⱼ)
  set P := F.toPostnikovTower
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  -- Im(W(E) · rot) = Σ Im(W(Fⱼ) · rot)
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  rw [hWE, Finset.sum_mul]
  rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
      ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  -- Each term ≥ 0, first term > 0
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)
    (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
  · -- First factor contributes Im > 0
    exact him_pos _ _ (F.semistable ⟨0, hn⟩) hfirst
      (hphases ⟨0, hn⟩).1 (hphases ⟨0, hn⟩).2
  · -- Each factor contributes Im ≥ 0
    by_cases hi : IsZero (P.factor i)
    · simp [K₀.of_isZero C hi]
    · exact le_of_lt (him_pos _ _ (F.semistable i) hi
        (hphases i).1 (hphases i).2)

/-- **Dual: Im negativity from HN factors.** If `E ∈ P((a, b))` is nonzero and every
nonzero σ-semistable factor has `Im(W(Fⱼ) · exp(-iπψ)) ≤ 0`, with at least one giving
strict negativity, then `Im(W(E) · exp(-iπψ)) < 0`. -/
theorem im_W_neg_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {ψ : ℝ}
    {a b : ℝ} (hI : σ.slicing.intervalProp C a b E)
    (him_neg : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        (W (K₀.of C F) *
          Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0) :
    (W (K₀.of C E) *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im < 0 := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b := by
    intro i
    exact ⟨by calc a < σ.slicing.phiMinus C E hE :=
              σ.slicing.phiMinus_gt_of_intervalProp C hE hI
            _ = F.φ ⟨F.n - 1, by omega⟩ :=
              σ.slicing.phiMinus_eq C E hE F hn hlast
            _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i
            ≤ F.φ ⟨0, hn⟩ :=
              F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C E hE :=
              (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
            _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI⟩
  set P := F.toPostnikovTower
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  rw [hWE, Finset.sum_mul]
  rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
      ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  -- Negate: show Σ (-Im) > 0, then Σ Im < 0
  suffices h : 0 < ∑ i : Fin F.n,
      -(W (K₀.of C (P.factor i)) * rot).im by
    linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
      (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)]
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (f := fun i ↦ -(W (K₀.of C (P.factor i)) * rot).im)
    (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
  · -- First factor: -Im > 0
    exact neg_pos.mpr (him_neg _ _ (F.semistable ⟨0, hn⟩) hfirst
      (hphases ⟨0, hn⟩).1 (hphases ⟨0, hn⟩).2)
  · -- Each factor: -Im ≥ 0
    by_cases hi : IsZero (P.factor i)
    · simp [K₀.of_isZero C hi]
    · exact le_of_lt (neg_pos.mpr (him_neg _ _ (F.semistable i) hi
        (hphases i).1 (hphases i).2))

/-! ### W-phase range for interval objects (Lemma 7.3(b)) -/

/-- **W-phase lower bound for interval objects.** If `E ∈ P((a, b))` is nonzero, and
every nonzero σ-semistable object of phase `φ ∈ (a, b)` has
`W`-phase in `(a - ε, a - ε + 1)` (so `Im(W(F) · exp(-iπ(a-ε))) > 0`), then
`wPhaseOf(W(E), α) > a - ε`.

This is part (b) of **Bridgeland's Lemma 7.3** (lower bound). The proof uses the
K₀ decomposition to show `Im(W(E) · exp(-iπ(a-ε))) > 0`, then converts to a phase
bound via the sin/Im relationship. -/
theorem wPhaseOf_gt_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {α : ℝ}
    {a b ε : ℝ}
    (hα_ge : a - ε ≤ α)
    (hI : σ.slicing.intervalProp C a b E)
    (hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b → W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        a - ε < wPhaseOf (W (K₀.of C F)) α ∧
        wPhaseOf (W (K₀.of C F)) α < a - ε + 1) :
    a - ε < wPhaseOf (W (K₀.of C E)) α := by
  -- Each nonzero factor has Im > 0 after rotation by a - ε
  have him : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      0 < (W (K₀.of C F) *
        Complex.exp (-(↑(Real.pi * (a - ε)) * Complex.I))).im := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    have hWne := hW_ne F φ hP hFne haφ hφb
    -- W(F) = ‖W(F)‖ · exp(iπ · wPhaseOf(W(F), α))
    set θ := wPhaseOf (W (K₀.of C F)) α
    have hm : (0 : ℝ) < ‖W (K₀.of C F)‖ := norm_pos_iff.mpr hWne
    exact im_pos_of_phase_above hm (wPhaseOf_compat _ _) hlo hhi
  -- By K₀ decomposition: Im(W(E) · rot) > 0
  have him_pos := im_W_pos_of_intervalProp C σ hE W hI him
  -- Convert Im > 0 to phase bound
  -- W(E) = ‖W(E)‖ · exp(iπψ), so W(E)·rot = ‖W(E)‖ · exp(iπ(ψ - (a-ε)))
  -- Im > 0 means sin(π(ψ - (a-ε))) > 0
  -- If ψ ≤ a - ε, then ψ - (a-ε) ≤ 0, and we need to check sin ≤ 0
  by_contra h
  push_neg at h -- h : wPhaseOf(W(E), α) ≤ a - ε
  set ψ := wPhaseOf (W (K₀.of C E)) α
  have hw := wPhaseOf_compat (W (K₀.of C E)) α
  rw [hw] at him_pos
  rw [mul_assoc, ← Complex.exp_add] at him_pos
  have harg : ↑(Real.pi * ψ) * Complex.I +
      -(↑(Real.pi * (a - ε)) * Complex.I) =
      ↑(Real.pi * (ψ - (a - ε))) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him_pos
  -- ψ - (a - ε) ∈ (-1, 0] (from ψ > α - 1 and ψ ≤ a - ε)
  have hψ_range := wPhaseOf_mem_Ioc (W (K₀.of C E)) α
  have hψ_lo : α - 1 < ψ := hψ_range.1
  -- sin(π(ψ - (a-ε))) ≤ 0 on (-1, 0] (since π(-1, 0] = (-π, 0])
  have hsin : Real.sin (Real.pi * (ψ - (a - ε))) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hψ_lo])
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (W (K₀.of C E))) hsin]

/-- **W-phase upper bound for interval objects.** If `E ∈ P((a, b))` is nonzero, and
every nonzero σ-semistable object of phase `φ ∈ (a, b)` has W-phase in
`(b + ε - 1, b + ε)` (so `Im(W(F) · exp(-iπ(b+ε))) < 0`), then
`wPhaseOf(W(E), α) < b + ε`. -/
theorem wPhaseOf_lt_of_intervalProp
    (σ : StabilityCondition C)
    {E : C} (hE : ¬IsZero E)
    (W : K₀ C →+ ℂ) {α : ℝ}
    {a b ε : ℝ}
    (hα_le : α ≤ b + ε)
    (hI : σ.slicing.intervalProp C a b E)
    (hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b → W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        b + ε - 1 < wPhaseOf (W (K₀.of C F)) α ∧
        wPhaseOf (W (K₀.of C F)) α < b + ε) :
    wPhaseOf (W (K₀.of C E)) α < b + ε := by
  -- Each nonzero factor has Im < 0 after rotation by b + ε
  have him : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      (W (K₀.of C F) *
        Complex.exp (-(↑(Real.pi * (b + ε)) * Complex.I))).im < 0 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    have hWne := hW_ne F φ hP hFne haφ hφb
    set θ := wPhaseOf (W (K₀.of C F)) α
    have hm : (0 : ℝ) < ‖W (K₀.of C F)‖ := norm_pos_iff.mpr hWne
    exact im_neg_of_phase_below hm (wPhaseOf_compat _ _) hlo hhi
  have him_neg := im_W_neg_of_intervalProp C σ hE W hI him
  by_contra h
  push_neg at h -- h : b + ε ≤ wPhaseOf(W(E), α)
  set ψ := wPhaseOf (W (K₀.of C E)) α
  have hw := wPhaseOf_compat (W (K₀.of C E)) α
  rw [hw] at him_neg
  rw [mul_assoc, ← Complex.exp_add] at him_neg
  have harg : ↑(Real.pi * ψ) * Complex.I +
      -(↑(Real.pi * (b + ε)) * Complex.I) =
      ↑(Real.pi * (ψ - (b + ε))) * Complex.I := by push_cast; ring
  rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero] at him_neg
  -- ψ - (b + ε) ∈ [0, 1) (from ψ ≥ b + ε and ψ ≤ α + 1)
  have hψ_range := wPhaseOf_mem_Ioc (W (K₀.of C E)) α
  have hψ_hi : ψ ≤ α + 1 := hψ_range.2
  have hsin : 0 ≤ Real.sin (Real.pi * (ψ - (b + ε))) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hψ_hi])
  linarith [mul_nonneg (norm_nonneg (W (K₀.of C E))) hsin]

/-! ### Node 7.3: Phase confinement of W-semistable objects -/

variable [IsTriangulated C] in
/-- **Bridgeland's Lemma 7.3 (upper bound).** If `E` is W-semistable of W-phase `ψ` in
`P((a, b))`, the interval is thin enough (`b - a + 2ε₀ < 1`), and each nonzero semistable
factor has W-phase within `ε₀` of its σ-phase, then `σ.phiPlus(E) ≤ ψ + ε₀`.

The proof splits `E` at the cutoff `ψ + ε₀` via the t-structure. The resulting subobject
`K` (with σ-phases above `ψ + ε₀`) has W-phase `> ψ` by the Im/sin argument, contradicting
W-semistability. -/
theorem phiPlus_le_of_wSemistable
    (σ : StabilityCondition C) {E : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ : ℝ} (hSS : ssf.Semistable C E ψ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀) :
    σ.slicing.phiPlus C E hSS.2.1 ≤ ψ + ε₀ := by
  obtain ⟨hI, hE, _, hψ, hsemistable⟩ := hSS
  -- W nonvanishing and reformulated perturbation bounds
  have hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → ssf.W (K₀.of C F) ≠ 0 :=
    fun F φ hP hFne haφ hφb ↦ ssf.nonzero F φ haφ hφb hP hFne
  have hperturb_gt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      a - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hperturb_lt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      b + ε₀ - 1 < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  -- ψ bounds from wPhaseOf_gt/lt_of_intervalProp applied to E
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hψ]; exact wPhaseOf_gt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hI hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hψ]; exact wPhaseOf_lt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hI hW_ne hperturb_lt
  -- Proof by contradiction
  by_contra hgt; push_neg at hgt
  have hψε_lt_b : ψ + ε₀ < b :=
    lt_trans hgt (σ.slicing.phiPlus_lt_of_intervalProp C hE hI)
  -- Extract HN filtration from intervalProp
  obtain ⟨F, hF⟩ := hI.resolve_left hE
  have hn : 0 < F.n := F.n_pos C hE
  -- Split E at cutoff ψ + ε₀
  obtain ⟨K, Y, fK, gY, δ, hT, hKgt, hYle, hKphiPlus⟩ :=
    σ.slicing.exists_split_at_cutoff C F hF hn (t := ψ + ε₀)
  -- K is nonzero (otherwise E ∈ leProp(ψ + ε₀), contradicting phiPlus > ψ + ε₀)
  have hKne : ¬IsZero K := by
    intro hKZ
    linarith [σ.slicing.phiPlus_le_of_leProp C hE
      (σ.slicing.leProp_of_triangle C (ψ + ε₀) (Or.inl hKZ) hYle hT)]
  -- K ∈ P((a, b))
  have hKI : σ.slicing.intervalProp C a b K :=
    σ.slicing.intervalProp_of_intrinsic_phases C hKne
      (by linarith [σ.slicing.phiMinus_gt_of_gtProp C hKne hKgt])
      (hKphiPlus hKne)
  -- K ∈ P((ψ + ε₀, b)) (narrower interval for Im argument)
  have hKI' : σ.slicing.intervalProp C (ψ + ε₀) b K :=
    σ.slicing.intervalProp_of_intrinsic_phases C hKne
      (σ.slicing.phiMinus_gt_of_gtProp C hKne hKgt) (hKphiPlus hKne)
  -- Im(W(K) · exp(-iπψ)) > 0 via K₀ decomposition
  have him_pos : 0 < (ssf.W (K₀.of C K) *
      Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im := by
    apply im_W_pos_of_intervalProp C σ hKne ssf.W hKI'
    intro G φ hP hGne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb G φ hP hGne (by linarith) hφb
    exact im_pos_of_phase_above (norm_pos_iff.mpr
      (ssf.nonzero G φ (by linarith) hφb hP hGne))
      (wPhaseOf_compat _ _) (by linarith) (by linarith)
  -- wPhaseOf(W(K), α) ∈ (ψ - 1, ψ + 1) via bounds on the original interval
  have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C K)) ssf.α :=
    wPhaseOf_gt_of_intervalProp C σ hKne ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hKI hW_ne hperturb_gt
  have hK_hi : wPhaseOf (ssf.W (K₀.of C K)) ssf.α < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hKne ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hKI hW_ne hperturb_lt
  -- Y ∈ P((a, b))
  have hYI : σ.slicing.intervalProp C a b Y := by
    by_cases hYZ : IsZero Y
    · exact Or.inl hYZ
    · exact σ.slicing.intervalProp_of_intrinsic_phases C hYZ
        (lt_of_lt_of_le (σ.slicing.phiMinus_gt_of_intervalProp C hE hI)
          (σ.slicing.phiMinus_triangle_le' C hYZ hE (by linarith) hKI
            (lt_of_le_of_lt (σ.slicing.phiPlus_le_of_leProp C hYZ hYle)
              (by linarith)) hT))
        (lt_of_le_of_lt (σ.slicing.phiPlus_le_of_leProp C hYZ hYle)
          (by linarith))
  -- wPhaseOf(W(K), α) > ψ (from Im > 0 + range condition)
  linarith [wPhaseOf_gt_of_im_pos him_pos
    (show wPhaseOf (ssf.W (K₀.of C K)) ssf.α ∈ Set.Ioo (ψ - 1) (ψ + 1) from
      ⟨by linarith, by linarith⟩),
    hsemistable hT hKI hYI hKne]

variable [IsTriangulated C] in
/-- **Bridgeland's Lemma 7.3 (lower bound).** If `E` is W-semistable of W-phase `ψ` in
`P((a, b))`, the interval is thin enough (`b - a + 2ε₀ < 1`), and each nonzero semistable
factor has W-phase within `ε₀` of its σ-phase, then `ψ - ε₀ ≤ σ.phiMinus(E)`.

The proof splits `E` at the cutoff `ψ - ε₀`. The resulting quotient `Y` (with σ-phases
`≤ ψ - ε₀`) has `Im(W(Y) · exp(-iπψ)) < 0` by the sin/Im argument applied to each HN
factor. Combined with `Im(W(E) · exp(-iπψ)) = 0` (from `wPhaseOf(W(E)) = ψ`), this
shows `Im(W(K) · exp(-iπψ)) > 0`, giving `wPhaseOf(W(K)) > ψ` and contradicting
W-semistability. -/
theorem phiMinus_ge_of_wSemistable
    (σ : StabilityCondition C) {E : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ : ℝ} (hSS : ssf.Semistable C E ψ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀) :
    ψ - ε₀ ≤ σ.slicing.phiMinus C E hSS.2.1 := by
  obtain ⟨hI, hE, _, hψ, hsemistable⟩ := hSS
  -- W nonvanishing and reformulated perturbation bounds
  have hW_ne : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b → ssf.W (K₀.of C F) ≠ 0 :=
    fun F φ hP hFne haφ hφb ↦ ssf.nonzero F φ haφ hφb hP hFne
  have hperturb_gt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      a - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hperturb_lt : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
      a < φ → φ < b →
      b + ε₀ - 1 < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
      wPhaseOf (ssf.W (K₀.of C F)) ssf.α < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hperturb F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  -- ψ bounds from wPhaseOf_gt/lt_of_intervalProp applied to E
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hψ]; exact wPhaseOf_gt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hI hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hψ]; exact wPhaseOf_lt_of_intervalProp C σ hE ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hI hW_ne hperturb_lt
  -- Proof by contradiction
  by_contra hlt; push_neg at hlt
  have hψε_gt_a : a < ψ - ε₀ :=
    lt_trans (σ.slicing.phiMinus_gt_of_intervalProp C hE hI) hlt
  -- Extract HN filtration from intervalProp
  obtain ⟨F, hF⟩ := hI.resolve_left hE
  have hn : 0 < F.n := F.n_pos C hE
  -- Split E at cutoff ψ - ε₀
  obtain ⟨K, Y, fK, gY, δ, hT, hKgt, hYle, hKphiPlus⟩ :=
    σ.slicing.exists_split_at_cutoff C F hF hn (t := ψ - ε₀)
  -- Y is nonzero (otherwise E ∈ gtProp(ψ - ε₀), contradicting phiMinus < ψ - ε₀)
  have hYne : ¬IsZero Y := by
    intro hYZ
    linarith [σ.slicing.phiMinus_gt_of_gtProp C hE
      (σ.slicing.gtProp_of_triangle C (ψ - ε₀) hKgt (Or.inl hYZ) hT)]
  -- K ∈ P((a, b))
  have hKI : σ.slicing.intervalProp C a b K := by
    by_cases hKZ : IsZero K
    · exact Or.inl hKZ
    · exact σ.slicing.intervalProp_of_intrinsic_phases C hKZ
        (by linarith [σ.slicing.phiMinus_gt_of_gtProp C hKZ hKgt])
        (hKphiPlus hKZ)
  -- Y ∈ P((a, b)) with phiPlus(Y) ≤ ψ - ε₀
  have hYphiPlus : σ.slicing.phiPlus C Y hYne ≤ ψ - ε₀ :=
    σ.slicing.phiPlus_le_of_leProp C hYne hYle
  have hYminus : a < σ.slicing.phiMinus C Y hYne :=
    lt_of_lt_of_le
      (σ.slicing.phiMinus_gt_of_intervalProp C hE (Or.inr ⟨F, hF⟩))
      (σ.slicing.phiMinus_triangle_le' C hYne hE
        (by linarith) hKI (by linarith [hYphiPlus]) hT)
  have hYI : σ.slicing.intervalProp C a b Y :=
    σ.slicing.intervalProp_of_intrinsic_phases C hYne hYminus
      (lt_of_le_of_lt hYphiPlus (by linarith))
  -- Im(W(Y) · exp(-iπψ)) < 0 via inline K₀ decomposition
  -- (Cannot use im_W_neg_of_intervalProp directly because the callback would need
  -- to handle arbitrary phases in (a, b), but we only know wPhaseOf < ψ for phases ≤ ψ-ε₀)
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_Y_neg : (ssf.W (K₀.of C Y) * rot).im < 0 := by
    obtain ⟨FY, hnY, hfirstY, hlastY⟩ :=
      HNFiltration.exists_both_nonzero C σ.slicing hYne
    -- All Y-phases are in (a, b) with φ ≤ ψ - ε₀
    have hphasesY : ∀ i : Fin FY.n,
        a < FY.φ i ∧ FY.φ i < b ∧ FY.φ i ≤ ψ - ε₀ := by
      intro i
      refine ⟨?_, ?_, ?_⟩
      · calc a < σ.slicing.phiMinus C Y hYne := hYminus
            _ = FY.φ ⟨FY.n - 1, by omega⟩ :=
              σ.slicing.phiMinus_eq C Y hYne FY hnY hlastY
            _ ≤ FY.φ i := FY.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
      · calc FY.φ i ≤ FY.φ ⟨0, hnY⟩ :=
              FY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C Y hYne :=
              (σ.slicing.phiPlus_eq C Y hYne FY hnY hfirstY).symm
            _ ≤ ψ - ε₀ := hYphiPlus
            _ < b := by linarith
      · calc FY.φ i ≤ FY.φ ⟨0, hnY⟩ :=
              FY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
            _ = σ.slicing.phiPlus C Y hYne :=
              (σ.slicing.phiPlus_eq C Y hYne FY hnY hfirstY).symm
            _ ≤ ψ - ε₀ := hYphiPlus
    -- Each nonzero factor has Im(W · rot) < 0 (wPhaseOf < ψ from φ + ε₀ ≤ ψ)
    have hfactor_neg : ∀ (i : Fin FY.n),
        ¬IsZero (FY.toPostnikovTower.factor i) →
        (ssf.W (K₀.of C (FY.toPostnikovTower.factor i)) * rot).im < 0 := by
      intro i hi
      obtain ⟨hlo_pert, hhi_pert⟩ := hperturb _ _ (FY.semistable i) hi
        (hphasesY i).1 (hphasesY i).2.1
      exact im_neg_of_phase_below
        (norm_pos_iff.mpr (ssf.nonzero _ _ (hphasesY i).1 (hphasesY i).2.1
          (FY.semistable i) hi))
        (wPhaseOf_compat _ _)
        (by linarith [(hphasesY i).1]) (by linarith [(hphasesY i).2.2])
    -- K₀ decomposition: W(Y) = Σ W(Fⱼ)
    set PY := FY.toPostnikovTower
    rw [show ssf.W (K₀.of C Y) = ∑ i : Fin FY.n,
        ssf.W (K₀.of C (PY.factor i)) from by
      rw [K₀.of_postnikovTower_eq_sum C PY, map_sum],
      Finset.sum_mul, show (∑ i : Fin FY.n,
        ssf.W (K₀.of C (PY.factor i)) * rot).im =
        ∑ i : Fin FY.n, (ssf.W (K₀.of C (PY.factor i)) * rot).im from
      map_sum Complex.imAddGroupHom _ _]
    -- Negate: Σ (-Im) > 0 ⟹ Σ Im < 0
    suffices h : 0 < ∑ i : Fin FY.n,
        -(ssf.W (K₀.of C (PY.factor i)) * rot).im by
      linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
        (f := fun i ↦ (ssf.W (K₀.of C (PY.factor i)) * rot).im)]
    apply lt_of_lt_of_le _ (Finset.single_le_sum
      (f := fun i ↦ -(ssf.W (K₀.of C (PY.factor i)) * rot).im)
      (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hnY⟩))
    · exact neg_pos.mpr (hfactor_neg ⟨0, hnY⟩ hfirstY)
    · by_cases hi : IsZero (PY.factor i)
      · simp [K₀.of_isZero C hi]
      · exact le_of_lt (neg_pos.mpr (hfactor_neg i hi))
  -- Im(W(E) · exp(-iπψ)) = 0 (since wPhaseOf(W(E)) = ψ)
  have him_E_zero : (ssf.W (K₀.of C E) * rot).im = 0 :=
    im_eq_zero_of_wPhaseOf_eq hψ
  -- K₀ additivity: W(K) + W(Y) = W(E)
  have hK₀ : ssf.W (K₀.of C K) + ssf.W (K₀.of C Y) = ssf.W (K₀.of C E) := by
    rw [← map_add]; congr 1
    exact (K₀.of_triangle C (Triangle.mk fK gY δ) hT).symm
  -- Case split on K
  by_cases hKZ : IsZero K
  · -- K = 0: W(Y) = W(E), so Im(W(E) · rot) < 0, contradicting Im = 0
    have hWK : ssf.W (K₀.of C K) = 0 := by rw [K₀.of_isZero C hKZ, map_zero]
    have hWY : ssf.W (K₀.of C Y) = ssf.W (K₀.of C E) := by
      have h := hK₀; rw [hWK, zero_add] at h; exact h
    rw [hWY] at him_Y_neg; linarith
  · -- K nonzero: Im(W(K) · rot) > 0 → wPhaseOf(W(K)) > ψ → contradicts semistability
    have him_K_pos := im_pos_of_sum_zero_and_neg hK₀ him_E_zero him_Y_neg
    -- wPhaseOf(W(K)) ∈ (ψ - 1, ψ + 1) via bounds on the original interval
    have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C K)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hKZ ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) hKI hW_ne hperturb_gt
    have hK_hi : wPhaseOf (ssf.W (K₀.of C K)) ssf.α < b + ε₀ :=
      wPhaseOf_lt_of_intervalProp C σ hKZ ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.2])) hKI hW_ne hperturb_lt
    -- wPhaseOf(W(K)) > ψ (from Im > 0 + range condition)
    linarith [wPhaseOf_gt_of_im_pos him_K_pos
      (show wPhaseOf (ssf.W (K₀.of C K)) ssf.α ∈ Set.Ioo (ψ - 1) (ψ + 1) from
        ⟨by linarith, by linarith⟩),
      hsemistable hT hKI hYI hKZ]

variable [IsTriangulated C] in
/-- **Bridgeland's Lemma 7.3 (phase confinement).** If `E` is W-semistable of W-phase `ψ`
in `P((a, b))`, the interval is thin enough, and each nonzero semistable factor has W-phase
within `ε₀` of its σ-phase, then `σ.phiMinus(E) ∈ [ψ - ε₀, ψ + ε₀]` and
`σ.phiPlus(E) ∈ [ψ - ε₀, ψ + ε₀]`. In particular, the σ-phases of `E` are confined to
a window of width `2ε₀` centered at the W-phase `ψ`. -/
theorem phase_confinement_of_wSemistable
    (σ : StabilityCondition C) {E : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ : ℝ} (hSS : ssf.Semistable C E ψ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀) :
    ψ - ε₀ ≤ σ.slicing.phiMinus C E hSS.2.1 ∧
    σ.slicing.phiPlus C E hSS.2.1 ≤ ψ + ε₀ :=
  ⟨phiMinus_ge_of_wSemistable C σ hSS hε₀ hthin hperturb,
   phiPlus_le_of_wSemistable C σ hSS hε₀ hthin hperturb⟩

variable [IsTriangulated C] in
/-- **Weak hom-vanishing for W-semistable objects.** If `E` is W-semistable of W-phase `ψ₁`
and `F` is W-semistable of W-phase `ψ₂` with `ψ₁ > ψ₂ + 2ε₀`, then `Hom(E, F) = 0`.

This follows from phase confinement: `E ∈ P((ψ₁-ε₀-δ, ψ₁+ε₀+δ))` and
`F ∈ P((ψ₂-ε₀-δ, ψ₂+ε₀+δ))`, and the intervals are disjoint when
`ψ₁ - ψ₂ > 2ε₀ + 2δ`. -/
theorem hom_eq_zero_of_wSemistable_gap
    (σ : StabilityCondition C) {E F : C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {ψ₁ ψ₂ : ℝ}
    (hE : ssf.Semistable C E ψ₁) (hF : ssf.Semistable C F ψ₂)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hperturb : ∀ (G : C) (φ : ℝ), (σ.slicing.P φ) G → ¬IsZero G →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C G)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C G)) ssf.α < φ + ε₀)
    (hgap : ψ₁ > ψ₂ + 2 * ε₀)
    (f : E ⟶ F) : f = 0 := by
  -- Phase confinement: intrinsic phases are within ε₀ of W-phases
  have ⟨hE_lo, hE_hi⟩ := phase_confinement_of_wSemistable C σ hE hε₀ hthin hperturb
  have ⟨hF_lo, hF_hi⟩ := phase_confinement_of_wSemistable C σ hF hε₀ hthin hperturb
  -- Choose δ > 0 small enough that the widened intervals are still disjoint
  set δ := (ψ₁ - ψ₂ - 2 * ε₀) / 4 with hδ_def
  have hδ_pos : 0 < δ := by linarith
  -- E ∈ P((ψ₁-ε₀-δ, ψ₁+ε₀+δ))
  have hEI : σ.slicing.intervalProp C (ψ₁ - ε₀ - δ) (ψ₁ + ε₀ + δ) E :=
    σ.slicing.intervalProp_of_intrinsic_phases C hE.2.1
      (by linarith) (by linarith)
  -- F ∈ P((ψ₂-ε₀-δ, ψ₂+ε₀+δ))
  have hFI : σ.slicing.intervalProp C (ψ₂ - ε₀ - δ) (ψ₂ + ε₀ + δ) F :=
    σ.slicing.intervalProp_of_intrinsic_phases C hF.2.1
      (by linarith) (by linarith)
  -- The gap: ψ₂+ε₀+δ ≤ ψ₁-ε₀-δ
  have hdisjoint : ψ₂ + ε₀ + δ ≤ ψ₁ - ε₀ - δ := by linarith
  -- Apply interval hom-vanishing
  exact σ.slicing.intervalHom_eq_zero C hEI hFI hdisjoint f

variable [IsTriangulated C] in
/-- **Phase confinement from stabSeminorm.** If `E` is W-semistable with W-phase `ψ` in a
thin interval `(a, b)` with `b - a + 2ε₀ < 1`, and `‖W - Z‖_σ < sin(πε₀)`, then
E's σ-phases are within `ε₀` of `ψ`:
`ψ - ε₀ ≤ phiMinus(E) ≤ phiPlus(E) ≤ ψ + ε₀`. -/
theorem phase_confinement_from_stabSeminorm
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a b : ℝ} (hab : a < b)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {ψ : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ) :
    ψ - ε₀ ≤ σ.slicing.phiMinus C E hSS.2.1 ∧
    σ.slicing.phiPlus C E hSS.2.1 ≤ ψ + ε₀ := by
  have hthin1 : b - a < 1 := by linarith
  exact phase_confinement_of_wSemistable C σ hSS hε₀ hthin
    (hperturb_of_stabSeminorm C σ W hW hthin1 hε₀ hε₀2 hsin)

/-! ### Extension-closure of `intervalProp` over Postnikov towers -/

/-- Extension-closure of `intervalProp` over Postnikov towers: if all factors of a
Postnikov tower have HN phases in `(a, b)`, then the total object does too.

This follows by induction on the tower length, applying `intervalProp_of_triangle`
at each step. -/
private lemma intervalProp_of_postnikovTower (s : Slicing C) {E : C} {a b : ℝ}
    (P : PostnikovTower C E)
    (hfactors : ∀ i, s.intervalProp C a b (P.factor i)) :
    s.intervalProp C a b E := by
  suffices h : ∀ k (hk : k ≤ P.n),
      s.intervalProp C a b (P.chain.obj' k (by omega)) by
    have hchain := h P.n le_rfl
    rw [show P.chain.obj' P.n (by omega) = P.chain.right from rfl] at hchain
    rcases hchain with hZ | ⟨F, hF⟩
    · exact Or.inl ((Iso.isZero_iff (Classical.choice P.top_iso)).mp hZ)
    · exact Or.inr ⟨F.ofIso C (Classical.choice P.top_iso), hF⟩
  intro k
  induction k with
  | zero =>
    intro _
    rw [show P.chain.obj' 0 (by omega) = P.chain.left from rfl]
    exact Or.inl P.base_isZero
  | succ k ih =>
    intro hk
    have hchain_k := ih (by omega)
    set T := P.triangle ⟨k, by omega⟩
    have hT := P.triangle_dist ⟨k, by omega⟩
    have e₁ := Classical.choice (P.triangle_obj₁ ⟨k, by omega⟩)
    have e₂ := Classical.choice (P.triangle_obj₂ ⟨k, by omega⟩)
    -- intervalProp for T.obj₁ (≅ chain(k))
    have h₁ : s.intervalProp C a b T.obj₁ := by
      rcases hchain_k with hZ | ⟨F, hF⟩
      · exact Or.inl ((Iso.isZero_iff e₁.symm).mp hZ)
      · exact Or.inr ⟨F.ofIso C e₁.symm, hF⟩
    -- intervalProp for T.obj₃ = factor(k)
    have h₃ : s.intervalProp C a b T.obj₃ := hfactors ⟨k, by omega⟩
    -- Apply intervalProp_of_triangle
    have h₂ : s.intervalProp C a b T.obj₂ :=
      s.intervalProp_of_triangle C h₁ h₃ hT
    -- Transport to chain(k+1)
    rcases h₂ with hZ | ⟨F, hF⟩
    · exact Or.inl ((Iso.isZero_iff e₂).mp hZ)
    · exact Or.inr ⟨F.ofIso C e₂, hF⟩

/-! ### P(φ) closure under K₀ decomposition in the heart

**Bridgeland Lemma 5.2** (each P(φ) is abelian). The key step is that P(φ) is closed
under subobjects and quotients in the heart P((φ-1, φ]). The proof uses the imaginary
part of the central charge: if Z(E) = Z(K) + Z(Q) with E ∈ P(φ), and K, Q have all
σ-phases in (φ-1, φ], then Im(Z(K) · exp(-iπφ)) ≤ 0 (each factor contributes
non-positive imaginary part after rotation), and the sum being zero forces all factors
to have phase exactly φ. -/

/-- **Im non-positivity for heart objects rotated by φ.** If each nonzero σ-semistable
factor of phase `ψ ∈ (a, b)` with `ψ ≤ φ` and `ψ > φ - 1` has non-positive
`Im(Z(F) · exp(-iπφ))`, and E ∈ P((a, b))` with phases ≤ φ and > φ-1, then
`Im(Z(E) · exp(-iπφ)) ≤ 0`. -/
theorem im_Z_nonpos_of_heart_phases
    (σ : StabilityCondition C) {φ : ℝ}
    {E : C} (hE : ¬IsZero E)
    (hle : σ.slicing.phiPlus C E hE ≤ φ)
    (hgt : φ - 1 < σ.slicing.phiMinus C E hE) :
    (σ.Z (K₀.of C E) *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im ≤ 0 := by
  -- Get HN filtration with nonzero first and last factors
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  -- Phase bounds for all factors: φ - 1 < F.φ i ≤ φ
  have hphases : ∀ i : Fin F.n, φ - 1 < F.φ i ∧ F.φ i ≤ φ := by
    intro i
    exact ⟨by calc φ - 1 < σ.slicing.phiMinus C E hE := hgt
          _ = F.φ ⟨F.n - 1, by omega⟩ :=
            σ.slicing.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C E hE :=
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
          _ ≤ φ := hle⟩
  -- K₀ decomposition: Z(E) = Σ Z(factors)
  set P := F.toPostnikovTower
  rw [show σ.Z (K₀.of C E) = ∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) from by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]]
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  rw [Finset.sum_mul, show (∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) * rot).im =
      ∑ i : Fin F.n, (σ.Z (K₀.of C (P.factor i)) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  -- Each term ≤ 0
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : IsZero (P.factor i)
  · simp [K₀.of_isZero C hi]
  · -- Nonzero factor: Z(factor) = m · exp(iπ · F.φ i) with m > 0
    obtain ⟨m, hm, hval⟩ := σ.compat (F.φ i) (P.factor i) (F.semistable i) hi
    rw [hval, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * F.φ i) * Complex.I + -(↑(Real.pi * φ) * Complex.I) =
        ↑(Real.pi * (F.φ i - φ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    -- m * sin(π(F.φ i - φ)) ≤ 0 since F.φ i - φ ∈ (-1, 0]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, (hphases i).2])
        (by nlinarith [Real.pi_pos, (hphases i).1]))

/-- **From Im = 0 to P(φ).** If `X` is a nonzero object with all σ-phases in
`(φ-1, φ]` (i.e., in the heart) and `Im(Z(X) · exp(-iπφ)) = 0`, then `X ∈ P(φ)`.

The proof uses K₀ decomposition: each HN factor of `X` contributes
`≤ 0` to the sum (by `im_Z_nonpos_of_heart_phases`), and the sum is `0`, so each
contribution is `0`. For nonzero factors, `sin(π(ψ-φ)) = 0` with `ψ ∈ (φ-1, φ]`
forces `ψ = φ`. By strict anti of HN phases, `X` has exactly one factor. -/
theorem P_phi_of_im_zero_heart
    (σ : StabilityCondition C) {φ : ℝ}
    {X : C} (hXne : ¬IsZero X)
    (hX_le : σ.slicing.phiPlus C X hXne ≤ φ)
    (hX_gt : φ - 1 < σ.slicing.phiMinus C X hXne)
    (him_zero : (σ.Z (K₀.of C X) *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im = 0) :
    σ.slicing.P φ X := by
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hXne
  -- All factor phases lie in (φ-1, φ]
  have hphases : ∀ i : Fin F.n, φ - 1 < F.φ i ∧ F.φ i ≤ φ := by
    intro i
    exact ⟨by calc φ - 1 < σ.slicing.phiMinus C X hXne := hX_gt
          _ = F.φ ⟨F.n - 1, by omega⟩ :=
            σ.slicing.phiMinus_eq C X hXne F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C X hXne :=
            (σ.slicing.phiPlus_eq C X hXne F hn hfirst).symm
          _ ≤ φ := hX_le⟩
  -- K₀ decomposition: Z(X) = Σ Z(factor_i)
  have hZX : σ.Z (K₀.of C X) =
      ∑ i : Fin F.n,
        σ.Z (K₀.of C (F.toPostnikovTower.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C F.toPostnikovTower, map_sum]
  -- Each Im term ≤ 0
  have hterms : ∀ i ∈ Finset.univ,
      (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im ≤ 0 := by
    intro i _
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · simp [K₀.of_isZero C hi]
    · obtain ⟨mi, hmi, hvali⟩ := σ.compat (F.φ i) _ (F.semistable i) hi
      rw [hvali, mul_assoc, ← Complex.exp_add]
      have hargi : ↑(Real.pi * F.φ i) * Complex.I +
          -(↑(Real.pi * φ) * Complex.I) =
          ↑(Real.pi * (F.φ i - φ)) * Complex.I := by push_cast; ring
      rw [hargi, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        zero_mul, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hmi)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (by nlinarith [Real.pi_pos, (hphases i).2])
          (by nlinarith [Real.pi_pos, (hphases i).1]))
  -- Sum = 0
  have hsum : ∑ i ∈ Finset.univ,
      (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im = 0 := by
    have : (σ.Z (K₀.of C X) * rot).im =
        ∑ i : Fin F.n,
          (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im := by
      rw [hZX, Finset.sum_mul]
      exact map_sum Complex.imAddGroupHom _ _
    linarith
  -- Each term = 0
  have hterm_zero : ∀ i ∈ Finset.univ,
      (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterms).mp hsum
  -- Nonzero factors have phase = φ
  have factor_eq : ∀ i : Fin F.n,
      ¬IsZero (F.toPostnikovTower.factor i) → F.φ i = φ := by
    intro i hi
    have him := hterm_zero i (Finset.mem_univ _)
    obtain ⟨mi, hmi, hvali⟩ := σ.compat (F.φ i) _ (F.semistable i) hi
    rw [hvali, mul_assoc, ← Complex.exp_add] at him
    have hargi : ↑(Real.pi * F.φ i) * Complex.I +
        -(↑(Real.pi * φ) * Complex.I) =
        ↑(Real.pi * (F.φ i - φ)) * Complex.I := by push_cast; ring
    rw [hargi, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero] at him
    have hsin_zero : Real.sin (Real.pi * (F.φ i - φ)) = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · linarith
      · exact h
    by_contra hne
    have hlt : F.φ i - φ < 0 := lt_of_le_of_ne
      (by linarith [(hphases i).2]) (sub_ne_zero.mpr hne)
    exact absurd hsin_zero (ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, (hphases i).1])))
  -- Top and bottom nonzero factors have phase φ → n = 1
  have htop : F.φ ⟨0, hn⟩ = φ := factor_eq ⟨0, hn⟩ hfirst
  have hbot : F.φ ⟨F.n - 1, by omega⟩ = φ := factor_eq ⟨F.n - 1, by omega⟩ hlast
  have hn1 : F.n = 1 := by
    by_contra h
    have := F.hφ (show (⟨0, hn⟩ : Fin F.n) < ⟨F.n - 1, by omega⟩ from
      Fin.mk_lt_mk.mpr (by omega))
    linarith
  -- X ≅ factor 0 ∈ P(φ)
  have hfact : σ.slicing.P φ (F.toPostnikovTower.factor ⟨0, hn⟩) := by
    rw [← htop]; exact F.semistable ⟨0, hn⟩
  let T := F.triangle ⟨0, hn⟩
  have hZ₁ : IsZero T.obj₁ :=
    IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩))
  have : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp hZ₁
  have hobj₂_eq : F.chain.obj' (0 + 1) (by omega) =
      F.chain.obj (Fin.last F.n) :=
    congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; omega))
  let e₂ : T.obj₂ ≅ X :=
    (Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)).trans
      ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  haveI := σ.slicing.closedUnderIso φ
  exact (σ.slicing.P φ).prop_of_iso (e₂.symm.trans (asIso T.mor₂)).symm hfact

/-- **P(φ) closure under subobjects and quotients.** If `E ∈ P(φ)` is nonzero
and `K → E → Q → K⟦1⟧` is a distinguished triangle where both `K` and `Q` have
all σ-phases in `(φ-1, φ]` (both in the heart), then both `K ∈ P(φ)` and
`Q ∈ P(φ)`.

This is the key step in **Bridgeland's Lemma 5.2** (each P(φ) is abelian). -/
theorem P_phi_of_heart_triangle
    (σ : StabilityCondition C) {φ : ℝ}
    {K E Q : C} {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hPφ : σ.slicing.P φ E) (hE : ¬IsZero E)
    (hKne : ¬IsZero K)
    (hK_le : σ.slicing.phiPlus C K hKne ≤ φ)
    (hK_gt : φ - 1 < σ.slicing.phiMinus C K hKne)
    (hQne : ¬IsZero Q)
    (hQ_le : σ.slicing.phiPlus C Q hQne ≤ φ)
    (hQ_gt : φ - 1 < σ.slicing.phiMinus C Q hQne) :
    σ.slicing.P φ K ∧ σ.slicing.P φ Q := by
  -- K₀ additivity: Z(E) = Z(K) + Z(Q)
  have hZsum : σ.Z (K₀.of C E) = σ.Z (K₀.of C K) + σ.Z (K₀.of C Q) := by
    have h := K₀.of_triangle C (Triangle.mk f₁ f₂ f₃) hT
    simp only [Pretriangulated.Triangle.mk] at h
    rw [h, map_add]
  -- Im(Z(E) · exp(-iπφ)) = 0
  obtain ⟨mE, hmE, hvE⟩ := σ.compat φ E hPφ hE
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  have him_E : (σ.Z (K₀.of C E) * rot).im = 0 := by
    rw [hvE, mul_assoc, ← Complex.exp_add]
    have : ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * φ) * Complex.I) = 0 := by ring
    rw [this, Complex.exp_zero, mul_one, Complex.ofReal_im]
  -- Im(Z(K) · rot) ≤ 0 and Im(Z(Q) · rot) ≤ 0
  have him_K := im_Z_nonpos_of_heart_phases C σ hKne hK_le hK_gt
  have him_Q := im_Z_nonpos_of_heart_phases C σ hQne hQ_le hQ_gt
  -- Sum = 0 forces both = 0
  have : (σ.Z (K₀.of C K) * rot).im + (σ.Z (K₀.of C Q) * rot).im = 0 := by
    have : (σ.Z (K₀.of C E) * rot).im =
        (σ.Z (K₀.of C K) * rot).im + (σ.Z (K₀.of C Q) * rot).im := by
      rw [hZsum, add_mul, Complex.add_im]
    linarith
  have him_K_zero : (σ.Z (K₀.of C K) * rot).im = 0 := by linarith
  have him_Q_zero : (σ.Z (K₀.of C Q) * rot).im = 0 := by linarith
  exact ⟨P_phi_of_im_zero_heart C σ hKne hK_le hK_gt him_K_zero,
    P_phi_of_im_zero_heart C σ hQne hQ_le hQ_gt him_Q_zero⟩

/-- **Im non-negativity for objects with phases above φ.** If `X` has all σ-phases in
`[φ, φ + 1)` (i.e., `φ ≤ phiMinus` and `phiPlus < φ + 1`), then
`Im(Z(X) · exp(-iπφ)) ≥ 0`. Symmetric to `im_Z_nonpos_of_heart_phases`. -/
theorem im_Z_nonneg_of_phases_above
    (σ : StabilityCondition C) {φ : ℝ}
    {E : C} (hE : ¬IsZero E)
    (hge : φ ≤ σ.slicing.phiMinus C E hE)
    (hlt : σ.slicing.phiPlus C E hE < φ + 1) :
    0 ≤ (σ.Z (K₀.of C E) *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im := by
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hE
  have hphases : ∀ i : Fin F.n, φ ≤ F.φ i ∧ F.φ i < φ + 1 := by
    intro i
    exact ⟨by calc φ ≤ σ.slicing.phiMinus C E hE := hge
          _ = F.φ ⟨F.n - 1, by omega⟩ :=
            σ.slicing.phiMinus_eq C E hE F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C E hE :=
            (σ.slicing.phiPlus_eq C E hE F hn hfirst).symm
          _ < φ + 1 := hlt⟩
  set P := F.toPostnikovTower
  rw [show σ.Z (K₀.of C E) = ∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) from by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]]
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  rw [Finset.sum_mul, show (∑ i : Fin F.n, σ.Z (K₀.of C (P.factor i)) * rot).im =
      ∑ i : Fin F.n, (σ.Z (K₀.of C (P.factor i)) * rot).im from
    map_sum Complex.imAddGroupHom _ _]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : IsZero (P.factor i)
  · simp [K₀.of_isZero C hi]
  · obtain ⟨m, hm, hval⟩ := σ.compat (F.φ i) (P.factor i) (F.semistable i) hi
    rw [hval, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * F.φ i) * Complex.I + -(↑(Real.pi * φ) * Complex.I) =
        ↑(Real.pi * (F.φ i - φ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonneg (le_of_lt hm)
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos, (hphases i).1])
        (by nlinarith [Real.pi_pos, (hphases i).2]))

/-- **From Im = 0 to P(φ) for objects with phases above φ.** If `X` is nonzero with
all σ-phases in `[φ, φ + 1)` and `Im(Z(X) · exp(-iπφ)) = 0`, then `X ∈ P(φ)`.
Symmetric to `P_phi_of_im_zero_heart`. -/
theorem P_phi_of_im_zero_above
    (σ : StabilityCondition C) {φ : ℝ}
    {X : C} (hXne : ¬IsZero X)
    (hX_ge : φ ≤ σ.slicing.phiMinus C X hXne)
    (hX_lt : σ.slicing.phiPlus C X hXne < φ + 1)
    (him_zero : (σ.Z (K₀.of C X) *
      Complex.exp (-(↑(Real.pi * φ) * Complex.I))).im = 0) :
    σ.slicing.P φ X := by
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hXne
  have hphases : ∀ i : Fin F.n, φ ≤ F.φ i ∧ F.φ i < φ + 1 := by
    intro i
    exact ⟨by calc φ ≤ σ.slicing.phiMinus C X hXne := hX_ge
          _ = F.φ ⟨F.n - 1, by omega⟩ :=
            σ.slicing.phiMinus_eq C X hXne F hn hlast
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by calc F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = σ.slicing.phiPlus C X hXne :=
            (σ.slicing.phiPlus_eq C X hXne F hn hfirst).symm
          _ < φ + 1 := hX_lt⟩
  have hZX : σ.Z (K₀.of C X) =
      ∑ i : Fin F.n, σ.Z (K₀.of C (F.toPostnikovTower.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C F.toPostnikovTower, map_sum]
  have hterms : ∀ i ∈ Finset.univ,
      0 ≤ (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im := by
    intro i _
    by_cases hi : IsZero (F.toPostnikovTower.factor i)
    · simp [K₀.of_isZero C hi]
    · obtain ⟨mi, hmi, hvali⟩ := σ.compat (F.φ i) _ (F.semistable i) hi
      rw [hvali, mul_assoc, ← Complex.exp_add]
      have hargi : ↑(Real.pi * F.φ i) * Complex.I +
          -(↑(Real.pi * φ) * Complex.I) =
          ↑(Real.pi * (F.φ i - φ)) * Complex.I := by push_cast; ring
      rw [hargi, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        zero_mul, add_zero]
      exact mul_nonneg (le_of_lt hmi)
        (Real.sin_nonneg_of_nonneg_of_le_pi
          (by nlinarith [Real.pi_pos, (hphases i).1])
          (by nlinarith [Real.pi_pos, (hphases i).2]))
  have hsum : ∑ i ∈ Finset.univ,
      (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im = 0 := by
    have : (σ.Z (K₀.of C X) * rot).im =
        ∑ i : Fin F.n,
          (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im := by
      rw [hZX, Finset.sum_mul]
      exact map_sum Complex.imAddGroupHom _ _
    linarith
  have hterm_zero : ∀ i ∈ Finset.univ,
      (σ.Z (K₀.of C (F.toPostnikovTower.factor i)) * rot).im = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum
  have factor_eq : ∀ i : Fin F.n,
      ¬IsZero (F.toPostnikovTower.factor i) → F.φ i = φ := by
    intro i hi
    have him := hterm_zero i (Finset.mem_univ _)
    obtain ⟨mi, hmi, hvali⟩ := σ.compat (F.φ i) _ (F.semistable i) hi
    rw [hvali, mul_assoc, ← Complex.exp_add] at him
    have hargi : ↑(Real.pi * F.φ i) * Complex.I +
        -(↑(Real.pi * φ) * Complex.I) =
        ↑(Real.pi * (F.φ i - φ)) * Complex.I := by push_cast; ring
    rw [hargi, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero] at him
    have hsin_zero : Real.sin (Real.pi * (F.φ i - φ)) = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · linarith
      · exact h
    by_contra hne
    have hlt' : 0 < F.φ i - φ := lt_of_le_of_ne
      (by linarith [(hphases i).1]) (fun h ↦ hne (by linarith))
    exact absurd hsin_zero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, (hphases i).2])))
  have htop : F.φ ⟨0, hn⟩ = φ := factor_eq ⟨0, hn⟩ hfirst
  have hbot : F.φ ⟨F.n - 1, by omega⟩ = φ := factor_eq ⟨F.n - 1, by omega⟩ hlast
  have hn1 : F.n = 1 := by
    by_contra h
    have := F.hφ (show (⟨0, hn⟩ : Fin F.n) < ⟨F.n - 1, by omega⟩ from
      Fin.mk_lt_mk.mpr (by omega))
    linarith
  have hfact : σ.slicing.P φ (F.toPostnikovTower.factor ⟨0, hn⟩) := by
    rw [← htop]; exact F.semistable ⟨0, hn⟩
  let T := F.triangle ⟨0, hn⟩
  have hZ₁ : IsZero T.obj₁ :=
    IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩))
  have : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp hZ₁
  have hobj₂_eq : F.chain.obj' (0 + 1) (by omega) =
      F.chain.obj (Fin.last F.n) :=
    congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; omega))
  let e₂ : T.obj₂ ≅ X :=
    (Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)).trans
      ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  haveI := σ.slicing.closedUnderIso φ
  exact (σ.slicing.P φ).prop_of_iso (e₂.symm.trans (asIso T.mor₂)).symm hfact

/-! ### P(φ) is abelian (Bridgeland Lemma 5.2)

Each slicing slice `P(φ)` of a stability condition is an abelian category.
The proof uses:
1. Extension closure (`semistable_of_triangle`) for finite products
2. Hom-vanishing from the slicing for negative Hom spaces
3. Admissibility via the t-structure truncation from the shifted slicing,
   with a Z-ray argument promoting heart membership to P(φ) membership -/

/-- P(φ) is closed under biproducts for a stability condition. -/
lemma StabilityCondition.P_phi_biprod
    (σ : StabilityCondition C) {φ : ℝ} {X Y : C}
    (hX : σ.slicing.P φ X) (hY : σ.slicing.P φ Y) :
    σ.slicing.P φ (X ⊞ Y) :=
  σ.slicing.semistable_of_triangle C φ hX hY
    (binaryBiproductTriangle_distinguished X Y)

/-- P(φ) is closed under binary products for a stability condition. -/
instance StabilityCondition.P_phi_closedUnderBinaryProducts
    (σ : StabilityCondition C) (φ : ℝ) :
    (σ.slicing.P φ).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact (σ.slicing.P φ).prop_of_iso
      ((biprod.isoProd (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) ≪≫
        (HasLimit.isoOfNatIso (Discrete.natIso (fun ⟨j⟩ ↦ match j with
          | WalkingPair.left => Iso.refl _
          | WalkingPair.right => Iso.refl _))).symm)
      (σ.P_phi_biprod C (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

/-- P(φ) is closed under finite products for a stability condition. -/
instance StabilityCondition.P_phi_closedUnderFiniteProducts
    (σ : StabilityCondition C) (φ : ℝ) :
    (σ.slicing.P φ).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- P(φ) has finite products for a stability condition. -/
noncomputable instance StabilityCondition.P_phi_hasFiniteProducts
    (σ : StabilityCondition C) (φ : ℝ) :
    HasFiniteProducts (σ.slicing.P φ).FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **No negative Hom spaces in P(φ).** For `X, Y ∈ P(φ)`, every morphism
`ι X ⟶ (ι Y)⟦n⟧` is zero when `n < 0`. Y⟦n⟧ ∈ P(φ+n)` by the shift axiom,
and since `n < 0` we have `φ > φ + n`, so hom-vanishing applies. -/
theorem StabilityCondition.P_phi_hom_vanishing
    (σ : StabilityCondition C) (φ : ℝ) :
    ∀ ⦃X Y : (σ.slicing.P φ).FullSubcategory⦄ ⦃n : ℤ⦄
      (f : (σ.slicing.P φ).ι.obj X ⟶ ((σ.slicing.P φ).ι.obj Y)⟦n⟧),
      n < 0 → f = 0 := by
  intro X Y n f hn
  exact σ.slicing.hom_vanishing φ (φ + ↑n) X.obj (Y.obj⟦n⟧)
    (by linarith [show (↑n : ℝ) < 0 from Int.cast_lt_zero.mpr hn])
    X.property
    ((σ.slicing.shift_int C φ Y.obj n).mp Y.property) f

set_option backward.isDefEq.respectTransparency false in
variable [IsTriangulated C] in
/-- **P(φ) membership for truncation of a P(φ)-cone** (**Bridgeland's Lemma 5.2**).
Given a distinguished triangle `A → B → X₃ → A⟦1⟧` with `A, B ∈ P(φ)`, the
t-structure truncation pieces of `X₃` (from the shifted slicing) lie in `P(φ)`.

The proof uses K₀ additivity and sign analysis of `Im(Z(·) · exp(-iπφ))`.
From the original triangle, `Im(Z(X₃)·rot) = 0`. From the truncation triangle,
`Im(Z(L)·rot) + Im(Z(Q)·rot) = 0`. Since Q has phases in `(φ-1, φ]`, we get
`Im(Z(Q)·rot) ≤ 0`. Since L has phases in `(φ, φ+1]`, an extra π rotation
gives `Im(Z(L)·rot) ≥ 0`. Both must vanish, and `P_phi_of_im_zero_heart`
promotes to `Q ∈ P(φ)` and `L ∈ P(φ+1)`. -/
private theorem P_phi_of_truncation_of_P_phi_cone
    (σ : StabilityCondition C) (φ : ℝ)
    {A B X₃ : C} (hA : σ.slicing.P φ A) (hB : σ.slicing.P φ B)
    {f₁ : A ⟶ B} {f₂ : B ⟶ X₃} {f₃ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    σ.slicing.P φ
      (((σ.slicing.phaseShift C (φ - 1)).toTStructure.truncGE 0).obj X₃) ∧
    σ.slicing.P φ
      ((((σ.slicing.phaseShift C (φ - 1)).toTStructure.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) := by
  set s := σ.slicing
  set ss := s.phaseShift C (φ - 1)
  set t := ss.toTStructure
  -- P(φ) objects have phase 1 in the shifted slicing
  have hP1A : ss.P 1 A := by
    change s.P (1 + (φ - 1)) A; rw [show (1 : ℝ) + (φ - 1) = φ from by ring]; exact hA
  have hP1B : ss.P 1 B := by
    change s.P (1 + (φ - 1)) B; rw [show (1 : ℝ) + (φ - 1) = φ from by ring]; exact hB
  have cast_le : (-↑(0 : ℤ) : ℝ) = 0 := by simp
  have cast_ge : (1 - ↑(0 : ℤ) : ℝ) = 1 := by simp
  -- A, B are in the heart of t
  haveI hA_le : t.IsLE A 0 := ⟨by
    change ss.gtProp C (-↑(0 : ℤ)) A; rw [cast_le]
    exact ss.gtProp_of_semistable C 1 0 A hP1A (by norm_num)⟩
  haveI hB_le : t.IsLE B 0 := ⟨by
    change ss.gtProp C (-↑(0 : ℤ)) B; rw [cast_le]
    exact ss.gtProp_of_semistable C 1 0 B hP1B (by norm_num)⟩
  haveI : t.IsGE A 0 := ⟨by
    change ss.leProp C (1 - ↑(0 : ℤ)) A; rw [cast_ge]
    exact ss.leProp_of_semistable C 1 1 A hP1A le_rfl⟩
  haveI : t.IsGE B 0 := ⟨by
    change ss.leProp C (1 - ↑(0 : ℤ)) B; rw [cast_ge]
    exact ss.leProp_of_semistable C 1 1 B hP1B le_rfl⟩
  -- Shift bounds for the rotation
  haveI : t.IsLE (A⟦(1 : ℤ)⟧) 0 := by
    haveI := t.isLE_shift A 0 1 (-1); exact t.isLE_of_le _ (-1) 0
  haveI : t.IsGE B (-1) := t.isGE_of_ge _ (-1) 0
  haveI : t.IsGE (A⟦(1 : ℤ)⟧) (-1) := t.isGE_shift A 0 1 (-1)
  -- X₃ bounds from the rotation triangle
  have hrot := rot_of_distTriang _ hT
  haveI hX₃_le : t.IsLE X₃ 0 := by
    refine t.isLE₂ _ hrot 0 ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂]; exact hB_le
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁]
      exact ‹t.IsLE (A⟦(1 : ℤ)⟧) 0›
  haveI : t.IsGE X₃ (-1) := by
    refine t.isGE₂ _ hrot (-1) ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂]; exact ‹t.IsGE B (-1)›
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁]
      exact ‹t.IsGE (A⟦(1 : ℤ)⟧) (-1)›
  -- Truncation of X₃
  have htrunc := t.triangleLTGE_distinguished 0 X₃
  -- Q bounds: IsLE 0, IsGE 0 (heart)
  haveI hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    have hrot_trunc := rot_of_distTriang _ htrunc
    refine t.isLE₂ _ hrot_trunc 0 ?_ ?_
    · dsimp; exact hX₃_le
    · dsimp
      haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      haveI := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  haveI : t.IsGE ((t.truncGE 0).obj X₃) 0 := inferInstance
  -- L bounds: IsLE(-1), IsGE(-1)
  haveI hL_le : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  haveI : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    have hinv := inv_rot_of_distTriang _ htrunc
    refine t.isGE₂ _ hinv (-1) ?_ ?_
    · dsimp
      haveI : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 :=
        t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · dsimp; exact ‹t.IsGE X₃ (-1)›
  -- Convert t-structure bounds to original slicing phase bounds
  -- Q has s-phases in (φ-1, φ]
  have hQ_sgt : s.gtProp C (φ - 1) ((t.truncGE 0).obj X₃) :=
    (s.phaseShift_gtProp_zero C (φ - 1) _).mp (by
      have h := hQ_le.le; change ss.gtProp C (-↑(0 : ℤ)) _ at h; rwa [cast_le] at h)
  have hQ_sle : s.leProp C φ ((t.truncGE 0).obj X₃) := by
    have h : ss.leProp C 1 ((t.truncGE 0).obj X₃) := by
      have h := (inferInstance : t.IsGE ((t.truncGE 0).obj X₃) 0).ge
      change ss.leProp C (1 - ↑(0 : ℤ)) _ at h; rwa [cast_ge] at h
    rcases h with hZ | ⟨F, hF, hle⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiPlus]; linarith⟩
  -- L has s-phases in (φ, φ+1]
  have hL_sgt : s.gtProp C φ ((t.truncLT 0).obj X₃) := by
    have h : ss.gtProp C 1 ((t.truncLT 0).obj X₃) := by
      have h := hL_le.le; change ss.gtProp C (-↑(-1 : ℤ)) _ at h
      simpa only [Int.cast_neg, Int.cast_one, neg_neg] using h
    rcases h with hZ | ⟨F, hF, hgt⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiMinus] at hgt
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiMinus]; linarith⟩
  have hL_sle : s.leProp C (φ + 1) ((t.truncLT 0).obj X₃) := by
    have h : ss.leProp C (1 + 1) ((t.truncLT 0).obj X₃) := by
      have h := (inferInstance : t.IsGE ((t.truncLT 0).obj X₃) (-1)).ge
      change ss.leProp C (1 - ↑(-1 : ℤ)) _ at h
      simpa only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] using h
    rcases h with hZ | ⟨F, hF, hle⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiPlus]; linarith⟩
  -- === Epi approach for Q, K₀ for L ===
  have hB_heart : t.heart B := (t.mem_heart_iff _).mpr ⟨hB_le, inferInstance⟩
  have hQ_heart : t.heart ((t.truncGE 0).obj X₃) :=
    (t.mem_heart_iff _).mpr ⟨hQ_le, inferInstance⟩
  letI := t.hasHeartFullSubcategory
  let B_H : t.heart.FullSubcategory := ⟨B, hB_heart⟩
  let Q_H : t.heart.FullSubcategory := ⟨(t.truncGE 0).obj X₃, hQ_heart⟩
  let g_C : B ⟶ (t.truncGE 0).obj X₃ :=
    f₂ ≫ ((t.triangleLTGE 0).obj X₃).mor₂
  let g_H : B_H ⟶ Q_H := ObjectProperty.homMk g_C
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  -- Type conversion for ι.obj
  have hι_simp : ∀ (X : t.heart.FullSubcategory), ι.obj X = X.obj := by
    intro X; rfl
  -- g_H is epi in the heart
  haveI : Epi g_H := by
    rw [Preadditive.epi_iff_cancel_zero]
    intro R k hk
    haveI : t.IsGE R.obj 0 :=
      ((t.mem_heart_iff R.obj).mp R.property).2
    have hk_C : g_C ≫ k.hom = 0 := by
      have := congr_arg InducedCategory.Hom.hom hk
      simp only [ObjectProperty.FullSubcategory.comp_hom] at this
      exact this
    have hmk : ((t.triangleLTGE 0).obj X₃).mor₂ ≫ k.hom = 0 := by
      have : f₂ ≫ (((t.triangleLTGE 0).obj X₃).mor₂ ≫ k.hom) = 0 := by
        rwa [← Category.assoc]
      obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃
        (Triangle.mk f₁ f₂ f₃) hT _ this
      dsimp only [Triangle.mk] at a ha
      haveI : t.IsLE (A⟦(1 : ℤ)⟧) (-1) := t.isLE_shift A 0 1 (-1)
      rw [show a = 0 from t.zero a (-1) 0 (by norm_num), comp_zero] at ha
      exact ha
    obtain ⟨b, hb⟩ := Triangle.yoneda_exact₃
      ((t.triangleLTGE 0).obj X₃) htrunc k.hom hmk
    dsimp only [TStructure.triangleLTGE, Triangle.functorMk, Triangle.mk] at b hb
    haveI : t.IsLE (((t.truncLT 0).obj X₃)⟦(1 : ℤ)⟧) (-2) :=
      t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
    rw [show b = 0 from t.zero b (-2) 0 (by norm_num), comp_zero] at hb
    exact ObjectProperty.hom_ext (P := t.heart) hb
  -- Get heart triangle I → B → Q → I⟦1⟧
  obtain ⟨I_H, i_H, δ_heart, hT_heart⟩ :=
    AbelianSubcategory.exists_distinguished_triangle_of_epi
      (TStructure.heart_hι t) (TStructure.heart_admissible t) g_H
  -- K₀ conversions via eqToIso
  have hK₀_B : K₀.of C (ι.obj B_H) = K₀.of C B :=
    K₀.of_iso C (eqToIso (hι_simp B_H))
  have hK₀_I : K₀.of C (ι.obj I_H) = K₀.of C I_H.obj :=
    K₀.of_iso C (eqToIso (hι_simp I_H))
  have hK₀_Q : K₀.of C (ι.obj Q_H) = K₀.of C ((t.truncGE 0).obj X₃) :=
    K₀.of_iso C (eqToIso (hι_simp Q_H))
  have hK₀_heart : K₀.of C B =
      K₀.of C I_H.obj + K₀.of C ((t.truncGE 0).obj X₃) := by
    have h := K₀.of_triangle C _ hT_heart
    dsimp only [Triangle.mk] at h; rwa [hK₀_B, hK₀_I, hK₀_Q] at h
  -- I_H phase bounds
  haveI hI_le : t.IsLE I_H.obj 0 :=
    ((t.mem_heart_iff I_H.obj).mp I_H.property).1
  haveI hI_ge : t.IsGE I_H.obj 0 :=
    ((t.mem_heart_iff I_H.obj).mp I_H.property).2
  have hI_sgt : s.gtProp C (φ - 1) I_H.obj :=
    (s.phaseShift_gtProp_zero C (φ - 1) _).mp (by
      have h := hI_le.le; change ss.gtProp C (-↑(0 : ℤ)) _ at h; rwa [cast_le] at h)
  have hI_sle : s.leProp C φ I_H.obj := by
    have h : ss.leProp C 1 I_H.obj := by
      have h := hI_ge.ge
      change ss.leProp C (1 - ↑(0 : ℤ)) _ at h; rwa [cast_ge] at h
    rcases h with hZ | ⟨F, hF, hle⟩
    · exact Or.inl hZ
    · simp only [HNFiltration.phiPlus] at hle
      exact Or.inr ⟨⟨F.toPostnikovTower, fun i ↦ F.φ i + (φ - 1),
        fun i j hij ↦ by linarith [F.hφ hij], fun j ↦ F.semistable j⟩, hF, by
        dsimp only [HNFiltration.phiPlus]; linarith⟩
  -- === K₀ + Im(Z·rot) ===
  -- P(φ) objects lie on the real axis after rotation by exp(-iπφ)
  set rot := Complex.exp (-(↑(Real.pi * φ) * Complex.I))
  have him_ray : ∀ {E : C}, s.P φ E → (σ.Z (K₀.of C E) * rot).im = 0 := by
    intro E hPφ
    by_cases hne : IsZero E
    · simp [K₀.of_isZero C hne]
    · obtain ⟨m, _, hv⟩ := σ.compat φ E hPφ hne
      rw [hv, mul_assoc, ← Complex.exp_add,
        show ↑(Real.pi * φ) * Complex.I + -(↑(Real.pi * φ) * Complex.I) = 0 from
          by ring,
        Complex.exp_zero, mul_one, Complex.ofReal_im]
  -- K₀ on truncation triangle: Z(X₃) = Z(L) + Z(Q)
  have hZtrunc : σ.Z (K₀.of C X₃) =
      σ.Z (K₀.of C ((t.truncLT 0).obj X₃)) +
      σ.Z (K₀.of C ((t.truncGE 0).obj X₃)) := by
    have h := K₀.of_triangle C _ htrunc
    dsimp [TStructure.triangleLTGE] at h; rw [h, map_add]
  -- K₀ on original triangle: Im(Z(X₃)·rot) = 0 since A, B ∈ P(φ)
  have hZX₃_im : (σ.Z (K₀.of C X₃) * rot).im = 0 := by
    have hZorig : σ.Z (K₀.of C B) =
        σ.Z (K₀.of C A) + σ.Z (K₀.of C X₃) := by
      have h := K₀.of_triangle C _ hT
      dsimp [Triangle.mk] at h; rw [h, map_add]
    have : (σ.Z (K₀.of C A) * rot).im + (σ.Z (K₀.of C X₃) * rot).im =
        (σ.Z (K₀.of C B) * rot).im := by
      rw [← Complex.add_im, ← add_mul, hZorig]
    linarith [him_ray hA, him_ray hB]
  -- Q ∈ P(φ) via K₀ on heart triangle
  have hQ_Pφ : s.P φ ((t.truncGE 0).obj X₃) := by
    by_cases hQne : IsZero ((t.truncGE 0).obj X₃)
    · exact s.zero_mem' C φ _ hQne
    · by_cases hIne : IsZero I_H.obj
      · -- I = 0 ⟹ g_H is iso ⟹ Q ≅ B ∈ P(φ)
        have hIne' : IsZero (ι.obj I_H) := by rwa [hι_simp]
        haveI : IsIso (ι.map g_H) :=
          (Triangle.isZero₁_iff_isIso₂
            (Triangle.mk (ι.map i_H) (ι.map g_H) δ_heart) hT_heart).mp hIne'
        exact (s.P φ).prop_of_iso
          ((eqToIso (hι_simp B_H)).symm ≪≫
            asIso (ι.map g_H) ≪≫ eqToIso (hι_simp Q_H)) hB
      · -- Both I and Q nonzero: K₀ + Im argument in the heart
        have him_I := im_Z_nonpos_of_heart_phases C σ hIne
          (s.phiPlus_le_of_leProp C hIne hI_sle)
          (s.phiMinus_gt_of_gtProp C hIne hI_sgt)
        have him_Q := im_Z_nonpos_of_heart_phases C σ hQne
          (s.phiPlus_le_of_leProp C hQne hQ_sle)
          (s.phiMinus_gt_of_gtProp C hQne hQ_sgt)
        have him_sum_heart : (σ.Z (K₀.of C I_H.obj) * rot).im +
            (σ.Z (K₀.of C ((t.truncGE 0).obj X₃)) * rot).im = 0 := by
          have h : σ.Z (K₀.of C I_H.obj) * rot +
              σ.Z (K₀.of C ((t.truncGE 0).obj X₃)) * rot =
              σ.Z (K₀.of C B) * rot := by
            rw [← add_mul, ← map_add, ← hK₀_heart]
          have him := congr_arg Complex.im h
          simp only [Complex.add_im] at him
          linarith [him_ray hB]
        exact P_phi_of_im_zero_heart C σ hQne
          (s.phiPlus_le_of_leProp C hQne hQ_sle)
          (s.phiMinus_gt_of_gtProp C hQne hQ_sgt) (by linarith)
  -- Im(Z(L)·rot) = 0 from truncation K₀ + hZX₃_im + him_ray hQ_Pφ
  have hL_im0 : (σ.Z (K₀.of C ((t.truncLT 0).obj X₃)) * rot).im = 0 := by
    have : (σ.Z (K₀.of C ((t.truncLT 0).obj X₃)) * rot).im +
        (σ.Z (K₀.of C ((t.truncGE 0).obj X₃)) * rot).im =
        (σ.Z (K₀.of C X₃) * rot).im := by
      rw [← Complex.add_im, ← add_mul, ← hZtrunc]
    linarith [him_ray hQ_Pφ, hZX₃_im]
  -- L ∈ P(φ+1) via P_phi_of_im_zero_heart at phase φ+1
  have hL_Pφ1 : s.P (φ + 1) ((t.truncLT 0).obj X₃) := by
    by_cases hLne : IsZero ((t.truncLT 0).obj X₃)
    · exact s.zero_mem' C (φ + 1) _ hLne
    · exact P_phi_of_im_zero_heart C σ hLne
        (s.phiPlus_le_of_leProp C hLne hL_sle)
        (show φ + 1 - 1 < s.phiMinus C _ hLne from by
          linarith [s.phiMinus_gt_of_gtProp C hLne hL_sgt])
        (by rw [show -(↑(Real.pi * (φ + 1)) * Complex.I) =
              -(↑(Real.pi * φ) * Complex.I) + -(↑Real.pi * Complex.I) from by
                push_cast; ring,
            Complex.exp_add, ← mul_assoc,
            show Complex.exp (-(↑Real.pi * Complex.I)) = -1 from by
              rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one],
            mul_neg_one, Complex.neg_im, hL_im0, neg_zero])
  -- L⟦-1⟧ ∈ P(φ) via shift
  have hK_Pφ : s.P φ (((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) := by
    have h := (s.shift_int C (φ + 1) ((t.truncLT 0).obj X₃) (-1)).mp hL_Pφ1
    convert h using 1; push_cast; ring
  exact ⟨hQ_Pφ, hK_Pφ⟩

variable [IsTriangulated C] in
/-- **Admissibility of morphisms in P(φ)** (**Bridgeland's Lemma 5.2**). For any morphism
`f₁ : X₁ → X₂` in `P(φ)` and distinguished triangle `ι(X₁) → ι(X₂) → X₃ → ι(X₁)⟦1⟧`,
there exist `K, Q ∈ P(φ)` and a distinguished triangle `(ι K)⟦1⟧ → X₃ → ι Q`.

The proof uses the truncation from the t-structure `(s.phaseShift(φ-1)).toTStructure`
to decompose X₃, then promotes the truncation pieces from heart `P((φ-1, φ])`
to `P(φ)` via `P_phi_of_truncation_of_P_phi_cone` (the epi approach). -/
theorem StabilityCondition.P_phi_admissible
    (σ : StabilityCondition C) (φ : ℝ) :
    AbelianSubcategory.admissibleMorphism (σ.slicing.P φ).ι = ⊤ := by
  set s := σ.slicing
  set ss := s.phaseShift C (φ - 1)
  set t := ss.toTStructure
  ext X₁ X₂ f₁; simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  -- P(φ) objects have phase 1 in the shifted slicing
  have hP1 : ∀ X : (s.P φ).FullSubcategory, ss.P 1 X.obj := by
    intro X; change s.P (1 + (φ - 1)) X.obj
    rw [show (1 : ℝ) + (φ - 1) = φ from by ring]; exact X.property
  -- Cast cleanup helpers
  have cast_le : (-↑(0 : ℤ) : ℝ) = 0 := by simp
  have cast_ge : (1 - ↑(0 : ℤ) : ℝ) = 1 := by simp
  -- Step 1: P(φ) objects are IsLE 0 and IsGE 0 for t
  haveI hX₁_le : t.IsLE X₁.obj 0 := by
    refine ⟨?_⟩; change ss.gtProp C (-↑(0 : ℤ)) X₁.obj
    rw [cast_le]; exact ss.gtProp_of_semistable C 1 0 X₁.obj (hP1 X₁) (by norm_num)
  haveI hX₂_le : t.IsLE X₂.obj 0 := by
    refine ⟨?_⟩; change ss.gtProp C (-↑(0 : ℤ)) X₂.obj
    rw [cast_le]; exact ss.gtProp_of_semistable C 1 0 X₂.obj (hP1 X₂) (by norm_num)
  haveI hX₁_ge : t.IsGE X₁.obj 0 := by
    refine ⟨?_⟩; change ss.leProp C (1 - ↑(0 : ℤ)) X₁.obj
    rw [cast_ge]; exact ss.leProp_of_semistable C 1 1 X₁.obj (hP1 X₁) le_rfl
  haveI hX₂_ge : t.IsGE X₂.obj 0 := by
    refine ⟨?_⟩; change ss.leProp C (1 - ↑(0 : ℤ)) X₂.obj
    rw [cast_ge]; exact ss.leProp_of_semistable C 1 1 X₂.obj (hP1 X₂) le_rfl
  -- Shifted objects for the rotation
  haveI : t.IsLE (X₁.obj⟦(1 : ℤ)⟧) 0 := by
    haveI := t.isLE_shift X₁.obj 0 1 (-1); exact t.isLE_of_le _ (-1) 0
  haveI : t.IsGE X₂.obj (-1) := t.isGE_of_ge _ (-1) 0
  haveI : t.IsGE (X₁.obj⟦(1 : ℤ)⟧) (-1) := t.isGE_shift X₁.obj 0 1 (-1)
  -- Step 2: X₃ is IsLE 0 and IsGE(-1) from the rotation triangle
  have hrot := rot_of_distTriang _ hT
  haveI hX₃_le : t.IsLE X₃ 0 := by
    refine t.isLE₂ _ hrot 0 ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂, ObjectProperty.ι_obj]
      exact hX₂_le
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁, ObjectProperty.ι_obj]
      exact ‹t.IsLE (X₁.obj⟦(1 : ℤ)⟧) 0›
  haveI hX₃_ge : t.IsGE X₃ (-1) := by
    refine t.isGE₂ _ hrot (-1) ?_ ?_
    · simp only [Triangle.rotate_obj₁, Triangle.mk_obj₂, ObjectProperty.ι_obj]
      exact ‹t.IsGE X₂.obj (-1)›
    · simp only [Triangle.rotate_obj₃, Triangle.mk_obj₁, ObjectProperty.ι_obj]
      exact ‹t.IsGE (X₁.obj⟦(1 : ℤ)⟧) (-1)›
  -- Step 3: Truncation — decompose X₃ via the t-structure
  have htrunc := t.triangleLTGE_distinguished 0 X₃
  -- Q := (truncGE 0).obj X₃ is IsLE 0 (rotation of truncation + isLE₂)
  haveI hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    have hrot_trunc := rot_of_distTriang _ htrunc
    refine t.isLE₂ _ hrot_trunc 0 ?_ ?_
    · dsimp; exact hX₃_le
    · dsimp
      haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      haveI := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  -- (truncLT 0).obj X₃ is IsGE(-1) (inverse rotation + isGE₂)
  haveI hK_ge : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    have hinv := inv_rot_of_distTriang _ htrunc
    refine t.isGE₂ _ hinv (-1) ?_ ?_
    · dsimp
      haveI : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 :=
        t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · dsimp; exact hX₃_ge
  -- Q is in the heart (IsGE 0 by truncation + IsLE 0)
  haveI : t.IsGE ((t.truncGE 0).obj X₃) 0 := inferInstance
  -- K' := ((truncLT 0).obj X₃)⟦-1⟧ is in the heart
  haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  -- Step 4: Promote from heart to P(φ) via Z-ray argument
  have ⟨hQ_Pφ, hK_Pφ⟩ := P_phi_of_truncation_of_P_phi_cone C σ φ
    X₁.property X₂.property hT
  -- Step 5: Build the admissible triangle from the truncation triangle
  let K : (s.P φ).FullSubcategory := ⟨_, hK_Pφ⟩
  let Q : (s.P φ).FullSubcategory := ⟨_, hQ_Pφ⟩
  let e₁ : ((s.P φ).ι.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj X₃ :=
    (shiftEquiv C (1 : ℤ)).counitIso.app ((t.truncLT 0).obj X₃)
  let α : ((s.P φ).ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃ := e₁.hom ≫ (t.truncLTι 0).app X₃
  let β : X₃ ⟶ (s.P φ).ι.obj Q := (t.truncGEπ 0).app X₃
  let γ : (s.P φ).ι.obj Q ⟶ ((s.P φ).ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    (t.truncGEδLT 0).app X₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv
  exact ⟨K, Q, α, β, γ, isomorphic_distinguished _
    (t.triangleLTGE_distinguished 0 X₃) _
    (Triangle.isoMk _ _ e₁ (Iso.refl _) (Iso.refl _)
      (by dsimp [α, TStructure.triangleLTGE]; simp)
      (by dsimp [β, TStructure.triangleLTGE]; simp)
      (by dsimp [γ]; simp))⟩

variable [IsTriangulated C] in
/-- **P(φ) is abelian** (**Bridgeland's Lemma 5.2**). Each slicing slice `P(φ)` of a
stability condition is an abelian category. -/
noncomputable def StabilityCondition.P_phi_abelian
    (σ : StabilityCondition C) (φ : ℝ) :
    Abelian (σ.slicing.P φ).FullSubcategory :=
  AbelianSubcategory.abelian (σ.slicing.P φ).ι
    (σ.P_phi_hom_vanishing C φ) (σ.P_phi_admissible C φ)

/-! ### Deformed slicing predicate -/

/-- **Deformed slicing predicate** (Node 7.Q). Given a stability condition `σ`, a
perturbation `W` with `‖W - Z‖_σ < sin(πε₀)`, the deformed slicing `Q(ψ)` consists of
zero objects and objects that are W-semistable of W-phase `ψ` in some thin interval
`P((a, b))` with `b - a + 2ε₀ < 1` and the **enveloping condition** `a + ε₀ ≤ ψ ≤ b - ε₀`.
The thinness constraint ensures phase confinement (Node 7.3) is always available.
The enveloping condition (matching Bridgeland §7) ensures the object's W-phase is well
inside the interval, which is needed for heart factorization arguments in hom-vanishing
(Lemma 7.6) and interval independence (Lemma 7.5). -/
def StabilityCondition.deformedPred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (_hε₀ : 0 < ε₀) (_hε₀2 : ε₀ < 1 / 4)
    (_hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (a b : ℝ) (hab : a < b) (_ : b - a + 2 * ε₀ < 1)
    (_ : a + ε₀ ≤ ψ) (_ : ψ ≤ b - ε₀),
    (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ

/-- Zero objects are in every `Q(ψ)`. -/
lemma StabilityCondition.deformedPred_zero (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) {E : C} (hE : IsZero E) :
    σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ E :=
  Or.inl hE

/-! ### Sharp hom-vanishing for Q (Node 7.6) -/

variable [IsTriangulated C] in
/-- **Sharp hom-vanishing for Q** (**Bridgeland's Lemma 7.6**). If `E ∈ Q(ψ₁)` and
`F ∈ Q(ψ₂)` with `ψ₁ > ψ₂`, then every morphism `E → F` is zero.

**Proof outline.** Two cases:
- **Large gap** (`ψ₁ > ψ₂ + 2ε₀`): Phase confinement
  (`phase_confinement_from_stabSeminorm`) puts `E` and `F` in disjoint σ-intervals,
  so `intervalHom_eq_zero` applies (cf. `hom_eq_zero_of_wSemistable_gap`).
- **Small gap** (`ψ₁ - ψ₂ ≤ 2ε₀`): Embed both `E, F` in the abelian heart
  `P((c, c+1])` of a σ-t-structure. Factor `f` as `E ↠ im(f) ↪ F`.
  F's W-semistability (weakened to only require `K ∈ P((a,b))`, not `Q`) gives
  `wPhaseOf(W(im(f))) ≤ ψ₂`. The K₀ identity `W(E) = W(ker(f)) + W(im(f))`
  with `phase(W(E)) = ψ₁ > ψ₂` forces `phase(W(ker(f))) > ψ₁`, contradicting
  E's W-semistability.

**Remaining blockers**: Both cases require **Lemma 7.5** (interval independence)
to place E and F in a common thin interval. Additionally, the small-gap case
requires abelian heart factorization and K₀ arithmetic in the heart. -/
theorem StabilityCondition.hom_eq_zero_of_deformedPred
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E F : C} {ψ₁ ψ₂ : ℝ}
    (hE : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ₁ E)
    (hF : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ₂ F)
    (hgap : ψ₁ > ψ₂)
    (f : E ⟶ F) : f = 0 := by
  -- Dispatch IsZero cases
  rcases hE with hEZ | ⟨a₁, b₁, hab₁, hthin₁, henv₁_lo, henv₁_hi, hSS₁⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨a₂, b₂, hab₂, hthin₂, henv₂_lo, henv₂_hi, hSS₂⟩
  · exact hFZ.eq_of_tgt f 0
  -- Both nonzero: E is W-semistable on (a₁, b₁) with phase ψ₁,
  -- F is W-semistable on (a₂, b₂) with phase ψ₂.
  -- Phase confinement: E's σ-phases ∈ [ψ₁ - ε₀, ψ₁ + ε₀],
  -- F's σ-phases ∈ [ψ₂ - ε₀, ψ₂ + ε₀]
  have ⟨hE_lo, hE_hi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab₁
    hε₀ hε₀2 hthin₁ hsin hSS₁
  have ⟨hF_lo, hF_hi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab₂
    hε₀ hε₀2 hthin₂ hsin hSS₂
  -- Large gap: E and F lie in disjoint σ-intervals
  set δ := (ψ₁ - ψ₂ - 2 * ε₀) / 4 with hδ_def
  -- Note: if ψ₁ - ψ₂ ≤ 2ε₀, then δ ≤ 0. We still proceed since
  -- intervalProp_of_intrinsic_phases and intervalHom_eq_zero work
  -- with any parameters.
  -- E ∈ P((ψ₁ - ε₀ - (ψ₁-ψ₂)/2, ψ₁ + ε₀ + (ψ₁-ψ₂)/2))
  -- But we use a tighter interval: E ∈ P((ψ₂ + ε₀, ...)) is wrong.
  -- Instead, use direct computation:
  -- ψ₂ + ε₀ < ψ₁ - ε₀ is equivalent to ψ₁ - ψ₂ > 2ε₀.
  -- When this holds, the σ-intervals [ψ₂-ε₀, ψ₂+ε₀] and [ψ₁-ε₀, ψ₁+ε₀] are disjoint.
  by_cases hlargeGap : ψ₁ > ψ₂ + 2 * ε₀
  · -- Large gap: disjoint σ-intervals
    set δ' := (ψ₁ - ψ₂ - 2 * ε₀) / 4 with hδ'_def
    have hδ'_pos : 0 < δ' := by linarith
    have hEI : σ.slicing.intervalProp C (ψ₁ - ε₀ - δ') (ψ₁ + ε₀ + δ') E :=
      σ.slicing.intervalProp_of_intrinsic_phases C hSS₁.2.1
        (by linarith) (by linarith)
    have hFI : σ.slicing.intervalProp C (ψ₂ - ε₀ - δ') (ψ₂ + ε₀ + δ') F :=
      σ.slicing.intervalProp_of_intrinsic_phases C hSS₂.2.1
        (by linarith) (by linarith)
    have hdisjoint : ψ₂ + ε₀ + δ' ≤ ψ₁ - ε₀ - δ' := by
      simp only [hδ'_def]; linarith
    exact σ.slicing.intervalHom_eq_zero C hEI hFI hdisjoint f
  · -- Small gap: 0 < ψ₁ - ψ₂ ≤ 2ε₀.
    -- Proof strategy (Bridgeland Lemma 7.6):
    -- 1. Both E, F lie in a common abelian heart P((c, c+1]) (needs ε₀ < 1/4)
    -- 2. Factor f as E ↠ im(f) ↪ F in the heart
    -- 3. SES 0 → im(f) → F → coker(f) → 0 gives:
    --    F's W-semistability implies wPhaseOf(W(im(f))) ≤ ψ₂
    -- 4. SES 0 → ker(f) → E → im(f) → 0 and W(E) = W(ker) + W(im):
    --    See-saw gives wPhaseOf(W(im(f))) ≥ ψ₁ (from E's W-semistability)
    -- 5. ψ₁ ≤ wPhaseOf(W(im)) ≤ ψ₂ contradicts ψ₁ > ψ₂
    -- Blockers: heart-SES-to-triangle correspondence, P(φ) closure under
    -- subobjects/quotients in hearts, wPhaseOf see-saw lemma
    push_neg at hlargeGap
    sorry

/-! ### Extension-closed subcategories Q(> t), Q(≤ t) (Node 7.8a) -/

/-- **Q(> t)**: the predicate on objects that are zero or lie in `Q(ψ)` for some `ψ > t`.
For Q-semistable objects this captures "phase > t". For general objects, the full
subcategory should be the extension-closure, but for semistable inputs this suffices
and avoids needing Q-HN filtrations. -/
def StabilityCondition.deformedGtPred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (ψ : ℝ), ψ > t ∧
    σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ E

/-- **Q(≤ t)**: the predicate on objects that are zero or lie in `Q(ψ)` for some `ψ ≤ t`.
Dual of `deformedGtPred`. -/
def StabilityCondition.deformedLePred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨ ∃ (ψ : ℝ), ψ ≤ t ∧
    σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ E

variable [IsTriangulated C] in
/-- **Orthogonality of Q(> t) and Q(≤ t)** (**Node 7.8b**). Every morphism from a
`Q(> t)`-object to a `Q(≤ t)`-object is zero, by the sharp hom-vanishing (Node 7.6). -/
theorem StabilityCondition.hom_eq_zero_of_deformedGt_deformedLe
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E F : C} {t : ℝ}
    (hE : σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t E)
    (hF : σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t F)
    (f : E ⟶ F) : f = 0 := by
  rcases hE with hEZ | ⟨ψ₁, hψ₁, hE'⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨ψ₂, hψ₂, hF'⟩
  · exact hFZ.eq_of_tgt f 0
  exact σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hsin hE' hF'
    (by linarith) f

/-! ### Deformed slicing construction -/

variable [IsTriangulated C] in
/-- **Deformed slicing** (Node 7.Q + 7.6 + 7.7). The slicing `Q` with `Q(ψ) =
deformedPred σ W hW ε₀ ψ`. The hom-vanishing axiom is Node 7.6, the HN existence
axiom is Node 7.7, and the shift axiom requires K₀.of interaction with shift.

**Remaining sorrys:**
- `hn_exists`: HN filtrations for Q (Node 7.7, requires abelian HN theory in the heart)
- Small-gap case of `hom_vanishing` (ψ₁ - ψ₂ ≤ 2ε₀, requires heart factorization)

The `closedUnderIso` and `shift_iff` fields are complete. The `hom_vanishing` field
handles the large-gap case via phase confinement and interval disjointness. -/
def StabilityCondition.deformedSlicing (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    Slicing C where
  P := σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin
  closedUnderIso := fun φ ↦ ⟨fun {E E'} e h ↦ by
    rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
    · exact Or.inl ((Iso.isZero_iff e).mp hZ)
    · refine Or.inr ⟨a, b, hab, hthin, henv_lo, henv_hi, ?_, fun h ↦ hSS.2.1
        ((Iso.isZero_iff e).mpr h), ?_, ?_, fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
      · -- intervalProp: transport via HNFiltration.ofIso
        rcases hSS.1 with hZ' | ⟨F, hF⟩
        · exact absurd hZ' hSS.2.1
        · exact Or.inr ⟨F.ofIso C e, hF⟩
      · -- W(K₀.of C E') ≠ 0
        rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]; exact hSS.2.2.1
      · -- wPhaseOf = φ
        rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]; exact hSS.2.2.2.1
      · -- semistability: compose triangle with iso
        have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
          isomorphic_distinguished _ hT _
            (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
              (by simp) (by simp) (by simp))
        exact hSS.2.2.2.2 hT' hK hQ hKne⟩
  zero_mem ψ := σ.deformedPred_zero C W hW ε₀ hε₀ hε₀2 hsin ψ (isZero_zero C)
  shift_iff := fun φ X ↦ by
    constructor
    · -- Forward: deformedPred φ X → deformedPred (φ+1) (X⟦1⟧)
      intro h
      rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
      · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
      · -- Use interval (a+1, b+1) with α' = (a+b)/2 + 1
        refine Or.inr ⟨a + 1, b + 1, by linarith, by linarith, by linarith, by linarith,
          ?_, fun h ↦ hSS.2.1
          (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) X h), ?_,
          ?_, fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
        · -- intervalProp C (a+1) (b+1) (X⟦1⟧)
          rcases hSS.1 with hZ' | ⟨F, hF⟩
          · exact absurd hZ' hSS.2.1
          · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
              simp only [HNFiltration.shiftHN, Int.cast_one]
              constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
        · -- W(K₀.of C (X⟦1⟧)) ≠ 0
          rw [K₀.of_shift_one, map_neg]
          exact neg_ne_zero.mpr hSS.2.2.1
        · -- wPhaseOf(W(K₀.of C (X⟦1⟧))) ((a+b)/2 + 1) = φ + 1
          change wPhaseOf (W (K₀.of C (X⟦(1 : ℤ)⟧))) ((a + 1 + (b + 1)) / 2) = φ + 1
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
          rw [K₀.of_shift_one, map_neg]
          have hphase : wPhaseOf (W (K₀.of C X)) ((a + b) / 2) = φ := hSS.2.2.2.1
          have hWne : W (K₀.of C X) ≠ 0 := hSS.2.2.1
          exact (wPhaseOf_neg hWne _).trans (by linarith)
        · -- Semistability transport: shift K → X⟦1⟧ → Q by -1, compose with iso
          -- to get K⟦-1⟧ → X → Q⟦-1⟧ (dist), apply X's semistability
          have hT_sh := Triangle.shift_distinguished _ hT (-1 : ℤ)
          -- Build triangle with obj₂ = X via iso (X⟦1⟧)⟦-1⟧ ≅ X
          have h10 : (1 : ℤ) + (-1 : ℤ) = 0 := by omega
          let eX := (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) h10).app X
          let shT := (Triangle.shiftFunctor C (-1)).obj (Triangle.mk f₁ f₂ f₃)
          set T' := Triangle.mk (shT.mor₁ ≫ eX.hom) (eX.inv ≫ shT.mor₂) shT.mor₃
          have hT' : T' ∈ distTriang C :=
            isomorphic_distinguished _ hT_sh _
              (Triangle.isoMk T' shT
                (Iso.refl _) eX.symm (Iso.refl _)
                (by simp [T'])
                (by change (eX.inv ≫ shT.mor₂) ≫ 𝟙 _ = eX.symm.hom ≫ shT.mor₂
                    simp [Iso.symm])
                (by simp [T']))
          -- K⟦-1⟧ ∈ P((a,b)), Q⟦-1⟧ ∈ P((a,b))
          have hK1 : σ.slicing.intervalProp C a b (K⟦(-1 : ℤ)⟧) := by
            rcases hK with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing (-1), fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hQ1 : σ.slicing.intervalProp C a b (Q⟦(-1 : ℤ)⟧) := by
            rcases hQ with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing (-1), fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hKne1 : ¬IsZero (K⟦(-1 : ℤ)⟧) := fun h ↦
            hKne (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (-1 : ℤ)) K h)
          -- Apply X's semistability
          have hsem : wPhaseOf (W (K₀.of C (K⟦(-1 : ℤ)⟧))) ((a + b) / 2) ≤ φ :=
            hSS.2.2.2.2 hT' hK1 hQ1 hKne1
          rw [K₀.of_shift_neg_one, map_neg] at hsem
          -- hsem : wPhaseOf (-W (K₀.of C K)) ((a + b) / 2) ≤ φ
          change wPhaseOf (W (K₀.of C K)) ((a + 1 + (b + 1)) / 2) ≤ φ + 1
          rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 from by ring]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
            have key2 := wPhaseOf_add_two hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 2 = (a + b) / 2 + 1 from by ring] at key2
            linarith
    · -- Backward: deformedPred (φ+1) (X⟦1⟧) → deformedPred φ X
      intro h
      rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
      · exact Or.inl (IsZero.of_full_of_faithful_of_isZero
          (shiftFunctor C (1 : ℤ)) X hZ)
      · -- Use interval (a-1, b-1) with α' = (a+b)/2 - 1
        refine Or.inr ⟨a - 1, b - 1, by linarith, by linarith, by linarith, by linarith, ?_,
          fun h ↦ hSS.2.1 ((shiftFunctor C (1 : ℤ)).map_isZero h), ?_, ?_,
          fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
        · -- intervalProp C (a-1) (b-1) X from intervalProp C a b (X⟦1⟧)
          rcases hSS.1 with hZ' | ⟨F, hF⟩
          · exact absurd hZ' hSS.2.1
          · exact Or.inr ⟨(F.shiftHN C σ.slicing (-1)).ofIso C
              ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).app X),
              fun i ↦ by
                change a - 1 < (F.shiftHN C σ.slicing (-1)).φ i ∧
                  (F.shiftHN C σ.slicing (-1)).φ i < b - 1
                simp only [HNFiltration.shiftHN, Int.cast_neg, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
        · -- W(K₀.of C X) ≠ 0
          change W (K₀.of C X) ≠ 0
          intro h; exact hSS.2.2.1 (show W (K₀.of C (X⟦(1 : ℤ)⟧)) = 0 from by
            rw [K₀.of_shift_one, map_neg, h, neg_zero])
        · -- wPhaseOf(W(K₀.of C X)) ((a-1+b-1)/2) = φ
          change wPhaseOf (W (K₀.of C X)) ((a - 1 + (b - 1)) / 2) = φ
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
          -- hSS.2.2.2.1 : wPhaseOf (W (K₀.of C (X⟦1⟧))) ((a+b)/2) = φ + 1
          have hphase : wPhaseOf (-W (K₀.of C X)) ((a + b) / 2) = φ + 1 := by
            have := hSS.2.2.2.1
            rwa [K₀.of_shift_one, map_neg] at this
          have hWne : W (K₀.of C X) ≠ 0 := by
            intro h; apply hSS.2.2.1
            change W (K₀.of C (X⟦(1 : ℤ)⟧)) = 0
            rw [K₀.of_shift_one, map_neg, neg_eq_zero]
            exact h
          have key := wPhaseOf_neg hWne ((a + b) / 2 - 1)
          rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
          linarith
        · -- Semistability: transport via ⟦1⟧
          -- Shift triangle K → X → Q by 1 to get K⟦1⟧ → X⟦1⟧ → Q⟦1⟧
          have hT' := Triangle.shift_distinguished _ hT (1 : ℤ)
          -- K⟦1⟧ ∈ P((a,b)), Q⟦1⟧ ∈ P((a,b))
          have hK1 : σ.slicing.intervalProp C a b (K⟦(1 : ℤ)⟧) := by
            rcases hK with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hQ1 : σ.slicing.intervalProp C a b (Q⟦(1 : ℤ)⟧) := by
            rcases hQ with hZ | ⟨F, hF⟩
            · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
            · exact Or.inr ⟨F.shiftHN C σ.slicing 1, fun i ↦ by
                simp only [HNFiltration.shiftHN, Int.cast_one]
                constructor <;> [linarith [(hF i).1]; linarith [(hF i).2]]⟩
          have hKne1 : ¬IsZero (K⟦(1 : ℤ)⟧) := fun h ↦
            hKne (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) K h)
          -- Apply X⟦1⟧'s semistability
          have hsem : wPhaseOf (W (K₀.of C (K⟦(1 : ℤ)⟧))) ((a + b) / 2) ≤ φ + 1 :=
            hSS.2.2.2.2 hT' hK1 hQ1 hKne1
          rw [K₀.of_shift_one, map_neg] at hsem
          -- hsem : wPhaseOf (-W (K₀.of C K)) ((a + b) / 2) ≤ φ + 1
          change wPhaseOf (W (K₀.of C K)) ((a - 1 + (b - 1)) / 2) ≤ φ
          rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 from by ring]
          by_cases hWK : W (K₀.of C K) = 0
          · simp only [hWK, neg_zero, wPhaseOf_zero] at hsem ⊢; linarith
          · have key := wPhaseOf_neg hWK ((a + b) / 2 - 1)
            rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 from by ring] at key
            linarith
  hom_vanishing ψ₁ ψ₂ A B hlt hA hB f :=
    σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hsin hA hB hlt f
  hn_exists := by
    -- Bridgeland Nodes 7.7-7.9: HN filtrations for the deformed slicing Q.
    -- Proof strategy:
    -- For each nonzero E, decompose via σ's t-structure Q(>t)/Q(≤t):
    -- 1. Use σ-HN filtration of E to get σ-semistable factors
    -- 2. Each factor gets a Q-HN filtration via W-HN in P(φ) (sorry 4)
    -- 3. Refine the σ-tower by inserting Q-HN subtowers for each factor
    -- 4. The resulting tower is a Q-HN filtration of E
    -- Alternatively (Bridgeland §7.7): quasi-abelian HN in thin categories
    -- using well-founded recursion on subobject lattice, with Lemma 7.6
    -- providing hom-vanishing. This is the main blocker (~350-600 lines).
    -- Requires: sigma_semistable_intervalProp (sorry 4), hom-vanishing
    -- (sorry 2), interval independence (sorry 1).
    sorry

variable [IsTriangulated C] in
/-- **W-compatibility of the deformed slicing.** For every nonzero Q-semistable object `E`
of Q-phase `ψ`, the central charge `W([E])` lies on the ray `ℝ₊ · exp(iπψ)`. This
follows directly from the `Semistable` definition, which stores
`wPhaseOf(W([E]), α) = ψ`. -/
theorem StabilityCondition.deformedSlicing_compat
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) (E : C)
    (hQ : (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hsin).P ψ E)
    (hE : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      W (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  -- hQ : deformedPred, so either IsZero or ∃ a b hab hthin, Semistable
  rcases hQ with hEZ | ⟨a, b, hab, _, _, _, hSS⟩
  · exact absurd hEZ hE
  · exact ⟨‖W (K₀.of C E)‖, norm_pos_iff.mpr hSS.2.2.1, hSS.polar⟩

/-! ### Note on Z-ray lemma

The Z-ray argument at the AGGREGATE level (Im(Z(K)·rot) + Im(Z(Q)·rot) = 0 with
each ≤ 0 resp. ≥ 0) does NOT force each to vanish. A counterexample: K with one factor
of phase φ-ε (contributing negative Im) and Q with one factor of phase φ+ε (contributing
positive Im that exactly cancels). The aggregate sums satisfy the sign constraints and
sum to zero without each being zero.

The correct argument works at the INDIVIDUAL FACTOR level inside P(φ), using the abelian
structure of P(φ) rather than K₀ additivity on K and Q separately. This is why
`sigma_semistable_intervalProp` constructs the Q-HN filtration inside P(φ)
using the restricted stability function, not via the Z-ray approach. -/

/-! ### K₀ additivity for SES in abelian subcategories

For a short exact sequence `0 → A → B → C → 0` in the abelian subcategory `P(φ)` of a
stability condition, the K₀ relation `[B] = [A] + [C]` holds in `K₀(C)`. The proof uses
the admissibility of `P(φ)` (from `P_phi_admissible`) and the fact that the kernel of a
monomorphism is zero: if `f : A → B` is mono and the admissibility kernel `K` satisfies
`K → A` mono and `K → A → B = 0`, then `K = 0`, which makes the admissibility triangle
degenerate, giving `T.obj₃ ≅ ι(Q)` and hence `[B] = [A] + [Q]`. -/

variable [IsTriangulated C] in
/-- **K₀ additivity for SES in P(φ)**. For any short exact sequence in the abelian
category `P(φ)`, the K₀ relation `[B] = [A] + [C]` holds in `K₀(C)`. This is the key
bridge between the abelian HN theory in `P(φ)` and the triangulated K₀ group. -/
theorem K0_of_shortExact_P_phi (σ : StabilityCondition C) (φ : ℝ)
    (S : @ShortComplex (σ.slicing.P φ).FullSubcategory _
      (@Preadditive.preadditiveHasZeroMorphisms _ _ (σ.P_phi_abelian C φ).toPreadditive))
    (hS : S.ShortExact) :
    K₀.of C ((σ.slicing.P φ).ι.obj S.X₂) =
      K₀.of C ((σ.slicing.P φ).ι.obj S.X₁) +
      K₀.of C ((σ.slicing.P φ).ι.obj S.X₃) := by
  letI hab := σ.P_phi_abelian C φ
  haveI : IsNormalEpiCategory (σ.slicing.P φ).FullSubcategory := hab.toIsNormalEpiCategory
  set ι := (σ.slicing.P φ).ι
  -- Step 1: ι.map S.f extends to a distinguished triangle
  obtain ⟨cone, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map S.f)
  have hK0_T := K₀.of_triangle C (Triangle.mk (ι.map S.f) f₂ f₃) hT
  -- Step 2: Admissibility gives K, Q ∈ P(φ) and decomposition of cone
  have hadm : AbelianSubcategory.admissibleMorphism ι S.f := by
    rw [σ.P_phi_admissible C φ]; trivial
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hadm f₂ f₃ hT
  have hK0_T' := K₀.of_triangle C (Triangle.mk α β γ) hT'
  have hK0_shift : K₀.of C ((ι.obj K)⟦(1 : ℤ)⟧) = -K₀.of C (ι.obj K) :=
    K₀.of_shift_one C (ι.obj K)
  -- Step 3: K = 0 (ιK ≫ S.f = 0 with S.f mono and ιK mono gives K zero)
  have hιK := AbelianSubcategory.ιK_mor₁ hT α
  haveI := hS.mono_f
  have hιK_eq_zero : AbelianSubcategory.ιK f₃ α = 0 :=
    (cancel_mono S.f).mp (by rw [hιK, zero_comp])
  have hK_zero : IsZero K := by
    have hιK_mono := AbelianSubcategory.mono_ιK
      (σ.P_phi_hom_vanishing C φ) hT hT'
    rw [hιK_eq_zero] at hιK_mono
    rw [IsZero.iff_id_eq_zero]
    exact (cancel_mono (0 : K ⟶ S.X₁)).mp (by simp)
  have hιK_isZero : IsZero (ι.obj K) := ι.map_isZero hK_zero
  have hK0_K : K₀.of C (ι.obj K) = 0 := K₀.of_isZero C hιK_isZero
  -- Step 4: Q ≅ S.X₃ (both are cokernels of S.f, so isomorphic by universality)
  have hπQ_coker := AbelianSubcategory.isColimitCokernelCofork
    (σ.P_phi_hom_vanishing C φ) hT hT'
  have hSg_coker := hS.gIsCokernel
  have iso_Q_X₃ : Q ≅ S.X₃ := hπQ_coker.coconePointUniqueUpToIso hSg_coker
  have hK0_Q : K₀.of C (ι.obj Q) = K₀.of C (ι.obj S.X₃) :=
    K₀.of_iso C (ι.mapIso iso_Q_X₃)
  -- Combine: [ι(B)] = [ι(A)] + [cone], [cone] = -[ι(K)] + [ι(Q)] = [ι(C)]
  have hcone : K₀.of C cone = K₀.of C (ι.obj S.X₃) := by
    have h := hK0_T'; simp only [Triangle.mk] at h
    rw [hK0_shift, hK0_K, neg_zero, zero_add, hK0_Q] at h
    exact h
  simp only [Triangle.mk] at hK0_T
  rw [hK0_T, hcone]

/-! ### Reverse phase confinement: σ-semistable → Q-interval -/

variable [IsTriangulated C] in
/-- **Reverse phase confinement**. If `E` is σ-semistable of phase `φ` and
`‖W - Z‖_σ < sin(πε₀)`, then `E` lies in the Q-interval `(φ - ε₀ - δ, φ + ε₀ + δ)`
for any `δ > 0`.

This replaces the incorrect statement `sigma_semistable_is_deformedPred` which claimed
σ-semistable implies Q-semistable. That is **false**: a σ-semistable object `E` can
decompose into W-semistable factors with different W-phases (e.g., `E = S₁ ⊕ S₂` with
`S₁, S₂` σ-stable of the same phase but different W-phases), so `E` need not be
Q-semistable. The correct statement is that `E` lies in a Q-interval of half-width
`ε₀ + δ` centered at `φ`.

The proof constructs a Q-HN filtration for `E` by decomposing it in the abelian
category `P(φ)` using the W-stability function restricted to `P(φ)`. Each W-HN
factor in `P(φ)` has W-phase within `ε₀` of `φ`, giving the desired interval bound.
-/
theorem sigma_semistable_intervalProp
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    {δ : ℝ} (hδ : 0 < δ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hsin).intervalProp C
      (φ - ε₀ - δ) (φ + ε₀ + δ) E := by
  sorry

/-! ### Deformation theorem (Theorem 7.1) -/

variable [IsTriangulated C] in
/-- **Bridgeland's Theorem 7.1** (deformation of stability conditions). Given a
stability condition `σ = (Z, P)` on a triangulated category `D` and a group
homomorphism `W : K₀(D) → ℂ` with `‖W - Z‖_σ < sin(πε₀)` (where `ε₀` comes from
the local finiteness of `σ`), there exists a locally-finite stability condition
`τ = (W, Q)` with `d(P, Q) ≤ ε₀`.

The proof constructs the deformed slicing `Q` via `deformedSlicing`, then verifies:
1. **Hom-vanishing** (Lemma 7.6): `hom_eq_zero_of_deformedPred`
2. **HN filtrations** (Lemma 7.7 + Nodes 7.8–7.9): well-founded recursion in thin
   quasi-abelian categories, assembled via t-structures `Q(> t)`
3. **Compatibility**: `deformedSlicing_compat`
4. **Local finiteness**: inherited from `σ` via phase confinement (Node 7.3)
5. **Distance bound**: `d(P, Q) ≤ ε₀` by phase confinement (Node 7.3)

The hypothesis `hε₀_lf` ensures `ε₀` is small enough relative to `σ`'s local finiteness
parameter, following Bridgeland's condition that intervals of half-width `ε₀ + δ` have
finite length. -/
theorem bridgeland_7_1 (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hε₀_lf : ∃ δ : ℝ, 0 < δ ∧ ∀ t (E : C),
      σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ)) E →
      Finite (Subobject E)) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε₀ := by
  refine ⟨⟨σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hsin, W,
    σ.deformedSlicing_compat C W hW ε₀ hε₀ hε₀2 hsin, ?_⟩, rfl, ?_⟩
  · -- Local finiteness: inherited from σ via phase confinement
    obtain ⟨δ, hδ, hlf_σ⟩ := hε₀_lf
    refine ⟨δ / 2, by linarith, fun t E hE_int ↦ ?_⟩
    -- Show E ∈ σ.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ))
    have hE_sigma : σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ)) E := by
      rcases hE_int with hZ | ⟨F, hF⟩
      · exact Or.inl hZ
      · -- F : HNFiltration for deformedPred, with Q-phases in (t - δ/2, t + δ/2)
        -- Each factor is in σ's interval by phase confinement
        apply intervalProp_of_postnikovTower C σ.slicing F.toPostnikovTower
        intro i
        have hsem := F.semistable i
        change σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin (F.φ i) _ at hsem
        rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
        · exact Or.inl hZ_i
        · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
            hε₀ hε₀2 hthin_i hsin hSS_i
          exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
            (by have := (hF i).1; linarith) (by have := (hF i).2; linarith)
    exact hlf_σ t E hE_sigma
  · -- Distance bound: d(P, Q) ≤ ε₀ by phase confinement
    set Q := σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hsin
    -- Forward: Q-HN factors → phase confinement → σ-intervalProp
    have forward : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        σ.slicing.intervalProp C
          (Q.phiMinus C E hE - ε₀ - δ) (Q.phiPlus C E hE + ε₀ + δ) E := by
      intro E hE δ hδ
      obtain ⟨G, hnG, hfirstG, hlastG⟩ := HNFiltration.exists_both_nonzero C Q hE
      apply intervalProp_of_postnikovTower C σ.slicing G.toPostnikovTower
      intro i
      by_cases hGi : IsZero (G.toPostnikovTower.factor i)
      · exact Or.inl hGi
      · have hsem := G.semistable i
        change σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin (G.φ i) _ at hsem
        rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
        · exact absurd hZ_i hGi
        · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
            hε₀ hε₀2 hthin_i hsin hSS_i
          have hGi_le : G.φ i ≤ Q.phiPlus C E hE := by
            rw [Q.phiPlus_eq C E hE G hnG hfirstG]
            exact G.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
          have hGi_ge : Q.phiMinus C E hE ≤ G.φ i := by
            rw [Q.phiMinus_eq C E hE G hnG hlastG]
            exact G.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
          exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
            (by linarith) (by linarith)
    -- Reverse: σ-HN factors → reverse phase confinement → Q-intervalProp
    have reverse : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
        Q.intervalProp C
          (σ.slicing.phiMinus C E hE - ε₀ - δ)
          (σ.slicing.phiPlus C E hE + ε₀ + δ) E := by
      intro E hE δ hδ
      obtain ⟨F, hnF, hfirstF, hlastF⟩ :=
        HNFiltration.exists_both_nonzero C σ.slicing hE
      apply intervalProp_of_postnikovTower C Q F.toPostnikovTower
      intro i
      by_cases hFi : IsZero (F.toPostnikovTower.factor i)
      · exact Or.inl hFi
      · have hFi_le : F.φ i ≤ σ.slicing.phiPlus C E hE := by
          rw [σ.slicing.phiPlus_eq C E hE F hnF hfirstF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        have hFi_ge : σ.slicing.phiMinus C E hE ≤ F.φ i := by
          rw [σ.slicing.phiMinus_eq C E hE F hnF hlastF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        -- Factor i is σ-semistable of phase F.φ i. By reverse phase confinement,
        -- it lies in Q-interval (F.φ i - ε₀ - δ, F.φ i + ε₀ + δ).
        have hQint := sigma_semistable_intervalProp C σ W hW
          hε₀ hε₀2 hsin (F.semistable i) hFi hδ
        -- Widen to (phiMinus - ε₀ - δ, phiPlus + ε₀ + δ) using monotonicity
        exact Q.intervalProp_mono C (by linarith) (by linarith) hQint
    -- Combine: |σ.phiPlus - Q.phiPlus| ≤ ε₀ and |σ.phiMinus - Q.phiMinus| ≤ ε₀
    apply slicingDist_le_of_phase_bounds
    · -- |σ.phiPlus(E) - Q.phiPlus(E)| ≤ ε₀
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiPlus(E) ≤ σ.phiPlus(E) + ε₀
        by_contra h; push_neg at h
        have := Q.phiPlus_lt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < -(σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE) - ε₀))
        linarith
      · -- σ.phiPlus(E) ≤ Q.phiPlus(E) + ε₀
        by_contra h; push_neg at h
        have := σ.slicing.phiPlus_lt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiPlus C E hE -
            Q.phiPlus C E hE - ε₀))
        linarith
    · -- |σ.phiMinus(E) - Q.phiMinus(E)| ≤ ε₀
      intro E hE; rw [abs_le]; constructor
      · -- Q.phiMinus(E) - ε₀ ≤ σ.phiMinus(E)
        by_contra h; push_neg at h
        have := σ.slicing.phiMinus_gt_of_intervalProp C hE
          (forward E hE _ (by linarith : (0 : ℝ) < -(σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE) - ε₀))
        linarith
      · -- σ.phiMinus(E) ≤ Q.phiMinus(E) + ε₀
        by_contra h; push_neg at h
        have := Q.phiMinus_gt_of_intervalProp C hE
          (reverse E hE _ (by linarith : (0 : ℝ) < σ.slicing.phiMinus C E hE -
            Q.phiMinus C E hE - ε₀))
        linarith

end CategoryTheory.Triangulated
