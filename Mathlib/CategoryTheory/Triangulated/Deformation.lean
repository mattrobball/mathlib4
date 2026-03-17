/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.StabilityCondition
import Mathlib.CategoryTheory.Triangulated.StabilityFunction
import Mathlib.CategoryTheory.Triangulated.IntervalCategory
import Mathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian

set_option linter.style.longFile 3500

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
  [IsTriangulated C]

/-! ### Node 7.0: ε₀ extraction from local finiteness -/

/-- **Node 7.0: Extraction of ε₀**. Given a stability condition `σ`, extract a positive
real `ε₀ < 1/8` such that for all `t`, every object in `P((t - 4ε₀, t + 4ε₀))` has
finite length. The width `8ε₀` is chosen to fit inside the local finiteness
parameter `2η`. -/
theorem StabilityCondition.exists_epsilon0 (σ : StabilityCondition C) :
    ∃ ε₀ : ℝ, ∃ hε₀ : 0 < ε₀, ∃ hε₀' : ε₀ < 1 / 8,
      ∀ t : ℝ,
        let a := t - 4 * ε₀
        let b := t + 4 * ε₀
        letI : Fact (a < b) := ⟨by
          dsimp [a, b]
          linarith⟩
        letI : Fact (b - a ≤ 1) := ⟨by
          dsimp [a, b]
          linarith⟩
        ∀ (E : σ.slicing.IntervalCat C a b),
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E := by
  obtain ⟨η, hη, hη', hlf⟩ := σ.locallyFinite.intervalFinite
  refine ⟨η / 4, by positivity, by linarith, ?_⟩
  intro t
  dsimp
  intro E
  let a : ℝ := t - 4 * (η / 4)
  let b : ℝ := t + 4 * (η / 4)
  have ha : a = t - η := by
    dsimp [a]
    ring
  have hb : b = t + η := by
    dsimp [b]
    ring
  letI : Fact (a < b) := ⟨by
    dsimp [a, b]
    linarith [hη]⟩
  letI : Fact (b - a ≤ 1) := ⟨by
    dsimp [a, b]
    linarith [hη']⟩
  suffices
      ∀ {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)],
        a = t - η → b = t + η →
        ∀ E : σ.slicing.IntervalCat C a b,
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E by
    simpa [a, b] using this (a := a) (b := b) ha hb E
  intro a b _ _ ha hb E
  subst a b
  simpa using hlf t E

/-- Variant of ε₀ extraction providing 2ε₀-intervals for the sector bound. -/
theorem StabilityCondition.exists_epsilon0_sector (σ : StabilityCondition C) :
    ∃ ε₀ : ℝ, ∃ hε₀ : 0 < ε₀, ∃ hε₀' : ε₀ < 1 / 4,
      ∀ t : ℝ,
        let a := t - 2 * ε₀
        let b := t + 2 * ε₀
        letI : Fact (a < b) := ⟨by
          dsimp [a, b]
          linarith⟩
        letI : Fact (b - a ≤ 1) := ⟨by
          dsimp [a, b]
          linarith⟩
        ∀ (E : σ.slicing.IntervalCat C a b),
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E := by
  obtain ⟨η, hη, hη', hlf⟩ := σ.locallyFinite.intervalFinite
  refine ⟨η / 2, by positivity, by linarith, ?_⟩
  intro t
  dsimp
  intro E
  let a : ℝ := t - 2 * (η / 2)
  let b : ℝ := t + 2 * (η / 2)
  have ha : a = t - η := by
    dsimp [a]
    ring
  have hb : b = t + η := by
    dsimp [b]
    ring
  letI : Fact (a < b) := ⟨by
    dsimp [a, b]
    linarith [hη]⟩
  letI : Fact (b - a ≤ 1) := ⟨by
    dsimp [a, b]
    linarith [hη']⟩
  suffices
      ∀ {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)],
        a = t - η → b = t + η →
        ∀ E : σ.slicing.IntervalCat C a b,
          IsStrictArtinianObject E ∧ IsStrictNoetherianObject E by
    simpa [a, b] using this (a := a) (b := b) ha hb E
  intro a b _ _ ha hb E
  subst a b
  simpa using hlf t E

private def SectorFiniteLength (σ : StabilityCondition C) (ε₀ : ℝ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) : Prop :=
  ∀ t : ℝ,
    let a := t - 2 * ε₀
    let b := t + 2 * ε₀
    letI : Fact (a < b) := ⟨by
      dsimp [a, b]
      linarith [hε₀]⟩
    letI : Fact (b - a ≤ 1) := ⟨by
      dsimp [a, b]
      linarith [hε₀2]⟩
    ∀ E : σ.slicing.IntervalCat C a b,
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E

/-- The wide local-finiteness input used in Bridgeland's p.24 Nodes 7.8–7.9: every interval of
radius `4 ε₀` has strict finite length. This is the witness needed to apply Lemma 7.7 in the
windows `P((t - 3 ε₀, t + 5 ε₀))` and `P((t - 3 ε₀, t + 5 ε₀ + δ))`. -/
private def WideSectorFiniteLength (σ : StabilityCondition C) (ε₀ : ℝ)
    (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8) : Prop :=
  ∀ t : ℝ,
    let a := t - 4 * ε₀
    let b := t + 4 * ε₀
    letI : Fact (a < b) := ⟨by
      dsimp [a, b]
      linarith [hε₀]⟩
    letI : Fact (b - a ≤ 1) := ⟨by
      dsimp [a, b]
      linarith [hε₀8]⟩
    ∀ E : σ.slicing.IntervalCat C a b,
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E

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

/-- **Dual strict phase see-saw**: if `w = w₁ + w₂` with `wPhaseOf(w, α) = ψ`,
`ψ < wPhaseOf(w₁, α)` and both summands lie in the same branch window
`(ψ - 1, ψ + 1)`, then the other nonzero summand has phase `< ψ`.

This is the quotient-side form used when a strict subobject destabilizes an object:
the complementary strict quotient must have strictly smaller phase. -/
theorem wPhaseOf_seesaw_dual {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : wPhaseOf w α = ψ)
    (hw₁_gt : ψ < wPhaseOf w₁ α)
    (hw₁_ne : w₁ ≠ 0)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w₂ α < ψ := by
  by_contra h
  push_neg at h
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im = 0 := im_eq_zero_of_wPhaseOf_eq hψ
  have him_w₁ : 0 < (w₁ * rot).im := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_pos (norm_pos_iff.mpr hw₁_ne)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos, hw₁_gt])
        (by nlinarith [Real.pi_pos, hw₁_range.2]))
  have him_w₂ : 0 ≤ (w₂ * rot).im := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by push_cast; ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonneg (norm_nonneg w₂)
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.2]))
  have hsum_im : (w * rot).im = (w₁ * rot).im + (w₂ * rot).im := by
    rw [← hsum, add_mul, Complex.add_im]
  linarith

theorem wPhaseOf_lt_of_add_le_lt {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioc (ψ - 1) ψ)
    (hw₂_lt : wPhaseOf w₂ α < ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw_range : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w α < ψ := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w₁ : (w₁ * rot).im ≤ 0 := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w₁)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw₁_range.2])
        (by nlinarith [Real.pi_pos, hw₁_range.1]))
  have him_w₂ : (w₂ * rot).im < 0 := by
    have hw₂_compat := wPhaseOf_compat w₂ α
    rw [hw₂_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₂ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₂ α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hw₂_lt])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  have him_w : (w * rot).im < 0 := by
    rw [← hsum, add_mul, Complex.add_im]
    linarith
  exact wPhaseOf_lt_of_im_neg him_w hw_range

/-- If `w = w₁ + w₂`, the total phase is at most `ψ`, and one summand has phase strictly
above `ψ`, then the other summand has phase strictly below `ψ`. This is the one-sided
source-envelope variant of the phase seesaw used in the faithful Lemma 7.5 argument. -/
theorem wPhaseOf_lt_of_add_le_gt {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hw_le : wPhaseOf w α ≤ ψ)
    (hw_range : wPhaseOf w α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₁_gt : ψ < wPhaseOf w₁ α)
    (hw₁_ne : w₁ ≠ 0)
    (hw₁_range : wPhaseOf w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₂_range : wPhaseOf w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    wPhaseOf w₂ α < ψ := by
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have him_w : (w * rot).im ≤ 0 := by
    have hw_compat := wPhaseOf_compat w α
    rw [hw_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw_le])
        (by nlinarith [Real.pi_pos, hw_range.1]))
  have him_w₁ : 0 < (w₁ * rot).im := by
    have hw₁_compat := wPhaseOf_compat w₁ α
    rw [hw₁_compat, mul_assoc, ← Complex.exp_add]
    have harg : ↑(Real.pi * wPhaseOf w₁ α) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
        ↑(Real.pi * (wPhaseOf w₁ α - ψ)) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    exact mul_pos (norm_pos_iff.mpr hw₁_ne)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos, hw₁_gt])
        (by nlinarith [Real.pi_pos, hw₁_range.2]))
  have him_w₂ : (w₂ * rot).im < 0 := by
    rw [← hsum, add_mul, Complex.add_im] at him_w
    linarith
  exact wPhaseOf_lt_of_im_neg him_w₂ hw₂_range

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

set_option maxHeartbeats 800000 in
variable [IsTriangulated C] in
/-- A nonzero strict quotient of a `W`-semistable interval object has `W`-phase at least
that of the middle term. This is the quotient-side semistability inequality needed for the
thin-interval HN recursion. -/
theorem SkewedStabilityFunction.phase_le_of_strictQuotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : σ.slicing.IntervalCat C a b} {ψ ε₀ : ℝ}
    (hX : ssf.Semistable C X.obj ψ)
    (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀)
    (p : X ⟶ Y) (hp : IsStrictEpi p)
    (hY : ¬IsZero Y.obj) :
    ψ ≤ wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α := by
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let t := (σ.slicing.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := σ.slicing) a b (Fact.out : b - a ≤ 1)
  have hEpi : Epi ((S.map FL).g) := by
    simpa [S, FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) p hp
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S] using (kernelIsKernel p)
  have hKer :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExact : (S.map FL).Exact := ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
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
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_gt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hX.1 hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_lt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hX.1 hW_ne hperturb_lt
  by_cases hKz : IsZero (kernel p).obj
  · have hKz' : IsZero (kernel p) :=
      Slicing.IntervalCat.isZero_of_obj_isZero (C := C) (s := σ.slicing) (a := a) (b := b) hKz
    have hkernel_zero : kernel.ι p = 0 := zero_of_source_iso_zero _ hKz'.isoZero
    haveI : Mono p := Preadditive.mono_of_kernel_zero hkernel_zero
    haveI : IsIso p := IsStrictEpi.isIso hp
    let eC : X.obj ≅ Y.obj := ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (asIso p))
    rw [← hX.2.2.2.1, ← K₀.of_iso C eC]
  · have hK : ¬IsZero (kernel p).obj := hKz
    obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
      (C := C) (s := σ.slicing) (a := a) (b := b) hL
    have hK_le : wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ≤ ψ :=
      hX.2.2.2.2 hT (kernel p).property Y.property hK
    have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hK ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) (kernel p).property hW_ne hperturb_gt
    have hY_ne : ssf.W (K₀.of C Y.obj) ≠ 0 := hW_interval Y.property hY
    have hY_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) Y.property hW_ne hperturb_gt
    have hY_hi : wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α < b + ε₀ :=
      wPhaseOf_lt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.2])) Y.property hW_ne hperturb_lt
    have hadd :
        ssf.W (K₀.of C X.obj) =
          ssf.W (K₀.of C (kernel p).obj) + ssf.W (K₀.of C Y.obj) := by
      simpa [S, map_add] using
        congrArg ssf.W (K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT)
    exact wPhaseOf_seesaw
      hadd.symm
      hX.2.2.2.1
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        hK_le⟩
      hY_ne
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        by
          have hψ_up : b + ε₀ < ψ + 1 := by
            have hmid : b + ε₀ < a - ε₀ + 1 := by linarith
            linarith
          linarith⟩

set_option maxHeartbeats 800000 in
variable [IsTriangulated C] in
/-- A nonzero quotient term in a distinguished triangle of a `W`-semistable interval object
has `W`-phase at least that of the middle term, provided both outer terms remain in the same
thin interval. This is the triangle-form quotient inequality used when the quotient is
produced in an ambient heart rather than as an explicit strict quotient in the interval
category itself. -/
theorem SkewedStabilityFunction.phase_le_of_triangle_quotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    {X K Y : C} {f₁ : K ⟶ X} {f₂ : X ⟶ Y} {f₃ : Y ⟶ K⟦(1 : ℤ)⟧} {ψ ε₀ : ℝ}
    (hX : ssf.Semistable C X ψ)
    (hε₀ : 0 < ε₀) (hthin : b - a + 2 * ε₀ < 1)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hperturb : ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        φ - ε₀ < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < φ + ε₀)
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (hKI : σ.slicing.intervalProp C a b K)
    (hYI : σ.slicing.intervalProp C a b Y)
    (hY : ¬IsZero Y) :
    ψ ≤ wPhaseOf (ssf.W (K₀.of C Y)) ssf.α := by
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
  have hψ_lo : a - ε₀ < ψ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_gt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.1])) hX.1 hW_ne hperturb_gt
  have hψ_hi : ψ < b + ε₀ := by
    rw [← hX.2.2.2.1]
    exact wPhaseOf_lt_of_intervalProp C σ hX.2.1 ssf.W
      (le_of_lt (by linarith [ssf.hα_mem.2])) hX.1 hW_ne hperturb_lt
  by_cases hKz : IsZero K
  · haveI : IsIso f₂ :=
      (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f₁ f₂ f₃) hT).mp hKz
    let eC : X ≅ Y := asIso f₂
    rw [← hX.2.2.2.1, ← K₀.of_iso C eC]
  · have hK_le : wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤ ψ :=
      hX.2.2.2.2 hT hKI hYI hKz
    have hK_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C K)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hKz ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) hKI hW_ne hperturb_gt
    have hY_ne : ssf.W (K₀.of C Y) ≠ 0 := hW_interval hYI hY
    have hY_lo : a - ε₀ < wPhaseOf (ssf.W (K₀.of C Y)) ssf.α :=
      wPhaseOf_gt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.1])) hYI hW_ne hperturb_gt
    have hY_hi : wPhaseOf (ssf.W (K₀.of C Y)) ssf.α < b + ε₀ :=
      wPhaseOf_lt_of_intervalProp C σ hY ssf.W
        (le_of_lt (by linarith [ssf.hα_mem.2])) hYI hW_ne hperturb_lt
    have hadd :
        ssf.W (K₀.of C X) =
          ssf.W (K₀.of C K) + ssf.W (K₀.of C Y) := by
      simpa [map_add] using
        congrArg ssf.W (K₀.of_triangle C (Triangle.mk f₁ f₂ f₃) hT)
    exact wPhaseOf_seesaw
      hadd.symm
      hX.2.2.2.1
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        hK_le⟩
      hY_ne
      ⟨by
          have : ψ - 1 < a - ε₀ := by
            have hmid : b + ε₀ - 1 < a - ε₀ := by linarith
            linarith
          linarith,
        by
          have : b + ε₀ < ψ + 1 := by
            have hmid : b + ε₀ < a - ε₀ + 1 := by linarith
            linarith
          linarith⟩

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

private theorem gtProp_of_wSemistable_phase_gt
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a b : ℝ} (hab : a < b)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {ψ t : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ)
    (hgt : t < ψ - ε₀) :
    σ.slicing.gtProp C t E := by
  have hE : ¬IsZero E := hSS.2.1
  have hconf := phase_confinement_from_stabSeminorm
    (C := C) (σ := σ) (W := W) (hW := hW) hab hε₀ hε₀2 hthin hsin hSS
  exact σ.slicing.gtProp_of_phiMinus_gt C hE (by linarith [hconf.1])

private theorem ltProp_of_wSemistable_phase_lt
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a b : ℝ} (hab : a < b)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {ψ t : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ)
    (hlt : ψ + ε₀ < t) :
    σ.slicing.ltProp C t E := by
  have hE : ¬IsZero E := hSS.2.1
  have hconf := phase_confinement_from_stabSeminorm
    (C := C) (σ := σ) (W := W) (hW := hW) hab hε₀ hε₀2 hthin hsin hSS
  exact σ.slicing.ltProp_of_phiPlus_lt C hE (by linarith [hconf.2])

private theorem wPhaseOf_eq_of_semistable_of_target_envelope
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a₁ b₁ : ℝ} (hab₁ : a₁ < b₁)
    {ψ : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    {a₂ b₂ ε₀ : ℝ} (hε₀ : 0 < ε₀) (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1) :
    wPhaseOf (W (K₀.of C E)) ((a₂ + b₂) / 2) = ψ := by
  have hbranch :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) ∈
        Set.Ioc (((a₂ + b₂) / 2) - 1) (((a₂ + b₂) / 2) + 1) := by
    have hpsi_branch : ψ ∈ Set.Ioc (((a₂ + b₂) / 2) - 1) (((a₂ + b₂) / 2) + 1) := by
      constructor
      · have hlo : ((a₂ + b₂) / 2) - 1 < a₂ + ε₀ := by
          by_contra h
          push_neg at h
          have hwidth : b₂ - a₂ < 1 - 2 * ε₀ := by
            linarith
          nlinarith
        exact lt_of_lt_of_le hlo henv₂_lo
      · have hhi : b₂ - ε₀ ≤ ((a₂ + b₂) / 2) + 1 := by
          by_contra h
          push_neg at h
          have hwidth : b₂ - a₂ < 1 - 2 * ε₀ := by
            linarith
          nlinarith
        exact le_trans henv₂_hi hhi
    have hwphase_eq :
        wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) = ψ := by
      simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1
    simpa [hwphase_eq] using hpsi_branch
  have hEq :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) =
        wPhaseOf (W (K₀.of C E)) ((a₂ + b₂) / 2) :=
    wPhaseOf_indep hSS.2.2.1 _ _ hbranch
  calc
    wPhaseOf (W (K₀.of C E)) ((a₂ + b₂) / 2)
        = wPhaseOf (W (K₀.of C E)) ((a₁ + b₁) / 2) := hEq.symm
    _ = ψ := by
      simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1

private theorem semistable_of_target_envelope_triangleTest
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {E : C} {a₁ b₁ : ℝ} (hab₁ : a₁ < b₁)
    {ψ : ℝ}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    {a₂ b₂ : ℝ} (hab₂ : a₂ < b₂) (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
    (htri : ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ E⦄ ⦃f₂ : E ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
      Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
      σ.slicing.intervalProp C a₂ b₂ K → σ.slicing.intervalProp C a₂ b₂ Q →
      ¬IsZero K →
      wPhaseOf (W (K₀.of C K)) ((a₂ + b₂) / 2) ≤ ψ) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  refine ⟨hI₂, hSS.2.1, hSS.2.2.1, ?_, htri⟩
  exact wPhaseOf_eq_of_semistable_of_target_envelope
    (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hSS hε₀ henv₂_lo henv₂_hi hthin₂

private theorem stabSeminorm_lt_cos_of_hsin_hthin
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    {a b ε₀ : ℝ} (hab : a < b) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.cos (Real.pi * (b - a) / 2)) := by
  have hsin_lt_cos : Real.sin (Real.pi * ε₀) <
      Real.cos (Real.pi * (b - a) / 2) := by
    rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    · nlinarith [Real.pi_pos, hab]
    · nlinarith [Real.pi_pos, hthin]
    · nlinarith [Real.pi_pos, hε₀2]
  have hcos_pos : 0 < Real.cos (Real.pi * (b - a) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos, hab]
    · nlinarith [Real.pi_pos, hthin, hε₀]
  exact lt_trans hsin ((ENNReal.ofReal_lt_ofReal_iff hcos_pos).mpr hsin_lt_cos)

private theorem wPhaseOf_eq_of_intervalProp_upper_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b₁ b₂ ε₀ : ℝ} (hab₁ : a < b₁) (hb : b₁ ≤ b₂)
    {E : C} (hI : σ.slicing.intervalProp C a b₁ E) (hEne : ¬IsZero E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin₂ : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) =
      wPhaseOf (W (K₀.of C E)) ((a + b₂) / 2) := by
  have hthin₁ : b₁ - a + 2 * ε₀ < 1 := by
    linarith
  have hthin₁' : b₁ - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin₁' hε₀ hε₀2 hsin
  have hW_ne :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₁ → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₁ →
        a - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₁ →
        b₁ + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₁) / 2) < b₁ + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hlo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_lo
  have hhi :
      wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) < b₁ + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_hi
  have hbranch :
      wPhaseOf (W (K₀.of C E)) ((a + b₁) / 2) ∈
        Set.Ioc (((a + b₂) / 2) - 1) (((a + b₂) / 2) + 1) := by
    constructor
    · linarith [hlo, hb, hthin₂]
    · linarith [hhi, hb, hthin₂]
  have hWneE : W (K₀.of C E) ≠ 0 := by
    exact σ.W_ne_zero_of_intervalProp C W hthin₁'
      (stabSeminorm_lt_cos_of_hsin_hthin
        (C := C) (σ := σ) (W := W) hab₁ hε₀ hε₀2 hthin₁ hsin) hEne hI
  exact wPhaseOf_indep hWneE _ _ hbranch

private theorem wPhaseOf_eq_of_intervalProp_lower_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b ε₀ : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₂ ≤ a₁)
    {E : C} (hI : σ.slicing.intervalProp C a₁ b E) (hEne : ¬IsZero E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin₂ : b - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) =
      wPhaseOf (W (K₀.of C E)) ((a₂ + b) / 2) := by
  have hthin₁ : b - a₁ + 2 * ε₀ < 1 := by
    linarith
  have hthin₁' : b - a₁ < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin₁' hε₀ hε₀2 hsin
  have hW_ne :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a₁ < φ → φ < b → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a₁ < φ → φ < b →
        a₁ - ε₀ < wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) < a₁ - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a₁ < φ → φ < b →
        b + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a₁ + b) / 2) < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hlo :
      a₁ - ε₀ < wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_lo
  have hhi :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_hi
  have hbranch :
      wPhaseOf (W (K₀.of C E)) ((a₁ + b) / 2) ∈
        Set.Ioc (((a₂ + b) / 2) - 1) (((a₂ + b) / 2) + 1) := by
    constructor
    · linarith [hlo, ha, hthin₂]
    · linarith [hhi, hthin₂]
  have hWneE : W (K₀.of C E) ≠ 0 := by
    exact σ.W_ne_zero_of_intervalProp C W hthin₁'
      (stabSeminorm_lt_cos_of_hsin_hthin
        (C := C) (σ := σ) (W := W) ha₁ hε₀ hε₀2 hthin₁ hsin) hEne hI
  exact wPhaseOf_indep hWneE _ _ hbranch

private theorem wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b ψ ε₀ : ℝ} {E : C}
    (hI : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
  have hab : a < b := by
    rcases hI with hEZ | ⟨F, hF⟩
    · exact absurd hEZ hEne
    · have hn : 0 < F.n := by
        by_contra hn
        exact hEne (F.toPostnikovTower.zero_isZero (by omega))
      linarith [(hF ⟨0, hn⟩).1, (hF ⟨0, hn⟩).2]
  have hthin' : b - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin' hε₀ hε₀2 hsin
  have hW_ne :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        a - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b →
        b + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hlo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_lo
  have hhi :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne hpert_hi
  constructor <;> linarith

private theorem exists_upper_boundary_triangle
    (s : Slicing C) [IsTriangulated C] {a b₁ b₂ : ℝ}
    (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    {Q : C} (hQ : s.intervalProp C a b₂ Q) :
    ∃ (X Y : C) (f : X ⟶ Q) (g : Q ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.geProp C b₁ X ∧
      s.intervalProp C a b₁ Y := by
  let ss := s.phaseShift C b₁
  let t := ss.toTStructureGE
  obtain ⟨X, Y, hX : t.le 0 X, hY : t.ge 1 Y, f, g, h, hT⟩ := t.exists_triangle_zero_one Q
  have hX_ge : s.geProp C b₁ X := by
    have hX' : ss.geProp C 0 X := by
      change ss.geProp C (-↑(0 : ℤ)) X at hX
      simpa using hX
    exact (s.phaseShift_geProp_zero C b₁ X).mp hX'
  have hY_lt : s.ltProp C b₁ Y := by
    have hY' : ss.ltProp C 0 Y := by
      change ss.ltProp C (1 - ↑(1 : ℤ)) Y at hY
      simpa using hY
    exact (s.phaseShift_ltProp_zero C b₁ Y).mp hY'
  refine ⟨X, Y, f, g, h, hT, hX_ge,
    ?_⟩
  by_cases hYZ : IsZero Y
  · exact Or.inl hYZ
  · have hY_minus : a < s.phiMinus C Y hYZ :=
      s.phiMinus_gt_of_triangle_with_geProp C hYZ
        (fun hQZ ↦ s.phiMinus_gt_of_intervalProp C hQZ hQ)
        hX_ge (by linarith) hT
    have hY_plus : s.phiPlus C Y hYZ < b₁ := s.phiPlus_lt_of_ltProp C hYZ hY_lt
    obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C s hYZ
    exact Or.inr ⟨F, fun i ↦ ⟨by
      calc
        a < s.phiMinus C Y hYZ := hY_minus
        _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C Y hYZ F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)),
      by
        calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
          _ = s.phiPlus C Y hYZ := (s.phiPlus_eq C Y hYZ F hn hfirst).symm
          _ < b₁ := hY_plus⟩⟩

private theorem gtProp_of_geProp_of_lt
    (s : Slicing C) {a b : ℝ} (hab : a < b) {E : C}
    (hE : s.geProp C b E) :
    s.gtProp C a E := by
  rcases hE with hZ | ⟨F, hF, hge⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨F, hF, lt_of_lt_of_le hab hge⟩

private theorem wPhaseOf_gt_of_geProp_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ψ ε₀ : ℝ} (hab : a < b) {E : C}
    (hI : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (hGe : σ.slicing.geProp C (ψ + ε₀) E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    ψ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) := by
  have hthin1 : b - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin1 hε₀ hε₀2 hsin
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEne
  have hphi_lower : ψ + ε₀ ≤ σ.slicing.phiMinus C E hEne :=
    σ.slicing.phiMinus_ge_of_geProp C hEne hGe
  have hphases : ∀ i : Fin F.n, ψ + ε₀ ≤ F.φ i ∧ F.φ i < b := by
    intro i
    constructor
    · calc
        ψ + ε₀ ≤ σ.slicing.phiMinus C E hEne := hphi_lower
        _ = F.φ ⟨F.n - 1, by omega⟩ := σ.slicing.phiMinus_eq C E hEne F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ = σ.slicing.phiPlus C E hEne := (σ.slicing.phiPlus_eq C E hEne F hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hEne hI
  set P := F.toPostnikovTower
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  have him_pos :
      0 < (W (K₀.of C E) * rot).im := by
    rw [hWE, Finset.sum_mul]
    rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
        ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
      map_sum Complex.imAddGroupHom _ _]
    apply lt_of_lt_of_le _ (Finset.single_le_sum
      (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)
      (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
    · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable ⟨0, hn⟩) hfirst
        (by linarith [(hphases ⟨0, hn⟩).1]) (hphases ⟨0, hn⟩).2
      have hlo_pert' :
          F.φ ⟨0, hn⟩ - ε₀ <
            wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) := by
        simpa [P] using hlo_pert
      have hhi_pert' :
          wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) < F.φ ⟨0, hn⟩ + ε₀ := by
        simpa [P] using hhi_pert
      exact im_pos_of_phase_above
        (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW
          (F.semistable ⟨0, hn⟩) hfirst))
        (wPhaseOf_compat _ _)
        (by linarith [hlo_pert', (hphases ⟨0, hn⟩).1])
        (by
          have hbψ : b + ε₀ < ψ + 1 := by
            linarith
          have hupper : F.φ ⟨0, hn⟩ + ε₀ < ψ + 1 := by
            linarith [(hphases ⟨0, hn⟩).2, hbψ]
          linarith [hhi_pert', hupper])
    · by_cases hi : IsZero (P.factor i)
      · simp [K₀.of_isZero C hi]
      · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable i) hi
          (by linarith [(hphases i).1]) (hphases i).2
        have hlo_pert' :
            F.φ i - ε₀ < wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) := by
          simpa [P] using hlo_pert
        have hhi_pert' :
            wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) < F.φ i + ε₀ := by
          simpa [P] using hhi_pert
        exact le_of_lt <| im_pos_of_phase_above
          (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW (F.semistable i) hi))
          (wPhaseOf_compat _ _)
          (by linarith [hlo_pert', (hphases i).1])
          (by
            have hbψ : b + ε₀ < ψ + 1 := by
              linarith
            have hupper : F.φ i + ε₀ < ψ + 1 := by
              linarith [(hphases i).2, hbψ]
            linarith [hhi_pert', hupper])
  have hW_ne_ab : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b → W (K₀.of C G) ≠ 0 := by
    intro G θ hG hGne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hG hGne
  have hpert_gt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      a - ε₀ < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < a - ε₀ + 1 := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by linarith⟩
  have hpert_lt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      b + ε₀ - 1 < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < b + ε₀ := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by linarith⟩
  have hphase_lo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W (by linarith) hI hW_ne_ab hpert_gt
  have hphase_hi :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W (by linarith) hI hW_ne_ab hpert_lt
  have hrange :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
    constructor
    · have : ψ - 1 < a - ε₀ := by
        linarith
      linarith
    · have : b + ε₀ < ψ + 1 := by
        linarith
      linarith
  exact wPhaseOf_gt_of_im_pos him_pos hrange

private theorem intervalProp_of_upper_boundary_triangle
    (s : Slicing C) [IsTriangulated C] {a b₁ b₂ : ℝ}
    (hab₁ : a < b₁) (hab₂ : a < b₂) (hb₁ : b₁ ≤ a + 1)
    {Q X Y : C}
    (hQ : s.intervalProp C a b₂ Q)
    (hX_ge : s.geProp C b₁ X)
    (hY : s.intervalProp C a b₁ Y)
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b₂ X := by
  have hY_le : s.leProp C (a + 1) Y := by
    exact ((s.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁) Y)
      (s.leProp_of_intervalProp C hY)
  have hX_gt : s.gtProp C a X :=
    gtProp_of_geProp_of_lt (C := C) (s := s) hab₁ hX_ge
  exact s.first_intervalProp_of_triangle C hab₂ hQ hY_le hX_gt hT

private theorem wPhaseOf_gt_of_upper_boundary_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b₁ b₂ ψ ε₀ : ℝ}
    (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    {Q X Y : C}
    (hQ : σ.slicing.intervalProp C a b₂ Q)
    (hX_ge : σ.slicing.geProp C b₁ X)
    (hY : σ.slicing.intervalProp C a b₁ Y)
    (hXne : ¬IsZero X)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    ψ < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) := by
  have hb₁ : b₁ ≤ a + 1 := by
    have : b₂ - a < 1 := by
      linarith
    linarith
  have hXI : σ.slicing.intervalProp C a b₂ X :=
    intervalProp_of_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb₁ hQ hX_ge hY hT
  have hX_ge' : σ.slicing.geProp C (ψ + ε₀) X := by
    exact ((σ.slicing.geProp_anti (C := C) (t₁ := ψ + ε₀) (t₂ := b₁)
      (by linarith)) X) hX_ge
  have henv_hi₂ : ψ ≤ b₂ - ε₀ := by
    linarith
  exact wPhaseOf_gt_of_geProp_target (C := C) σ W hW hab₂
    hXI hXne hX_ge' hε₀ hε₀2 henv_lo henv_hi₂ hthin hsin

private theorem wPhaseOf_gt_of_upper_source_boundary_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {φ ψ ε₀ : ℝ} {Q X Y : C}
    (hQ : σ.slicing.intervalProp C (ψ - ε₀) (φ + ε₀) Q)
    (hX_ge : σ.slicing.geProp C (ψ + ε₀) X)
    (hY : σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) Y)
    (hXne : ¬IsZero X)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_lo : φ - ε₀ < ψ) (hψ_hi : ψ < φ + ε₀) (hψ_le : ψ ≤ φ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    ψ < wPhaseOf (W (K₀.of C X)) (((ψ - ε₀) + (φ + ε₀)) / 2) := by
  have hthin : (φ + ε₀) - (ψ - ε₀) + 2 * ε₀ < 1 := by
    linarith [hε₀8]
  exact wPhaseOf_gt_of_upper_boundary_triangle
    (C := C) (σ := σ) (W := W) (hW := hW)
    (a := ψ - ε₀) (b₁ := ψ + ε₀) (b₂ := φ + ε₀) (ψ := ψ) (ε₀ := ε₀)
    (by linarith) (by linarith) (by linarith [hψ_le]) hQ hX_ge hY hXne
    hε₀ hε₀2 (by linarith) (by linarith) hthin hsin hT

private theorem wPhaseOf_gt_of_upper_source_boundary_P_phi
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {φ ψ ε₀ : ℝ} {Q X Y : C}
    (hQ : σ.slicing.intervalProp C (ψ - ε₀) (φ + ε₀) Q)
    (hX_ge : σ.slicing.geProp C (ψ + ε₀) X)
    (hY_Pφ : σ.slicing.P φ Y)
    (hXne : ¬IsZero X)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_lo : φ - ε₀ < ψ) (hψ_hi : ψ < φ + ε₀) (hψ_le : ψ ≤ φ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ Q} {g : Q ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    ψ < wPhaseOf (W (K₀.of C X)) (((ψ - ε₀) + (φ + ε₀)) / 2) := by
  have hY :
      σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) Y := by
    exact σ.slicing.intervalProp_of_semistable C hY_Pφ (by linarith) (by linarith)
  exact wPhaseOf_gt_of_upper_source_boundary_target
    (C := C) (σ := σ) (W := W) (hW := hW)
    hQ hX_ge hY hXne hε₀ hε₀2 hε₀8 hψ_lo hψ_hi hψ_le hsin hT

private theorem wPhaseOf_lt_of_leProp_source
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ψ ε₀ : ℝ} (hab : a < b) {E : C}
    (hI : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (hLe : σ.slicing.leProp C (ψ - ε₀) E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < ψ := by
  have hthin1 : b - a < 1 := by
    linarith
  let hpert := hperturb_of_stabSeminorm C σ W hW hthin1 hε₀ hε₀2 hsin
  obtain ⟨F, hn, hfirst, hlast⟩ := HNFiltration.exists_both_nonzero C σ.slicing hEne
  have hphi_upper : σ.slicing.phiPlus C E hEne ≤ ψ - ε₀ :=
    σ.slicing.phiPlus_le_of_leProp C hEne hLe
  have hphases : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i ≤ ψ - ε₀ := by
    intro i
    constructor
    · calc
        a < σ.slicing.phiMinus C E hEne := σ.slicing.phiMinus_gt_of_intervalProp C hEne hI
        _ = F.φ ⟨F.n - 1, by omega⟩ := σ.slicing.phiMinus_eq C E hEne F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ = σ.slicing.phiPlus C E hEne := (σ.slicing.phiPlus_eq C E hEne F hn hfirst).symm
        _ ≤ ψ - ε₀ := hphi_upper
  set P := F.toPostnikovTower
  set rot := Complex.exp (-(↑(Real.pi * ψ) * Complex.I))
  have hWE : W (K₀.of C E) =
      ∑ i : Fin F.n, W (K₀.of C (P.factor i)) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum]
  have him_neg :
      (W (K₀.of C E) * rot).im < 0 := by
    rw [hWE, Finset.sum_mul]
    rw [show (∑ i : Fin F.n, W (K₀.of C (P.factor i)) * rot).im =
        ∑ i : Fin F.n, (W (K₀.of C (P.factor i)) * rot).im from
      map_sum Complex.imAddGroupHom _ _]
    suffices h : 0 < ∑ i : Fin F.n, -(W (K₀.of C (P.factor i)) * rot).im by
      linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
        (f := fun i ↦ (W (K₀.of C (P.factor i)) * rot).im)]
    apply lt_of_lt_of_le _ (Finset.single_le_sum
      (f := fun i ↦ -(W (K₀.of C (P.factor i)) * rot).im)
      (fun i _ ↦ ?_) (Finset.mem_univ ⟨0, hn⟩))
    · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable ⟨0, hn⟩) hfirst
          (hphases ⟨0, hn⟩).1 (lt_of_le_of_lt (hphases ⟨0, hn⟩).2 <| by linarith)
      have hlo_pert' :
          F.φ ⟨0, hn⟩ - ε₀ <
            wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) := by
        simpa [P] using hlo_pert
      have hhi_pert' :
          wPhaseOf (W (K₀.of C (P.factor ⟨0, hn⟩))) ((a + b) / 2) <
            F.φ ⟨0, hn⟩ + ε₀ := by
        simpa [P] using hhi_pert
      exact neg_pos.mpr <| im_neg_of_phase_below
        (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW
          (F.semistable ⟨0, hn⟩) hfirst))
        (wPhaseOf_compat _ _)
        (by
          have hlower : ψ - 1 < a - ε₀ := by
            linarith
          linarith [hlo_pert', hlower, (hphases ⟨0, hn⟩).1])
        (by linarith [hhi_pert', (hphases ⟨0, hn⟩).2])
    · by_cases hi : IsZero (P.factor i)
      · simp [P, K₀.of_isZero C hi]
      · obtain ⟨hlo_pert, hhi_pert⟩ := hpert _ _ (F.semistable i) hi (hphases i).1
            (lt_of_le_of_lt (hphases i).2 <| by linarith)
        have hlo_pert' :
            F.φ i - ε₀ <
              wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) := by
          simpa [P] using hlo_pert
        have hhi_pert' :
            wPhaseOf (W (K₀.of C (P.factor i))) ((a + b) / 2) < F.φ i + ε₀ := by
          simpa [P] using hhi_pert
        exact le_of_lt <| neg_pos.mpr <| im_neg_of_phase_below
          (norm_pos_iff.mpr (σ.W_ne_zero_of_seminorm_lt_one C W hW (F.semistable i) hi))
          (wPhaseOf_compat _ _)
          (by
            have hlower : ψ - 1 < a - ε₀ := by
              linarith
            linarith [hlo_pert', hlower, (hphases i).1])
          (by linarith [hhi_pert', (hphases i).2])
  have hW_ne_ab : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b → W (K₀.of C G) ≠ 0 := by
    intro G θ hG hGne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hG hGne
  have hpert_gt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      a - ε₀ < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < a - ε₀ + 1 := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by linarith⟩
  have hpert_lt : ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
      a < θ → θ < b →
      b + ε₀ - 1 < wPhaseOf (W (K₀.of C G)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C G)) ((a + b) / 2) < b + ε₀ := by
    intro G θ hG hGne haθ hθb
    obtain ⟨hlo, hhi⟩ := hpert G θ hG hGne haθ hθb
    exact ⟨by linarith, by linarith⟩
  have hphase_lo :
      a - ε₀ < wPhaseOf (W (K₀.of C E)) ((a + b) / 2) :=
    wPhaseOf_gt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne_ab hpert_gt
  have hphase_hi :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) < b + ε₀ :=
    wPhaseOf_lt_of_intervalProp C σ hEne W
      (by linarith) hI hW_ne_ab hpert_lt
  have hrange :
      wPhaseOf (W (K₀.of C E)) ((a + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
    constructor
    · have : ψ - 1 < a - ε₀ := by
        linarith
      linarith
    · have : b + ε₀ < ψ + 1 := by
        linarith
      linarith
  exact wPhaseOf_lt_of_im_neg him_neg hrange

private theorem exists_lower_boundary_triangle
    (s : Slicing C) [IsTriangulated C] {a₁ a₂ b : ℝ}
    (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₂ ≤ a₁)
    {K : C} (hK : s.intervalProp C a₂ b K) :
    ∃ (X Y : C) (f : X ⟶ K) (g : K ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.intervalProp C a₁ b X ∧
      s.leProp C a₁ Y := by
  let ss := s.phaseShift C a₁
  let t := ss.toTStructure
  obtain ⟨X, Y, hX : t.le 0 X, hY : t.ge 1 Y, f, g, h, hT⟩ := t.exists_triangle_zero_one K
  have hX_gt : s.gtProp C a₁ X := by
    have hX' : ss.gtProp C 0 X := by
      change ss.gtProp C (-↑(0 : ℤ)) X at hX
      simpa using hX
    exact (s.phaseShift_gtProp_zero C a₁ X).mp hX'
  have hY_le : s.leProp C a₁ Y := by
    have hY' : ss.leProp C 0 Y := by
      change ss.leProp C (1 - ↑(1 : ℤ)) Y at hY
      simpa using hY
    exact (s.phaseShift_leProp_zero C a₁ Y).mp hY'
  have hX_I : s.intervalProp C a₁ b X := by
    by_cases hXZ : IsZero X
    · exact Or.inl hXZ
    · have hX_plus : s.phiPlus C X hXZ < b :=
        s.phiPlus_lt_of_triangle_with_leProp C hXZ
          (fun hKZ ↦ s.phiPlus_lt_of_intervalProp C hKZ hK) hY_le (by linarith) hT
      have hX_minus : a₁ < s.phiMinus C X hXZ :=
        s.phiMinus_gt_of_gtProp C hXZ hX_gt
      exact s.intervalProp_of_intrinsic_phases C hXZ hX_minus hX_plus
  exact ⟨X, Y, f, g, h, hT, hX_I, hY_le⟩

private theorem intervalProp_of_lower_boundary_triangle
    (s : Slicing C) [IsTriangulated C] {a₁ a₂ b : ℝ}
    (hb : a₂ < b) (ha₁ : a₁ < b) (ha : a₂ ≤ a₁)
    {K X Y : C}
    (hK : s.intervalProp C a₂ b K)
    (hX : s.intervalProp C a₁ b X)
    (hY_le : s.leProp C a₁ Y)
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a₂ b Y := by
  by_cases hY0 : IsZero Y
  · exact Or.inl hY0
  · have hY_plus : s.phiPlus C Y hY0 < b := by
      have hY_plus_le : s.phiPlus C Y hY0 ≤ a₁ := s.phiPlus_le_of_leProp C hY0 hY_le
      linarith
    have hX_ge : s.geProp C a₁ X := by
      rcases s.gtProp_of_intervalProp C hX with hXZ | ⟨F, hF, hgt⟩
      · exact Or.inl hXZ
      · exact Or.inr ⟨F, hF, le_of_lt hgt⟩
    have hY_minus : a₂ < s.phiMinus C Y hY0 :=
      s.phiMinus_gt_of_triangle_with_geProp C hY0
        (fun hK0 ↦ s.phiMinus_gt_of_intervalProp C hK0 hK)
        hX_ge (by linarith) hT
    exact s.intervalProp_of_intrinsic_phases C hY0 hY_minus hY_plus

private theorem wPhaseOf_lt_of_lower_boundary_triangle
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b ψ ε₀ : ℝ}
    (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₂ ≤ a₁)
    {K X Y : C}
    (hK : σ.slicing.intervalProp C a₂ b K)
    (hX : σ.slicing.intervalProp C a₁ b X)
    (hY_le : σ.slicing.leProp C a₁ Y)
    (hYne : ¬IsZero Y)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₁ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin : b - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) < ψ := by
  have hY_I : σ.slicing.intervalProp C a₂ b Y :=
    intervalProp_of_lower_boundary_triangle (C := C) (s := σ.slicing)
      ha₂ ha₁ ha hK hX hY_le hT
  have hY_le' : σ.slicing.leProp C (ψ - ε₀) Y := by
    exact ((σ.slicing.leProp_mono (C := C) (t₁ := a₁) (t₂ := ψ - ε₀) (by linarith)) Y) hY_le
  exact wPhaseOf_lt_of_leProp_source (C := C) σ W hW ha₂
    hY_I hYne hY_le' hε₀ hε₀2 (by linarith) henv_hi hthin hsin

private theorem wPhaseOf_lt_of_lower_source_boundary_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {φ ψ ε₀ : ℝ} {K X Y : C}
    (hK : σ.slicing.intervalProp C (φ - ε₀) (ψ + ε₀) K)
    (hX : σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) X)
    (hY_le : σ.slicing.leProp C (ψ - ε₀) Y)
    (hYne : ¬IsZero Y)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_lo : φ - ε₀ < ψ) (hψ_hi : ψ < φ + ε₀) (hφ_le : φ ≤ ψ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    wPhaseOf (W (K₀.of C Y)) (((φ - ε₀) + (ψ + ε₀)) / 2) < ψ := by
  have hthin : (ψ + ε₀) - (φ - ε₀) + 2 * ε₀ < 1 := by
    linarith [hε₀8]
  exact wPhaseOf_lt_of_lower_boundary_triangle
    (C := C) (σ := σ) (W := W) (hW := hW)
    (a₁ := ψ - ε₀) (a₂ := φ - ε₀) (b := ψ + ε₀) (ψ := ψ) (ε₀ := ε₀)
    (by linarith) (by linarith) (by linarith [hφ_le]) hK hX hY_le hYne
    hε₀ hε₀2 (by linarith) (by linarith) hthin hsin hT

private theorem wPhaseOf_lt_of_lower_source_boundary_P_phi
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {φ ψ ε₀ : ℝ} {K X Y : C}
    (hK : σ.slicing.intervalProp C (φ - ε₀) (ψ + ε₀) K)
    (hX_Pφ : σ.slicing.P φ X)
    (hY_le : σ.slicing.leProp C (ψ - ε₀) Y)
    (hYne : ¬IsZero Y)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hψ_lo : φ - ε₀ < ψ) (hψ_hi : ψ < φ + ε₀) (hφ_le : φ ≤ ψ)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {f : X ⟶ K} {g : K ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    wPhaseOf (W (K₀.of C Y)) (((φ - ε₀) + (ψ + ε₀)) / 2) < ψ := by
  have hX :
      σ.slicing.intervalProp C (ψ - ε₀) (ψ + ε₀) X := by
    exact σ.slicing.intervalProp_of_semistable C hX_Pφ (by linarith) (by linarith)
  exact wPhaseOf_lt_of_lower_source_boundary_target
    (C := C) (σ := σ) (W := W) (hW := hW)
    hK hX hY_le hYne hε₀ hε₀2 hε₀8 hψ_lo hψ_hi hφ_le hsin hT

variable [IsTriangulated C] in
/-- Package the upper-boundary truncation as a strict short exact sequence in the larger thin
interval category. This is the Section 7 reduction step `0 → A → E → E' → 0`, with the
subobject supported on the upper boundary strip and the quotient still lying in the larger thin
category. -/
private theorem exists_upper_boundary_strictShortExact
    (s : Slicing C) {a b₁ b₂ : ℝ}
    [Fact (a < b₂)] [Fact (b₂ - a ≤ 1)]
    (hab₁ : a < b₁) (hb : b₁ ≤ b₂)
    {Q : C} (hQ : s.intervalProp C a b₂ Q) :
    ∃ S : ShortComplex (s.IntervalCat C a b₂),
      StrictShortExact S ∧
      S.X₂ = ⟨Q, hQ⟩ ∧
      s.geProp C b₁ S.X₁.obj ∧
      s.intervalProp C a b₁ S.X₃.obj := by
  have hab₂ : a < b₂ := Fact.out
  have hthin₂ : b₂ - a ≤ 1 := Fact.out
  obtain ⟨X, Y, f, g, h, hT, hX_ge, hY_small⟩ :=
    exists_upper_boundary_triangle (C := C) (s := s)
      (a := a) (b₁ := b₁) (b₂ := b₂) hab₁ hab₂ hb hQ
  have hb₁_le : b₁ ≤ a + 1 := by
    linarith
  let XI : s.IntervalCat C a b₂ := ⟨X,
    intervalProp_of_upper_boundary_triangle (C := C) (s := s)
      (a := a) (b₁ := b₁) (b₂ := b₂) hab₁ hab₂ hb₁_le hQ hX_ge hY_small hT⟩
  let YI : s.IntervalCat C a b₂ := ⟨Y,
    s.intervalProp_mono C (show a ≤ a by linarith) hb hY_small⟩
  let QI : s.IntervalCat C a b₂ := ⟨Q, hQ⟩
  let fi : XI ⟶ QI := ObjectProperty.homMk f
  let gi : QI ⟶ YI := ObjectProperty.homMk g
  let S : ShortComplex (s.IntervalCat C a b₂) := ShortComplex.mk fi gi (by
      ext
      simpa [fi, gi] using comp_distTriang_mor_zero₁₂ _ hT)
  have hTS : Triangle.mk S.f.hom S.g.hom h ∈ distTriang C := by
    simpa [S, fi, gi] using hT
  refine ⟨S, ?_, ?_, hX_ge, hY_small⟩
  · exact Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := s) (a := a) (b := b₂) hTS
  · simp [S, QI, XI, YI]

variable [IsTriangulated C] in
/-- Package the lower-boundary truncation as a strict short exact sequence in the larger thin
interval category. This is the dual Section 7 reduction step, with the kernel already lying in
the smaller target interval and the quotient supported on the lower boundary strip. -/
private theorem exists_lower_boundary_strictShortExact
    (s : Slicing C) {a₁ a₂ b : ℝ}
    [Fact (a₂ < b)] [Fact (b - a₂ ≤ 1)]
    (ha₁ : a₁ < b) (ha : a₂ ≤ a₁)
    {K : C} (hK : s.intervalProp C a₂ b K) :
    ∃ S : ShortComplex (s.IntervalCat C a₂ b),
      StrictShortExact S ∧
      S.X₂ = ⟨K, hK⟩ ∧
      s.intervalProp C a₁ b S.X₁.obj ∧
      s.leProp C a₁ S.X₃.obj := by
  have ha₂b : a₂ < b := Fact.out
  have hthin : b - a₂ ≤ 1 := Fact.out
  obtain ⟨X, Y, f, g, h, hT, hX_small, hY_le⟩ :=
    exists_lower_boundary_triangle (C := C) (s := s)
      (a₁ := a₁) (a₂ := a₂) (b := b) ha₁ ha₂b ha hK
  let XI : s.IntervalCat C a₂ b := ⟨X,
    s.intervalProp_mono C ha (show b ≤ b by linarith) hX_small⟩
  let YI : s.IntervalCat C a₂ b := ⟨Y,
    intervalProp_of_lower_boundary_triangle (C := C) (s := s)
      (a₁ := a₁) (a₂ := a₂) (b := b) ha₂b ha₁ ha
      hK hX_small hY_le hT⟩
  let KI : s.IntervalCat C a₂ b := ⟨K, hK⟩
  let fi : XI ⟶ KI := ObjectProperty.homMk f
  let gi : KI ⟶ YI := ObjectProperty.homMk g
  let S : ShortComplex (s.IntervalCat C a₂ b) := ShortComplex.mk fi gi (by
      ext
      simpa [fi, gi] using comp_distTriang_mor_zero₁₂ _ hT)
  have hTS : Triangle.mk S.f.hom S.g.hom h ∈ distTriang C := by
    simpa [S, fi, gi] using hT
  refine ⟨S, ?_, ?_, hX_small, hY_le⟩
  · exact Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := s) (a := a₂) (b := b) hTS
  · simp [S, KI, XI, YI]

private theorem intervalProp_of_wSemistable_upper_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b₁ b₂ ψ ε₀ : ℝ} (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin₂ : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    σ.slicing.intervalProp C a b₁ E := by
  have hthin₂' : b₂ - a < 1 := by
    linarith
  obtain ⟨X, Y, fX, gY, δY, hTQ, hX_ge, hY₁⟩ :=
    exists_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb hSS.1
  have hb₁_le : b₁ ≤ a + 1 := by
    linarith
  have hX₂ : σ.slicing.intervalProp C a b₂ X :=
    intervalProp_of_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb₁_le hSS.1 hX_ge hY₁ hTQ
  have hY₂ : σ.slicing.intervalProp C a b₂ Y :=
    σ.slicing.intervalProp_mono C (show a ≤ a by linarith) hb hY₁
  by_cases hX_zero : IsZero X
  · exact σ.slicing.intervalProp_of_triangle C (Or.inl hX_zero) hY₁ hTQ
  · have hX_phase_gt :
        ψ < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) :=
      wPhaseOf_gt_of_upper_boundary_triangle
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab₂ hb hSS.1 hX_ge hY₁ hX_zero
        hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTQ
    by_cases hY_zero : IsZero Y
    · haveI : IsIso fX :=
        (Triangle.isZero₃_iff_isIso₁ (Triangle.mk fX gY δY) hTQ).mp hY_zero
      have hX_phase_eq :
          wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) = ψ := by
        rw [K₀.of_iso C (asIso fX)]
        simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1
      linarith
    · letI : Fact (a < b₂) := ⟨hab₂⟩
      letI : Fact (b₂ - a ≤ 1) := ⟨by linarith⟩
      let EI₂ : σ.slicing.IntervalCat C a b₂ := ⟨E, hSS.1⟩
      let XI₂ : σ.slicing.IntervalCat C a b₂ := ⟨X, hX₂⟩
      let YI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Y, hY₂⟩
      let xE : XI₂ ⟶ EI₂ := ObjectProperty.homMk fX
      let qY : EI₂ ⟶ YI₂ := ObjectProperty.homMk gY
      let hcomp : xE ≫ qY = 0 := by
        ext
        simpa [xE, qY] using comp_distTriang_mor_zero₁₂ _ hTQ
      let S : ShortComplex (σ.slicing.IntervalCat C a b₂) := ShortComplex.mk xE qY hcomp
      have hT₂ : Triangle.mk S.f.hom S.g.hom δY ∈ distTriang C := by
        simpa [S, xE, qY] using hTQ
      have hS : StrictShortExact S :=
        Slicing.IntervalCat.strictShortExact_of_distTriang
          (C := C) (s := σ.slicing) (a := a) (b := b₂) hT₂
      have hqY_strict : IsStrictEpi qY := ⟨hS.shortExact.epi_g, hS.strict_g⟩
      let hpert₂ := hperturb_of_stabSeminorm C σ W hW hthin₂' hε₀ hε₀2 hsin
      have hW_interval :
          ∀ {F : C}, σ.slicing.intervalProp C a b₂ F → ¬IsZero F → W (K₀.of C F) ≠ 0 := by
        intro F hF hFne
        exact σ.W_ne_zero_of_intervalProp C W hthin₂'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) hab₂ hε₀ hε₀2 hthin₂ hsin) hFne hF
      have hY_phase_ge :
          ψ ≤ wPhaseOf (W (K₀.of C Y)) ((a + b₂) / 2) := by
        let ssf₂ := σ.skewedStabilityFunction_of_near C W hW hab₂
        simpa [StabilityCondition.skewedStabilityFunction_of_near, EI₂, YI₂, qY] using
          (SkewedStabilityFunction.phase_le_of_strictQuotient
            (C := C) (σ := σ) (a := a) (b := b₂) (ssf := ssf₂)
            (X := EI₂) (Y := YI₂) hSS hε₀ hthin₂ hW_interval hpert₂ qY hqY_strict hY_zero)
      have henv_hi₂ : ψ ≤ b₂ - ε₀ := by
        linarith
      have hX_range :
          wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hX₂ hX_zero hε₀ hε₀2 henv_lo henv_hi₂
          hthin₂ hsin
      have hY_range :
          wPhaseOf (W (K₀.of C Y)) ((a + b₂) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hY₂ hY_zero hε₀ hε₀2 henv_lo henv_hi₂
          hthin₂ hsin
      have hsum :
          W (K₀.of C E) = W (K₀.of C X) + W (K₀.of C Y) := by
        simpa [map_add] using congrArg W
          (K₀.of_triangle C (Triangle.mk fX gY δY) hTQ)
      have hY_phase_lt :
          wPhaseOf (W (K₀.of C Y)) ((a + b₂) / 2) < ψ := by
        exact wPhaseOf_seesaw_dual hsum.symm
          (by simpa [StabilityCondition.skewedStabilityFunction_of_near] using hSS.2.2.2.1)
          hX_phase_gt (hW_interval hX₂ hX_zero) hX_range hY_range
      linarith

private theorem intervalProp_of_wSemistable_lower_target
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b ψ ε₀ : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₁ ≤ a₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW ha₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₂ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin₁ : b - a₁ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    σ.slicing.intervalProp C a₂ b E := by
  obtain ⟨X, Y, fX, gY, δY, hTQ, hX₂, hY_le⟩ :=
    exists_lower_boundary_triangle (C := C) (s := σ.slicing)
      (a₁ := a₂) (a₂ := a₁) (b := b) ha₂ ha₁ ha hSS.1
  have hY₁ : σ.slicing.intervalProp C a₁ b Y :=
    intervalProp_of_lower_boundary_triangle (C := C) (s := σ.slicing)
      (a₁ := a₂) (a₂ := a₁) (b := b) ha₁ ha₂ ha hSS.1 hX₂ hY_le hTQ
  by_cases hY_zero : IsZero Y
  · exact σ.slicing.intervalProp_of_triangle C hX₂ (Or.inl hY_zero) hTQ
  · have hY_phase_lt :
        wPhaseOf (W (K₀.of C Y)) ((a₁ + b) / 2) < ψ :=
      wPhaseOf_lt_of_lower_boundary_triangle
        (C := C) (σ := σ) (W := W) (hW := hW) ha₂ ha₁ ha hSS.1 hX₂ hY_le hY_zero
        hε₀ hε₀2 henv_lo henv_hi hthin₁ hsin hTQ
    letI : Fact (a₁ < b) := ⟨ha₁⟩
    letI : Fact (b - a₁ ≤ 1) := ⟨by linarith⟩
    have hX₁ : σ.slicing.intervalProp C a₁ b X :=
      σ.slicing.intervalProp_mono C ha (show b ≤ b by linarith) hX₂
    let EI₁ : σ.slicing.IntervalCat C a₁ b := ⟨E, hSS.1⟩
    let XI₁ : σ.slicing.IntervalCat C a₁ b := ⟨X, hX₁⟩
    let YI₁ : σ.slicing.IntervalCat C a₁ b := ⟨Y, hY₁⟩
    let xE : XI₁ ⟶ EI₁ := ObjectProperty.homMk fX
    let qY : EI₁ ⟶ YI₁ := ObjectProperty.homMk gY
    let hcomp : xE ≫ qY = 0 := by
      ext
      simpa [xE, qY] using comp_distTriang_mor_zero₁₂ _ hTQ
    let S : ShortComplex (σ.slicing.IntervalCat C a₁ b) := ShortComplex.mk xE qY hcomp
    have hT₁ : Triangle.mk S.f.hom S.g.hom δY ∈ distTriang C := by
      simpa [S, xE, qY] using hTQ
    have hS : StrictShortExact S :=
      Slicing.IntervalCat.strictShortExact_of_distTriang
        (C := C) (s := σ.slicing) (a := a₁) (b := b) hT₁
    have hqY_strict : IsStrictEpi qY := ⟨hS.shortExact.epi_g, hS.strict_g⟩
    have hthin₁' : b - a₁ < 1 := by
      linarith
    let hpert₁ := hperturb_of_stabSeminorm C σ W hW hthin₁' hε₀ hε₀2 hsin
    have hW_interval :
        ∀ {F : C}, σ.slicing.intervalProp C a₁ b F → ¬IsZero F → W (K₀.of C F) ≠ 0 := by
      intro F hF hFne
      exact σ.W_ne_zero_of_intervalProp C W hthin₁'
        (stabSeminorm_lt_cos_of_hsin_hthin
          (C := C) (σ := σ) (W := W) ha₁ hε₀ hε₀2 hthin₁ hsin) hFne hF
    have hY_phase_ge :
        ψ ≤ wPhaseOf (W (K₀.of C Y)) ((a₁ + b) / 2) := by
      let ssf₁ := σ.skewedStabilityFunction_of_near C W hW ha₁
      simpa [StabilityCondition.skewedStabilityFunction_of_near, EI₁, YI₁, qY] using
        (SkewedStabilityFunction.phase_le_of_strictQuotient
          (C := C) (σ := σ) (a := a₁) (b := b) (ssf := ssf₁)
          (X := EI₁) (Y := YI₁) hSS hε₀ hthin₁ hW_interval hpert₁ qY hqY_strict hY_zero)
    linarith

/-! ### Thin-interval Phase 3 selection infrastructure -/

private lemma intervalSubobject_isZero_iff_eq_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b} (B : Subobject X) :
    IsZero (B : s.IntervalCat C a b) ↔ B = ⊥ := by
  constructor
  · intro hZ
    have : B.arrow = 0 := zero_of_source_iso_zero _ hZ.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  · intro h
    subst h
    exact (isZero_zero (s.IntervalCat C a b)).of_iso Subobject.botCoeIsoZero

private lemma intervalSubobject_not_isZero_of_ne_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b} {B : Subobject X}
    (h : B ≠ ⊥) : ¬IsZero (B : s.IntervalCat C a b) :=
  fun hZ ↦ h ((intervalSubobject_isZero_iff_eq_bot
    (C := C) (s := s) (a := a) (b := b) (X := X) B).mp hZ)

private lemma intervalSubobject_top_ne_bot_of_not_isZero
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (hX : ¬IsZero X) : (⊤ : Subobject X) ≠ ⊥ := by
  intro h
  apply hX
  have hZ : IsZero ((⊤ : Subobject X) : s.IntervalCat C a b) :=
    (intervalSubobject_isZero_iff_eq_bot
      (C := C) (s := s) (a := a) (b := b) (X := X) _).mpr h
  exact hZ.of_iso (asIso (⊤ : Subobject X).arrow).symm

private lemma intervalSubobject_arrow_strictMono_of_strictMono
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (f : Y ⟶ X) (hf : IsStrictMono f) :
    letI : Mono f := hf.mono
    IsStrictMono (Subobject.mk f).arrow := by
  letI : Mono f := hf.mono
  let e := Subobject.underlyingIso f
  have he : IsStrictMono e.hom := isStrictMono_of_isIso
  have hcomp : IsStrictMono (e.hom ≫ f) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := s) (a := a) (b := b) e.hom f he hf
  have harr : e.hom ≫ f = (Subobject.mk f).arrow := by
    simpa [e] using (Subobject.underlyingIso_hom_comp_eq_mk f)
  rw [← harr]
  exact hcomp

private theorem interval_strictShortExact_cokernel_of_strictMono
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (f : Y ⟶ X) (hf : IsStrictMono f) :
    StrictShortExact (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) := by
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S, KernelFork.ofι] using hf.isLimitKernelFork
  have hEpi : Epi ((S.map FL).g) := by
    simpa [S, FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) (cokernel.π f) (isStrictEpi_cokernel f)
  have hKer :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hL
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT

private theorem intervalInclusion_map_strictMono
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X Y : s₁.IntervalCat C a₁ b₁} (f : X ⟶ Y) (hf : IsStrictMono f) :
    IsStrictMono ((ObjectProperty.ιOfLE h).map f) := by
  let S : ShortComplex (s₁.IntervalCat C a₁ b₁) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : StrictShortExact S :=
    interval_strictShortExact_cokernel_of_strictMono
      (C := C) (s := s₁) (a := a₁) (b := b₁) f hf
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
    (C := C) (s := s₁) (a := a₁) (b := b₁) hS
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  let S' : ShortComplex (s₂.IntervalCat C a₂ b₂) := S.map I
  have hT' : Triangle.mk S'.f.hom S'.g.hom δ ∈ distTriang C := by
    simpa [I, S, S'] using hT
  exact
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := s₂) (a := a₂) (b := b₂) hT').1

private theorem interval_strictArtinianObject_of_inclusion
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsArtinianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  exact isStrictArtinianObject_of_faithful_map_strictMono I (fun f hf ↦
    intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h f hf)

private theorem interval_strictNoetherianObject_of_inclusion
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictNoetherianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  exact isStrictNoetherianObject_of_faithful_map_strictMono I (fun f hf ↦
    intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h f hf)

private theorem interval_strictFiniteLength_of_inclusion
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsArtinianObject ((ObjectProperty.ιOfLE h).obj X)]
    [IsNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X ∧ IsStrictNoetherianObject X := by
  exact ⟨interval_strictArtinianObject_of_inclusion (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h,
    interval_strictNoetherianObject_of_inclusion (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h⟩

private theorem interval_thinFiniteLength_of_inclusion
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : s₂.IntervalCat C a₂ b₂,
      IsArtinianObject Y ∧ IsNoetherianObject Y) :
    ∀ X : s₁.IntervalCat C a₁ b₁,
      IsStrictArtinianObject X ∧ IsStrictNoetherianObject X := by
  intro X
  have hBig := hFinite ((ObjectProperty.ιOfLE h).obj X)
  letI : IsArtinianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.1
  letI : IsNoetherianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.2
  simpa using
    (interval_strictFiniteLength_of_inclusion
      (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h (X := X))

private theorem interval_strictArtinianObject_of_inclusion_strict
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsStrictArtinianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  let F : StrictSubobject X → StrictSubobject (I.obj X) := fun B ↦ by
    let hstrict : IsStrictMono (I.map B.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B.1.arrow B.2
    letI : Mono (I.map B.1.arrow) := hstrict.mono
    exact ⟨Subobject.mk (I.map B.1.arrow),
      intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s₂) (a := a₂) (b := b₂) (I.map B.1.arrow) hstrict⟩
  have hF_inj : Function.Injective F := by
    intro B₁ B₂ hEq
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    apply Subtype.ext
    have hEq' : Subobject.mk (I.map B₁.1.arrow) = Subobject.mk (I.map B₂.1.arrow) :=
      congrArg Subtype.val hEq
    simpa [Subobject.mk_arrow] using
      (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
        (I.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
        (I.map_injective (by
          simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
          exact Subobject.ofMkLEMk_comp hEq'.le)))
  have hF_mono : Monotone F := by
    intro B₁ B₂ hB
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    change Subobject.mk (I.map B₁.1.arrow) ≤ Subobject.mk (I.map B₂.1.arrow)
    have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
      simpa [Subobject.mk_arrow] using (show B₁.1 ≤ B₂.1 from hB)
    exact Subobject.mk_le_mk_of_comm (I.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
      change I.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk) ≫ I.map B₂.1.arrow =
        I.map B₁.1.arrow
      rw [← I.map_comp]
      simpa using congrArg I.map (Subobject.ofMkLEMk_comp hmk))
  exact
    (show isStrictArtinianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedLT (StrictSubobject X) from by
          rw [← wellFoundedGT_dual_iff, wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o (StrictSubobject (I.obj X))ᵒᵈ :=
            ⟨fun n ↦ OrderDual.toDual (F (f n)),
              fun i j hij ↦ by
                change F (f j) ≤ F (f i)
                exact hF_mono (f.2 hij)⟩
          obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
          exact ⟨n, fun m hm ↦ hF_inj (by
            simpa using congrArg OrderDual.ofDual (hn m hm))⟩))

private theorem interval_strictNoetherianObject_of_inclusion_strict
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsStrictNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictNoetherianObject X := by
  let I : s₁.IntervalCat C a₁ b₁ ⥤ s₂.IntervalCat C a₂ b₂ := ObjectProperty.ιOfLE h
  let F : StrictSubobject X → StrictSubobject (I.obj X) := fun B ↦ by
    let hstrict : IsStrictMono (I.map B.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B.1.arrow B.2
    letI : Mono (I.map B.1.arrow) := hstrict.mono
    exact ⟨Subobject.mk (I.map B.1.arrow),
      intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s₂) (a := a₂) (b := b₂) (I.map B.1.arrow) hstrict⟩
  have hF_inj : Function.Injective F := by
    intro B₁ B₂ hEq
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    apply Subtype.ext
    have hEq' : Subobject.mk (I.map B₁.1.arrow) = Subobject.mk (I.map B₂.1.arrow) :=
      congrArg Subtype.val hEq
    simpa [Subobject.mk_arrow] using
      (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
        (I.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
        (I.map_injective (by
          simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
          exact Subobject.ofMkLEMk_comp hEq'.le)))
  have hF_mono : Monotone F := by
    intro B₁ B₂ hB
    let hstrict₁ : IsStrictMono (I.map B₁.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₁.1.arrow B₁.2
    let hstrict₂ : IsStrictMono (I.map B₂.1.arrow) :=
      intervalInclusion_map_strictMono (C := C) (s₁ := s₁) (s₂ := s₂)
        (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h B₂.1.arrow B₂.2
    letI : Mono (I.map B₁.1.arrow) := hstrict₁.mono
    letI : Mono (I.map B₂.1.arrow) := hstrict₂.mono
    change Subobject.mk (I.map B₁.1.arrow) ≤ Subobject.mk (I.map B₂.1.arrow)
    have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
      simpa [Subobject.mk_arrow] using (show B₁.1 ≤ B₂.1 from hB)
    exact Subobject.mk_le_mk_of_comm (I.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
      change I.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk) ≫ I.map B₂.1.arrow =
        I.map B₁.1.arrow
      rw [← I.map_comp]
      simpa using congrArg I.map (Subobject.ofMkLEMk_comp hmk))
  exact
    (show isStrictNoetherianObject.Is X from
      ObjectProperty.is_of_prop _
        (show WellFoundedGT (StrictSubobject X) from by
          rw [wellFoundedGT_iff_monotone_chain_condition]
          intro f
          let g : ℕ →o StrictSubobject (I.obj X) :=
            ⟨fun n ↦ F (f n),
              fun i j hij ↦ hF_mono (f.2 hij)⟩
          obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
          exact ⟨n, fun m hm ↦ hF_inj (hn m hm)⟩))

private theorem interval_strictFiniteLength_of_inclusion_strict
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X : s₁.IntervalCat C a₁ b₁}
    [IsStrictArtinianObject ((ObjectProperty.ιOfLE h).obj X)]
    [IsStrictNoetherianObject ((ObjectProperty.ιOfLE h).obj X)] :
    IsStrictArtinianObject X ∧ IsStrictNoetherianObject X := by
  exact ⟨interval_strictArtinianObject_of_inclusion_strict (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h,
    interval_strictNoetherianObject_of_inclusion_strict (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h⟩

private theorem interval_thinFiniteLength_of_inclusion_strict
    {s₁ s₂ : Slicing C} [IsTriangulated C]
    {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : s₂.IntervalCat C a₂ b₂,
      IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y) :
    ∀ X : s₁.IntervalCat C a₁ b₁,
      IsStrictArtinianObject X ∧ IsStrictNoetherianObject X := by
  intro X
  have hBig := hFinite ((ObjectProperty.ιOfLE h).obj X)
  letI : IsStrictArtinianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.1
  letI : IsStrictNoetherianObject ((ObjectProperty.ιOfLE h).obj X) := hBig.2
  simpa using
    (interval_strictFiniteLength_of_inclusion_strict
      (C := C) (s₁ := s₁) (s₂ := s₂)
      (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h (X := X))

private theorem SectorFiniteLength.of_wide
    (σ : StabilityCondition C) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8) :
    SectorFiniteLength (C := C) σ ε₀ hε₀ hε₀2 := by
  intro t
  dsimp [SectorFiniteLength, WideSectorFiniteLength] at hWide ⊢
  intro E
  letI : Fact (t - 2 * ε₀ < t + 2 * ε₀) := ⟨by linarith [hε₀]⟩
  letI : Fact ((t + 2 * ε₀) - (t - 2 * ε₀) ≤ 1) := ⟨by linarith [hε₀2]⟩
  letI : Fact (t - 4 * ε₀ < t + 4 * ε₀) := ⟨by linarith [hε₀]⟩
  letI : Fact ((t + 4 * ε₀) - (t - 4 * ε₀) ≤ 1) := ⟨by linarith [hε₀8]⟩
  let hIncl :
      σ.slicing.intervalProp C (t - 2 * ε₀) (t + 2 * ε₀) ≤
        σ.slicing.intervalProp C (t - 4 * ε₀) (t + 4 * ε₀) := by
    intro F hF
    exact σ.slicing.intervalProp_mono C (by linarith) (by linarith) hF
  exact interval_thinFiniteLength_of_inclusion_strict
    (C := C) (s₁ := σ.slicing) (s₂ := σ.slicing)
    (a₁ := t - 2 * ε₀) (b₁ := t + 2 * ε₀)
    (a₂ := t - 4 * ε₀) (b₂ := t + 4 * ε₀) hIncl (hWide t) E

private theorem interval_K0_of_strictMono
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (f : Y ⟶ X) (hf : IsStrictMono f) :
    K₀.of C X.obj = K₀.of C Y.obj + K₀.of C (cokernel f).obj := by
  simpa using
    Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := s) (a := a) (b := b)
      (interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := s) (a := a) (b := b) f hf)

private lemma interval_card_subobject_lt_of_ne_top
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b} {M : Subobject X}
    (hM : M ≠ ⊤) [Finite (Subobject X)] :
    Nat.card (Subobject (M : s.IntervalCat C a b)) < Nat.card (Subobject X) := by
  let φ := (Subobject.map M.arrow).obj
  haveI : Finite (Subobject (M : s.IntervalCat C a b)) := by
    exact Finite.of_injective φ (Subobject.map_obj_injective M.arrow)
  haveI := Fintype.ofFinite (Subobject X)
  haveI := Fintype.ofFinite (Subobject (M : s.IntervalCat C a b))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem (b := ⊤) φ
    (Subobject.map_obj_injective M.arrow) (by
    simp only [Set.mem_range, not_exists]
    intro B hB
    have hle : φ B ≤ M := by
      calc
        φ B ≤ φ ⊤ := (Subobject.map M.arrow).monotone le_top
        _ = M := by simpa [φ] using (Subobject.map_top M.arrow)
    have htop_le : (⊤ : Subobject X) ≤ M := by
      simpa only [hB] using hle
    exact hM (top_le_iff.mp htop_le))

private def intervalLiftSub
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) (A : Subobject (M : s.IntervalCat C a b)) : Subobject X :=
  Subobject.mk (A.arrow ≫ M.arrow)

private lemma intervalLiftSub_le
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) (A : Subobject (M : s.IntervalCat C a b)) :
    intervalLiftSub (C := C) (X := X) M A ≤ M := by
  have h := Subobject.mk_le_mk_of_comm A.arrow
    (show A.arrow ≫ M.arrow = A.arrow ≫ M.arrow from rfl)
  rwa [Subobject.mk_arrow] at h

private lemma intervalLiftSub_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) :
    intervalLiftSub (C := C) (X := X) M (⊥ : Subobject (M : s.IntervalCat C a b)) = ⊥ := by
  apply (Subobject.mk_eq_bot_iff_zero).mpr
  simp [intervalLiftSub, Subobject.bot_arrow]

private lemma intervalLiftSub_ne_bot
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) {A : Subobject (M : s.IntervalCat C a b)} (hA : A ≠ ⊥) :
    intervalLiftSub (C := C) (X := X) M A ≠ ⊥ := by
  intro h
  apply hA
  rw [← Subobject.mk_arrow A]
  apply (Subobject.mk_eq_bot_iff_zero).mpr
  apply (cancel_mono M.arrow).1
  simpa [intervalLiftSub, Subobject.mk_arrow] using
    (Subobject.mk_eq_bot_iff_zero.mp h)

private lemma intervalLiftSub_mono
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) {A B : Subobject (M : s.IntervalCat C a b)} (h : A ≤ B) :
    intervalLiftSub (C := C) (X := X) M A ≤ intervalLiftSub (C := C) (X := X) M B := by
  refine Subobject.mk_le_mk_of_comm (Subobject.ofLE A B h) ?_
  simp [intervalLiftSub, Category.assoc, Subobject.ofLE_arrow]

private lemma intervalLiftSub_lt
    {s : Slicing C} {a b : ℝ} {X : s.IntervalCat C a b}
    (M : Subobject X) {A : Subobject (M : s.IntervalCat C a b)} (hA : A ≠ ⊤) :
    intervalLiftSub (C := C) (X := X) M A < M := by
  refine lt_of_le_of_ne (intervalLiftSub_le (C := C) (X := X) M A) ?_
  intro hEq
  apply hA
  apply (Subobject.map_obj_injective M.arrow)
  rw [show (Subobject.map M.arrow).obj A = intervalLiftSub (C := C) (X := X) M A by
    simpa [intervalLiftSub] using (Subobject.map_mk A.arrow M.arrow)]
  rw [show (Subobject.map M.arrow).obj (⊤ : Subobject (M : s.IntervalCat C a b)) = M by
    simpa using (Subobject.map_top M.arrow)]
  exact hEq

private lemma intervalSubobject_bot_arrow_strictMono
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} :
    IsStrictMono ((⊥ : Subobject X).arrow) := by
  let f : ((⊥ : Subobject X) : s.IntervalCat C a b) ⟶ X := (⊥ : Subobject X).arrow
  have hzero : f = 0 := by simp [f, Subobject.bot_arrow]
  letI : IsIso (cokernel.π f) := by
    rw [hzero]
    infer_instance
  apply isStrictMono_of_isLimitKernelFork
  refine KernelFork.IsLimit.ofMonoOfIsZero
    (KernelFork.ofι f (cokernel.condition f)) inferInstance ?_
  exact (isZero_zero (s.IntervalCat C a b)).of_iso Subobject.botCoeIsoZero

private lemma intervalLiftSub_arrow_strictMono_of_strictMono
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    (hM : IsStrictMono M.arrow) {A : Subobject (M : s.IntervalCat C a b)}
    (hA : IsStrictMono A.arrow) :
    IsStrictMono (intervalLiftSub (C := C) (X := X) M A).arrow := by
  have hcomp : IsStrictMono (A.arrow ≫ M.arrow) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := s) (a := a) (b := b) A.arrow M.arrow hA hM
  simpa [intervalLiftSub] using
    (intervalSubobject_arrow_strictMono_of_strictMono
      (C := C) (s := s) (a := a) (b := b) (A.arrow ≫ M.arrow) hcomp)

private lemma intervalLiftSub_wPhase_eq
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    {X : s.IntervalCat C a b} (M : Subobject X)
    (A : Subobject (M : s.IntervalCat C a b)) :
    wPhaseOf
        (ssf.W
          (K₀.of C (((intervalLiftSub (C := C) (X := X) M A : Subobject X) :
            s.IntervalCat C a b).obj))) ssf.α =
      wPhaseOf (ssf.W (K₀.of C ((A : s.IntervalCat C a b).obj))) ssf.α := by
  let eI :
      ((intervalLiftSub (C := C) (X := X) M A : Subobject X) : s.IntervalCat C a b) ≅
        (A : s.IntervalCat C a b) :=
    Subobject.underlyingIso (A.arrow ≫ M.arrow)
  let eC :
      (((intervalLiftSub (C := C) (X := X) M A : Subobject X) : s.IntervalCat C a b).obj) ≅
        (A : s.IntervalCat C a b).obj :=
    (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso eI
  simpa [eI, eC] using
    congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)

variable [IsTriangulated C] in
/-- A non-semistable thin-interval object contains a proper strict subobject of strictly larger
`W`-phase. This is the paper-faithful first step in Bridgeland's descent argument: the witness
is extracted directly from the failure of the semistability triangle test, not by finite
enumeration of subobjects. -/
private theorem SkewedStabilityFunction.exists_phase_gt_strictSubobject_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)) :
    ∃ B : Subobject X, B ≠ ⊥ ∧ B ≠ ⊤ ∧ IsStrictMono B.arrow ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hX_obj : ¬IsZero X.obj := by
    intro hZ
    exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hW_X : ssf.W (K₀.of C X.obj) ≠ 0 := hW_interval X.property hX_obj
  have htri :
      ¬ ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ X.obj⦄ ⦃f₂ : X.obj ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
          Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
          σ.slicing.intervalProp C a b K →
          σ.slicing.intervalProp C a b Q →
          ¬IsZero K →
          wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    intro hsem
    exact hns ⟨X.property, hX_obj, hW_X, rfl,
      fun {K Q} {f₁} {f₂} {f₃} hT hK hQ hKne ↦ hsem hT hK hQ hKne⟩
  push_neg at htri
  obtain ⟨K, Q, f₁, f₂, f₃, hT, hK, hQ, hKne, hgt⟩ := htri
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iKX : KI ⟶ X := ObjectProperty.homMk f₁
  let gXQ : X ⟶ QI := ObjectProperty.homMk f₂
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iKX gXQ (by
      ext
      simpa [iKX, gXQ] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT' : Triangle.mk S.f.hom S.g.hom f₃ ∈ distTriang C := by
    simpa [S, iKX, gXQ] using hT
  have hK_strict : IsStrictMono iKX :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b) hT').1
  letI : Mono iKX := hK_strict.mono
  let B : Subobject X := Subobject.mk iKX
  have hB_ne_bot : B ≠ ⊥ := by
    intro hB
    have hBZ : IsZero (B : σ.slicing.IntervalCat C a b) :=
      (intervalSubobject_isZero_iff_eq_bot
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) B).mpr hB
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero
      (hBZ.of_iso (Subobject.underlyingIso iKX).symm))
  have hB_strict : IsStrictMono B.arrow := by
    simpa [B] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) iKX hK_strict)
  have hB_ne_top : B ≠ ⊤ := by
    intro hB
    have hIsoK :
        phaseObj KI = phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) := by
      let eI :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) ≅ KI :=
        eqToIso (by
          simpa [B] using congrArg
            (fun Z : Subobject X => (Z : σ.slicing.IntervalCat C a b)) hB.symm) ≪≫
          Subobject.underlyingIso iKX
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
      simpa [phaseObj] using
        congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC).symm
    have hIsoTop :
        phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) = phaseObj X := by
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
      simpa [phaseObj] using
        congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
    have hEqPhase : phaseObj KI = phaseObj X := hIsoK.trans hIsoTop
    have : phaseObj X < phaseObj X := by
      simpa [phaseObj, KI] using hgt.trans_eq hEqPhase
    exact lt_irrefl _ this
  have hB_phase_eq :
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α =
        wPhaseOf (ssf.W (K₀.of C K)) ssf.α := by
    let eC :
        (B : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
      (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
        (Subobject.underlyingIso iKX)
    simpa [B, KI] using
      congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
  refine ⟨B, hB_ne_bot, hB_ne_top, hB_strict, ?_⟩
  rwa [hB_phase_eq]

private def intervalLiftSubCokernelIso
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)] {X : s.IntervalCat C a b}
    (M : Subobject X) {A B : Subobject (M : s.IntervalCat C a b)} (h : A ≤ B) :
    cokernel (Subobject.ofLE
      (intervalLiftSub (C := C) (X := X) M A) (intervalLiftSub (C := C) (X := X) M B)
      (intervalLiftSub_mono (C := C) (X := X) M h)) ≅
      cokernel (Subobject.ofLE A B h) := by
  let fLift := Subobject.ofLE
    (intervalLiftSub (C := C) (X := X) M A)
    (intervalLiftSub (C := C) (X := X) M B)
    (intervalLiftSub_mono (C := C) (X := X) M h)
  let fBase := Subobject.ofLE A B h
  let eA :
      ((intervalLiftSub (C := C) (X := X) M A : Subobject X) : s.IntervalCat C a b) ≅
        (A : s.IntervalCat C a b) := Subobject.underlyingIso (A.arrow ≫ M.arrow)
  let eB :
      ((intervalLiftSub (C := C) (X := X) M B : Subobject X) : s.IntervalCat C a b) ≅
        (B : s.IntervalCat C a b) := Subobject.underlyingIso (B.arrow ≫ M.arrow)
  have hwBase : fBase ≫ (B.arrow ≫ M.arrow) = A.arrow ≫ M.arrow := by
    simpa [fBase, Category.assoc] using
      congrArg (fun k => k ≫ M.arrow) (Subobject.ofLE_arrow h)
  have hArrow :
      fLift = eA.hom ≫ fBase ≫ eB.inv := by
    simpa [intervalLiftSub, eA, eB, Category.assoc] using
      (Subobject.ofLE_mk_le_mk_of_comm
        fBase
        hwBase :
          Subobject.ofLE
              (Subobject.mk (A.arrow ≫ M.arrow))
              (Subobject.mk (B.arrow ≫ M.arrow))
              (Subobject.mk_le_mk_of_comm (Subobject.ofLE A B h)
                hwBase) =
            (Subobject.underlyingIso (A.arrow ≫ M.arrow)).hom ≫
              fBase ≫
                (Subobject.underlyingIso (B.arrow ≫ M.arrow)).inv)
  have hw :
      fLift ≫ eB.hom = eA.hom ≫ fBase := by
    rw [hArrow]
    simp
  exact cokernel.mapIso (f := fLift) (f' := fBase) eA eB hw

variable [IsTriangulated C] in
/-- Among the proper strict kernels of a non-semistable interval object, there is one whose
strict quotient has minimal `W`-phase, and among those minimal-phase kernels we may choose one
that is maximal for inclusion. This is the quotient-recursion selection step for Phase 3. -/
private theorem SkewedStabilityFunction.exists_minPhase_maximal_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    [Finite (Subobject X)] :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → M < B →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) := by
  let phaseQ : Subobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hX_obj : ¬IsZero X.obj := by
    intro hZ
    exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hW_X : ssf.W (K₀.of C X.obj) ≠ 0 := hW_interval X.property hX_obj
  have htri :
      ¬ ∀ ⦃K Q : C⦄ ⦃f₁ : K ⟶ X.obj⦄ ⦃f₂ : X.obj ⟶ Q⦄ ⦃f₃ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
          Triangle.mk f₁ f₂ f₃ ∈ distTriang C →
          σ.slicing.intervalProp C a b K →
          σ.slicing.intervalProp C a b Q →
          ¬IsZero K →
          wPhaseOf (ssf.W (K₀.of C K)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    intro hsem
    exact hns ⟨X.property, hX_obj, hW_X, rfl,
      fun {K Q} {f₁} {f₂} {f₃} hT hK hQ hKne ↦ hsem hT hK hQ hKne⟩
  push_neg at htri
  obtain ⟨K, Q, f₁, f₂, f₃, hT, hK, hQ, hKne, hgt⟩ := htri
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iKX : KI ⟶ X := ObjectProperty.homMk f₁
  let gXQ : X ⟶ QI := ObjectProperty.homMk f₂
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iKX gXQ (by
      ext
      simpa [iKX, gXQ] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT' : Triangle.mk S.f.hom S.g.hom f₃ ∈ distTriang C := by
    simpa [S, iKX, gXQ] using hT
  have hK_strict : IsStrictMono iKX :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b) hT').1
  letI : Mono iKX := hK_strict.mono
  let B : Subobject X := Subobject.mk iKX
  have hB_strict : IsStrictMono B.arrow := by
    simpa [B] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) iKX hK_strict)
  have hB_ne_top : B ≠ ⊤ := by
    intro hB
    have hIsoK :
        phaseObj KI = phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) := by
      let eI :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) ≅ KI :=
        eqToIso (by
          simpa [B] using congrArg
            (fun Z : Subobject X => (Z : σ.slicing.IntervalCat C a b)) hB.symm) ≪≫
          Subobject.underlyingIso iKX
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
      simpa [phaseObj] using
        congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC).symm
    have hIsoTop :
        phaseObj ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b) = phaseObj X := by
      let eC :
          ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
      simpa [phaseObj] using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
    have hEqPhase : phaseObj KI = phaseObj X := hIsoK.trans hIsoTop
    have hEqPhase' :
        wPhaseOf (ssf.W (K₀.of C K)) ssf.α =
          wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
      simpa [phaseObj, KI] using hEqPhase
    have : wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
      simpa [hEqPhase'] using hgt
    exact lt_irrefl _ this
  let T : Set (Subobject X) := {B | B ≠ ⊤ ∧ IsStrictMono B.arrow}
  have hT_ne : T.Nonempty := ⟨B, hB_ne_top, hB_strict⟩
  have hT_fin : T.Finite := Set.toFinite _
  obtain ⟨M₀, hM₀T, hM₀min⟩ := Set.exists_min_image T phaseQ hT_fin hT_ne
  let S : Set (Subobject X) := {B | B ∈ T ∧ phaseQ B = phaseQ M₀}
  have hS_ne : S.Nonempty := ⟨M₀, hM₀T, rfl⟩
  have hS_fin : S.Finite := Set.toFinite _
  obtain ⟨M, ⟨hMT, hM_phase⟩, hM_max⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨M, hMT.1, hMT.2, ?_, ?_⟩
  · intro B hB hB_strict
    change phaseQ M ≤ phaseQ B
    rw [hM_phase]
    exact hM₀min B ⟨hB, hB_strict⟩
  · intro B hB hB_strict hMB
    have hBT : B ∈ T := ⟨hB, hB_strict⟩
    have hle : phaseQ M ≤ phaseQ B := by
      rw [hM_phase]
      exact hM₀min B hBT
    exact lt_of_le_of_ne hle (fun hEq ↦
      absurd (hM_max ⟨hBT, hEq.symm.trans hM_phase⟩ hMB.le) (not_le_of_gt hMB))

variable [IsTriangulated C] in
/-- Among the proper strict kernels of a non-semistable interval object, there is one whose
strict quotient has minimal `W`-phase, and among the kernels achieving that minimal quotient
phase we may choose one that is minimal for inclusion. This is the mdq-oriented selection
step needed to force strict phase drop in the kernel recursion. -/
private theorem SkewedStabilityFunction.exists_minPhase_minimal_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    [Finite (Subobject X)] :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) ∧
      (∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → B < M →
        wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) := by
  let phaseQ : Subobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α
  obtain ⟨M₀, hM₀_top, hM₀_strict, hM₀_min, _⟩ :=
    ssf.exists_minPhase_maximal_strictKernel
      (C := C) (σ := σ) (a := a) (b := b) hX hW_interval hns
  let T : Set (Subobject X) := {B | B ≠ ⊤ ∧ IsStrictMono B.arrow}
  let S : Set (Subobject X) := {B | B ∈ T ∧ phaseQ B = phaseQ M₀}
  have hS_ne : S.Nonempty := ⟨M₀, ⟨hM₀_top, hM₀_strict⟩, rfl⟩
  have hS_fin : S.Finite := Set.toFinite _
  obtain ⟨M, ⟨hMT, hM_phase⟩, hM_min⟩ := hS_fin.exists_minimal hS_ne
  refine ⟨M, hMT.1, hMT.2, ?_, ?_⟩
  · intro B hB hB_strict
    change phaseQ M ≤ phaseQ B
    rw [hM_phase]
    exact hM₀_min B hB hB_strict
  · intro B hB hB_strict hBM
    have hBT : B ∈ T := ⟨hB, hB_strict⟩
    have hle : phaseQ M ≤ phaseQ B := by
      rw [hM_phase]
      exact hM₀_min B hB hB_strict
    exact lt_of_le_of_ne hle (fun hEq ↦
      absurd (hM_min ⟨hBT, hEq.symm.trans hM_phase⟩ hBM.le) (not_le_of_gt hBM))

variable [IsTriangulated C] in
/-- Among the nonzero strict subobjects of a thin-interval object, there is one with maximal
W-phase, and among those maximal-phase candidates we may choose one that is maximal for
inclusion. This is the strict-subobject selection step needed for the thin-interval HN
recursion. -/
private theorem SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject_of_finite
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hT_fin : Set.Finite {B : Subobject X | B ≠ ⊥ ∧ IsStrictMono B.arrow}) :
    ∃ M : Subobject X, M ≠ ⊥ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      (∀ B : Subobject X, IsStrictMono B.arrow → M < B →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) := by
  let phase : Subobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α
  let T : Set (Subobject X) := {B | B ≠ ⊥ ∧ IsStrictMono B.arrow}
  have hT_ne : T.Nonempty := by
    refine ⟨⊤,
      intervalSubobject_top_ne_bot_of_not_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hX, ?_⟩
    exact isStrictMono_of_isIso
  have hT_fin' : T.Finite := by
    simpa [T] using hT_fin
  obtain ⟨M₀, hM₀T, hM₀max⟩ := Set.exists_max_image T phase hT_fin' hT_ne
  let S : Set (Subobject X) := {B | B ∈ T ∧ phase B = phase M₀}
  have hS_ne : S.Nonempty := ⟨M₀, hM₀T, rfl⟩
  have hS_fin : S.Finite := hT_fin'.subset (by
    intro B hB
    exact hB.1)
  obtain ⟨M, ⟨hMT, hM_phase⟩, hM_max⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨M, hMT.1, hMT.2, ?_, ?_⟩
  · intro B hB hBstrict
    change phase B ≤ phase M
    rw [hM_phase]
    exact hM₀max B ⟨hB, hBstrict⟩
  · intro B hBstrict hMB
    have hBT : B ∈ T := ⟨ne_bot_of_gt hMB, hBstrict⟩
    have hle : phase B ≤ phase M := by
      rw [hM_phase]
      exact hM₀max B hBT
    change phase B < phase M
    exact lt_of_le_of_ne hle (fun hEq ↦
      absurd (hM_max ⟨hBT, hEq.trans hM_phase⟩ hMB.le) (not_le_of_gt hMB))

variable [IsTriangulated C] in
/-- Among the nonzero strict subobjects of a thin-interval object, there is one with maximal
W-phase, and among those maximal-phase candidates we may choose one that is maximal for
inclusion. This is the strict-subobject selection step needed for the thin-interval HN
recursion. -/
private theorem SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    [Finite (Subobject X)] :
    ∃ M : Subobject X, M ≠ ⊥ ∧ IsStrictMono M.arrow ∧
      (∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      (∀ B : Subobject X, IsStrictMono B.arrow → M < B →
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) := by
  exact ssf.exists_maxPhase_maximal_strictSubobject_of_finite
    (C := C) (σ := σ) (a := a) (b := b) (X := X) hX (Set.toFinite _)

variable [IsTriangulated C] in
/-- A nonzero strict subobject that is maximal for W-phase among all nonzero strict subobjects
is W-semistable. -/
private theorem SkewedStabilityFunction.semistable_of_maxPhase_strictSubobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
      (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) := by
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hMint_ne : ¬IsZero (M : σ.slicing.IntervalCat C a b) :=
    intervalSubobject_not_isZero_of_ne_bot (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne
  have hMobj_ne : ¬IsZero (M : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact hMint_ne <|
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  refine ⟨(M : σ.slicing.IntervalCat C a b).property, hMobj_ne,
    hW_interval (M : σ.slicing.IntervalCat C a b).property hMobj_ne, rfl, ?_⟩
  intro K Q f₁ f₂ f₃ hT hK hQ hKne
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iKM : KI ⟶ (M : σ.slicing.IntervalCat C a b) := ObjectProperty.homMk f₁
  let gMQ : (M : σ.slicing.IntervalCat C a b) ⟶ QI := ObjectProperty.homMk f₂
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iKM gMQ (by
      ext
      simpa [iKM, gMQ] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT' : Triangle.mk S.f.hom S.g.hom f₃ ∈ distTriang C := by
    simpa [S, iKM, gMQ] using hT
  have hK_strict : IsStrictMono iKM :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b) hT').1
  have hComp_strict : IsStrictMono (iKM ≫ M.arrow) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) iKM M.arrow hK_strict hM_strict
  haveI : Mono (iKM ≫ M.arrow) := hComp_strict.mono
  let B : Subobject X := Subobject.mk (iKM ≫ M.arrow)
  have hKI_ne : ¬IsZero KI := by
    intro hZ
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  have hB_ne : B ≠ ⊥ := by
    intro hB
    have hzero : iKM ≫ M.arrow = 0 := by
      exact (Subobject.mk_eq_bot_iff_zero).mp (show Subobject.mk (iKM ≫ M.arrow) = ⊥ by simpa [B] using hB)
    have hId : 𝟙 KI = 0 := by
      apply (cancel_mono (iKM ≫ M.arrow)).1
      simpa [hzero]
    exact hKI_ne ((IsZero.iff_id_eq_zero KI).mpr hId)
  have hB_strict : IsStrictMono B.arrow := by
    let e := Subobject.underlyingIso (iKM ≫ M.arrow)
    have he_strict : IsStrictMono e.hom := isStrictMono_of_isIso
    have htmp : IsStrictMono (e.hom ≫ (iKM ≫ M.arrow)) :=
      Slicing.IntervalCat.comp_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) e.hom (iKM ≫ M.arrow) he_strict hComp_strict
    have hArrow : e.hom ≫ (iKM ≫ M.arrow) = B.arrow := by
      simpa [e, B, Category.assoc] using
        (Subobject.underlyingIso_hom_comp_eq_mk (iKM ≫ M.arrow))
    rw [← hArrow]
    exact htmp
  have hPhaseB : phaseObj KI ≤ phaseObj (M : σ.slicing.IntervalCat C a b) := by
    have hPhaseSub : phaseObj (B : σ.slicing.IntervalCat C a b) ≤
        phaseObj (M : σ.slicing.IntervalCat C a b) :=
      hM_max B hB_ne hB_strict
    have hIsoK :
        phaseObj KI = phaseObj (B : σ.slicing.IntervalCat C a b) := by
      let eC : (B : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (Subobject.underlyingIso (iKM ≫ M.arrow))
      simpa [phaseObj] using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α)
        (K₀.of_iso C eC).symm
    exact hIsoK.trans_le hPhaseSub
  simpa [phaseObj, KI]
    using hPhaseB

/-! ### Thin-interval pullback infrastructure -/

private theorem interval_pullbackπ_strictEpi_of_strictEpi
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (p : X ⟶ Y) (hp : IsStrictEpi p)
    (B : Subobject Y) :
    IsStrictEpi (Subobject.pullbackπ p B) := by
  letI := s.intervalCat_quasiAbelian (C := C) (a := a) (b := b)
  let e := (Subobject.isPullback p B).isoPullback
  have hpb : IsStrictEpi (pullback.fst B.arrow p) :=
    QuasiAbelian.pullback_strictEpi B.arrow p hp
  have he : e.hom ≫ pullback.fst B.arrow p = Subobject.pullbackπ p B := by
    simpa [e] using (Subobject.isPullback p B).isoPullback_hom_fst
  have hcomp : IsStrictEpi (e.hom ≫ pullback.fst B.arrow p) :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := s) (a := a) (b := b) e.hom (pullback.fst B.arrow p)
      isStrictEpi_of_isIso hpb
  simpa [he] using hcomp

private theorem interval_pullback_arrow_strictMono_of_strictMono
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (p : X ⟶ Y)
    (B : Subobject Y) (hB : IsStrictMono B.arrow) :
    IsStrictMono (((Subobject.pullback p).obj B).arrow) := by
  let pb := (Subobject.pullback p).obj B
  let sq := Subobject.isPullback p B
  let hKerB := hB.isLimitKernelFork
  letI : NormalMono pb.arrow :=
    { Z := cokernel B.arrow
      g := p ≫ cokernel.π B.arrow
      w := by
        calc
          pb.arrow ≫ (p ≫ cokernel.π B.arrow)
              = (pb.arrow ≫ p) ≫ cokernel.π B.arrow := by simp [Category.assoc]
          _ = (Subobject.pullbackπ p B ≫ B.arrow) ≫ cokernel.π B.arrow := by
              rw [sq.w]
          _ = Subobject.pullbackπ p B ≫ (B.arrow ≫ cokernel.π B.arrow) := by
              simp [Category.assoc]
          _ = 0 := by simp
      isLimit := KernelFork.IsLimit.ofι' pb.arrow
        (by
          calc
            pb.arrow ≫ (p ≫ cokernel.π B.arrow)
                = (pb.arrow ≫ p) ≫ cokernel.π B.arrow := by simp [Category.assoc]
            _ = (Subobject.pullbackπ p B ≫ B.arrow) ≫ cokernel.π B.arrow := by
                rw [sq.w]
            _ = Subobject.pullbackπ p B ≫ (B.arrow ≫ cokernel.π B.arrow) := by
                simp [Category.assoc]
            _ = 0 := by simp)
        (fun {W} g hg ↦ by
          let u : W ⟶ (B : s.IntervalCat C a b) :=
            hKerB.lift (KernelFork.ofι (g ≫ p) (by simpa [Category.assoc] using hg))
          have hu : u ≫ B.arrow = g ≫ p := by
            exact hKerB.fac _ Limits.WalkingParallelPair.zero
          exact ⟨sq.lift u g hu, by simpa [pb] using sq.lift_snd u g hu⟩) }
  exact isStrictMono_of_normalMono

private lemma interval_le_pullback_cokernel
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X)
    (B : Subobject (cokernel M.arrow)) :
    M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  let sq := Subobject.isPullback q B
  refine Subobject.le_of_comm (sq.lift 0 M.arrow (by simpa [q] using cokernel.condition M.arrow)) ?_
  simpa [pbB] using sq.lift_snd 0 M.arrow (by simpa [q] using cokernel.condition M.arrow)

private lemma interval_ofLE_pullbackπ_eq_zero
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X)
    (B : Subobject (cokernel M.arrow)) :
    Subobject.ofLE M _ (interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B) ≫
      Subobject.pullbackπ (cokernel.π M.arrow) B = 0 := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  let hle := interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
  let sq := Subobject.isPullback q B
  apply (cancel_mono B.arrow).mp
  calc
    (Subobject.ofLE M pbB hle ≫ Subobject.pullbackπ q B) ≫ B.arrow
        = Subobject.ofLE M pbB hle ≫ (pbB.arrow ≫ q) := by
            rw [Category.assoc, sq.w]
    _ = (Subobject.ofLE M pbB hle ≫ pbB.arrow) ≫ q := by simp [Category.assoc]
    _ = M.arrow ≫ q := by rw [Subobject.ofLE_arrow]
    _ = 0 ≫ B.arrow := by
          rw [show M.arrow ≫ q = 0 by simpa [q] using cokernel.condition M.arrow]
          simp

private theorem interval_strictShortExact_of_kernel_strictEpi
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (S : ShortComplex (s.IntervalCat C a b))
    (hKer : IsLimit (KernelFork.ofι S.f S.zero))
    (hg : IsStrictEpi S.g) :
    StrictShortExact S := by
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKer
  have hEpiL : Epi ((S.map FL).g) := by
    simpa [FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) S.g hg
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExactL : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
  have hShortExactL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExactL (Fork.IsLimit.mono hKerL) hEpiL
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hShortExactL
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT

private theorem interval_strictShortExact_pullback_left
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {K E Q : s.IntervalCat C a b}
    {i : K ⟶ E} {q : E ⟶ Q}
    (hiq : i ≫ q = 0)
    (hKer : IsLimit (KernelFork.ofι i hiq))
    (hq : IsStrictEpi q)
    (B : Subobject Q) :
    let pb := (Subobject.pullback q).obj B
    let m : K ⟶ pb := by
      let hiB : B.Factors (i ≫ q) := by
        simpa [hiq] using (Subobject.factors_zero : B.Factors (0 : K ⟶ Q))
      exact pb.factorThru i (Limits.pullback_factors q B i hiB)
    StrictShortExact
      (ShortComplex.mk m (Subobject.pullbackπ q B) (by
        apply (cancel_mono B.arrow).mp
        calc
          (m ≫ Subobject.pullbackπ q B) ≫ B.arrow
              = m ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by simp [Category.assoc]
          _ = m ≫ (((Subobject.pullback q).obj B).arrow ≫ q) := by
              rw [(Subobject.isPullback q B).w]
          _ = (m ≫ ((Subobject.pullback q).obj B).arrow) ≫ q := by simp [Category.assoc]
          _ = i ≫ q := by
              let hiB : B.Factors (i ≫ q) := by
                simpa [hiq] using (Subobject.factors_zero : B.Factors (0 : K ⟶ Q))
              change
                (((Subobject.pullback q).obj B).factorThru i (Limits.pullback_factors q B i hiB) ≫
                    ((Subobject.pullback q).obj B).arrow) ≫ q =
                  i ≫ q
              simpa [Category.assoc] using
                congrArg (fun t ↦ t ≫ q)
                  (Subobject.factorThru_arrow ((Subobject.pullback q).obj B) i
                    (Limits.pullback_factors q B i hiB))
          _ = 0 := hiq
          _ = 0 ≫ B.arrow := by simp)) := by
  let pb := (Subobject.pullback q).obj B
  let hiB : B.Factors (i ≫ q) := by
    simpa [hiq] using (Subobject.factors_zero : B.Factors (0 : K ⟶ Q))
  let hpb : pb.Factors i := Limits.pullback_factors q B i hiB
  let m : K ⟶ pb := by
    exact pb.factorThru i hpb
  have hm : m ≫ pb.arrow = i := by
    change pb.factorThru i hpb ≫ pb.arrow = i
    exact Subobject.factorThru_arrow pb i hpb
  let hcomp : m ≫ Subobject.pullbackπ q B = 0 := by
    apply (cancel_mono B.arrow).mp
    calc
      (m ≫ Subobject.pullbackπ q B) ≫ B.arrow
          = m ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by simp [Category.assoc]
      _ = m ≫ (pb.arrow ≫ q) := by rw [(Subobject.isPullback q B).w]
      _ = (m ≫ pb.arrow) ≫ q := by simp [Category.assoc]
      _ = i ≫ q := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ q) hm
      _ = 0 := hiq
      _ = 0 ≫ B.arrow := by simp
  haveI : Mono i := Fork.IsLimit.mono hKer
  haveI : Mono m := mono_of_mono_fac hm
  have hKer' : IsLimit (KernelFork.ofι m hcomp) := by
    refine KernelFork.IsLimit.ofι' m hcomp (fun {W} g hg ↦ ?_)
    let u : W ⟶ K :=
      hKer.lift (KernelFork.ofι (g ≫ pb.arrow) (by
        calc
          (g ≫ pb.arrow) ≫ q = g ≫ (pb.arrow ≫ q) := by simp [Category.assoc]
          _ = g ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by rw [(Subobject.isPullback q B).w]
          _ = (g ≫ Subobject.pullbackπ q B) ≫ B.arrow := by simp [Category.assoc]
          _ = 0 := by simp [hg]))
    have hu : u ≫ i = g ≫ pb.arrow := by
      exact hKer.fac _ Limits.WalkingParallelPair.zero
    refine ⟨u, ?_⟩
    apply (cancel_mono pb.arrow).1
    calc
      (u ≫ m) ≫ pb.arrow = u ≫ i := by
        simp [Category.assoc, hm]
      _ = g ≫ pb.arrow := hu
  have hπ : IsStrictEpi (Subobject.pullbackπ q B) :=
    interval_pullbackπ_strictEpi_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) q hq B
  exact interval_strictShortExact_of_kernel_strictEpi
    (C := C) (s := s) (a := a) (b := b)
    (ShortComplex.mk m (Subobject.pullbackπ q B) hcomp) hKer' hπ

private theorem interval_strictShortExact_pullback_right
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {E Q Y : s.IntervalCat C a b}
    (q : E ⟶ Q) (hq : IsStrictEpi q)
    (B : Subobject Q)
    (g : Q ⟶ Y) (hBg : B.arrow ≫ g = 0)
    (hBKer : IsLimit (KernelFork.ofι B.arrow hBg))
    (hg : IsStrictEpi g) :
    let pb := (Subobject.pullback q).obj B
    let p : E ⟶ Y := q ≫ g
    StrictShortExact
      (ShortComplex.mk pb.arrow p (by
        calc
          pb.arrow ≫ p = pb.arrow ≫ q ≫ g := by simp [p, Category.assoc]
          _ = (pb.arrow ≫ q) ≫ g := by simp [Category.assoc]
          _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ g := by
              rw [(Subobject.isPullback q B).w]
          _ = Subobject.pullbackπ q B ≫ B.arrow ≫ g := by simp [Category.assoc]
          _ = 0 := by simp [hBg, Category.assoc])) := by
  let pb := (Subobject.pullback q).obj B
  let p : E ⟶ Y := q ≫ g
  let hcomp : pb.arrow ≫ p = 0 := by
    calc
      pb.arrow ≫ p = pb.arrow ≫ q ≫ g := by simp [p, Category.assoc]
      _ = (pb.arrow ≫ q) ≫ g := by simp [Category.assoc]
      _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ g := by
          rw [(Subobject.isPullback q B).w]
      _ = Subobject.pullbackπ q B ≫ B.arrow ≫ g := by simp [Category.assoc]
      _ = 0 := by simp [hBg, Category.assoc]
  have hKer : IsLimit (KernelFork.ofι pb.arrow hcomp) := by
    refine KernelFork.IsLimit.ofι' pb.arrow hcomp (fun {W} k hk ↦ ?_)
    let u : W ⟶ (B : s.IntervalCat C a b) :=
      hBKer.lift (KernelFork.ofι (k ≫ q) (by
        simpa [p, Category.assoc] using hk))
    have hu : u ≫ B.arrow = k ≫ q := by
      exact hBKer.fac _ Limits.WalkingParallelPair.zero
    refine ⟨(Subobject.isPullback q B).lift u k hu, ?_⟩
    simpa [pb] using (Subobject.isPullback q B).lift_snd u k hu
  have hp : IsStrictEpi p :=
    Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := s) (a := a) (b := b) q g hq hg
  exact interval_strictShortExact_of_kernel_strictEpi
    (C := C) (s := s) (a := a) (b := b)
    (ShortComplex.mk pb.arrow p hcomp) hKer hp

private theorem interval_strictShortExact_ofLE_pullbackπ_cokernel
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    (B : Subobject (cokernel M.arrow)) :
    let pbB := (Subobject.pullback (cokernel.π M.arrow)).obj B
    let hle := interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
    StrictShortExact
      (ShortComplex.mk
        (Subobject.ofLE M pbB hle)
        (Subobject.pullbackπ (cokernel.π M.arrow) B)
        (interval_ofLE_pullbackπ_eq_zero (C := C) (s := s) (a := a) (b := b) M B)) := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  let hle := interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
  let hcomp := interval_ofLE_pullbackπ_eq_zero (C := C) (s := s) (a := a) (b := b) M B
  let i := Subobject.ofLE M pbB hle
  let π := Subobject.pullbackπ q B
  have hq : IsStrictEpi q := isStrictEpi_cokernel M.arrow
  have hπ : IsStrictEpi π :=
    interval_pullbackπ_strictEpi_of_strictEpi
      (C := C) (s := s) (a := a) (b := b) q hq B
  have hkey : ∀ {W : s.IntervalCat C a b} (g : W ⟶ pbB), g ≫ π = 0 →
      (g ≫ pbB.arrow) ≫ q = 0 := by
    intro W g hg
    calc
      (g ≫ pbB.arrow) ≫ q = g ≫ (pbB.arrow ≫ q) := by simp [Category.assoc]
      _ = g ≫ (π ≫ B.arrow) := by rw [(Subobject.isPullback q B).w]
      _ = (g ≫ π) ≫ B.arrow := by simp [Category.assoc]
      _ = 0 := by simp [hg]
  have hKer : IsLimit (KernelFork.ofι i hcomp) := by
    refine KernelFork.IsLimit.ofι' i hcomp (fun {W} g hg ↦ ?_)
    let k : W ⟶ (M : s.IntervalCat C a b) :=
      hM.isLimitKernelFork.lift (KernelFork.ofι (g ≫ pbB.arrow) (hkey g hg))
    have hk : k ≫ M.arrow = g ≫ pbB.arrow := by
      exact hM.isLimitKernelFork.fac _ Limits.WalkingParallelPair.zero
    refine ⟨k, ?_⟩
    apply (cancel_mono pbB.arrow).1
    simpa [i, Category.assoc, Subobject.ofLE_arrow] using hk
  let S : ShortComplex (s.IntervalCat C a b) := ShortComplex.mk i π hcomp
  let t := (s.phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    CategoryTheory.categoryWithHomology_of_abelian (C := t.heart.FullSubcategory)
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have hKerL :
      IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKer
  have hEpiL : Epi ((S.map FL).g) := by
    simpa [S, FL] using
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) π hπ
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExactL : (S.map FL).Exact := ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKerL
  have hShortExactL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExactL (Fork.IsLimit.mono hKerL) hEpiL
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
    (C := C) (s := s) (a := a) (b := b) hShortExactL
  exact Slicing.IntervalCat.strictShortExact_of_distTriang
    (C := C) (s := s) (a := a) (b := b) hT

private noncomputable def interval_fIsKernel_of_strictShortExact
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {S : ShortComplex (s.IntervalCat C a b)} (hS : StrictShortExact S) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  let tR := (s.phaseShift C (b - 1)).toTStructureGE
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := tR.heartFullSubcategoryAbelian
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have := hS.shortExact.mono_f
  have := hS.shortExact.epi_g
  let h := hS.shortExact.exact.condition.choose
  let eHi : kernel S.g ≅ h.left.K :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.left.hi
  have heHi : eHi.inv ≫ kernel.ι S.g = h.left.i := by
    simpa [KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) h.left.hi
        Limits.WalkingParallelPair.zero
  haveI : Epi h.left.f' := hS.shortExact.exact.epi_f' h.left
  have hFRMono : Mono (FR.map h.left.f') := by
    haveI : Mono (FR.map S.f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) S.f
        ⟨inferInstance, hS.strict_f⟩
    have hFRComp : FR.map h.left.f' ≫ FR.map h.left.i = FR.map S.f := by
      calc
        FR.map h.left.f' ≫ FR.map h.left.i = FR.map (h.left.f' ≫ h.left.i) := by
          rw [← FR.map_comp]
        _ = FR.map S.f := by
          simp [h.left.f'_i]
    haveI : Mono (FR.map h.left.f' ≫ FR.map h.left.i) := by
      rw [hFRComp]
      infer_instance
    exact mono_of_mono (FR.map h.left.f') (FR.map h.left.i)
  have hf'Strict : IsStrictMono h.left.f' :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart
      (C := C) (s := s) (a := a) (b := b) h.left.f'
  haveI : IsIso h.left.f' := hf'Strict.isIso
  let eK : S.X₁ ≅ kernel S.g := asIso h.left.f' ≪≫ eHi.symm
  refine kernel.isoKernel S.g S.f eK ?_
  calc
    eK.hom ≫ kernel.ι S.g = h.left.f' ≫ h.left.i := by
        simp [eK, heHi, Category.assoc]
    _ = S.f := h.left.f'_i

private noncomputable def interval_cokernel_pullbackTopIso
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X)
    {B : Subobject (cokernel M.arrow)} (hB : IsStrictMono B.arrow) :
    cokernel ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow ≅ cokernel B.arrow := by
  let q : X ⟶ cokernel M.arrow := cokernel.π M.arrow
  let pb : Subobject X := (Subobject.pullback q).obj B
  let p : X ⟶ cokernel B.arrow := q ≫ cokernel.π B.arrow
  let hcomp : pb.arrow ≫ p = 0 := by
    calc
      pb.arrow ≫ p = pb.arrow ≫ q ≫ cokernel.π B.arrow := by simp [p]
      _ = (pb.arrow ≫ q) ≫ cokernel.π B.arrow := by simp [Category.assoc]
      _ = (Subobject.pullbackπ q B ≫ B.arrow) ≫ cokernel.π B.arrow := by
          rw [(Subobject.isPullback q B).w]
      _ = Subobject.pullbackπ q B ≫ (B.arrow ≫ cokernel.π B.arrow) := by
          simp [Category.assoc]
      _ = 0 := by simp
  let S : ShortComplex (s.IntervalCat C a b) := ShortComplex.mk pb.arrow p hcomp
  have hS : StrictShortExact S := by
    simpa [S, pb, p, hcomp] using
      interval_strictShortExact_pullback_right
        (C := C) (s := s) (a := a) (b := b)
        q (isStrictEpi_cokernel M.arrow) B (cokernel.π B.arrow) (cokernel.condition B.arrow)
        hB.isLimitKernelFork (isStrictEpi_cokernel B.arrow)
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    interval_fIsKernel_of_strictShortExact
      (C := C) (s := s) (a := a) (b := b) hS
  have hp : IsStrictEpi p := ⟨hS.shortExact.epi_g, hS.strict_g⟩
  let eK' : kernel p ≅ (pb : s.IntervalCat C a b) :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel p) hKer
  let eK : (pb : s.IntervalCat C a b) ≅ kernel p := eK'.symm
  have heK : eK.hom ≫ kernel.ι p = pb.arrow := by
    simpa [S, p, KernelFork.ofι] using
      IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel p) hKer
        Limits.WalkingParallelPair.zero
  let eC : cokernel pb.arrow ≅ cokernel (kernel.ι p) :=
    cokernel.mapIso pb.arrow (kernel.ι p) eK (Iso.refl _)
      (by simpa [heK])
  let eQ : cokernel (kernel.ι p) ≅ cokernel B.arrow :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι p))
      hp.isColimitCokernelCofork
  exact eC ≪≫ eQ

private theorem semistable_of_upper_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a b₁ b₂ ψ ε₀ : ℝ} (hab₁ : a < b₁) (hab₂ : a < b₂) (hb : b₁ ≤ b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin₂ : b₂ - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  have hEI₂ : σ.slicing.intervalProp C a b₂ E :=
    σ.slicing.intervalProp_mono C (show a ≤ a by linarith) hb hSS.1
  have henv_hi₂ : ψ ≤ b₂ - ε₀ := by
    linarith
  have hb₁_le : b₁ ≤ a + 1 := by
    linarith
  have hthin₂' : b₂ - a < 1 := by
    linarith
  have hsmall₂ :
      stabSeminorm C σ (W - σ.Z) <
        ENNReal.ofReal (Real.cos (Real.pi * (b₂ - a) / 2)) :=
    stabSeminorm_lt_cos_of_hsin_hthin
      (C := C) (σ := σ) (W := W) hab₂ hε₀ hε₀2 hthin₂ hsin
  let hpert₂ := hperturb_of_stabSeminorm C σ W hW hthin₂' hε₀ hε₀2 hsin
  have hW_ne₂ :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₂ → W (K₀.of C F) ≠ 0 := by
    intro F φ hP hFne _ _
    exact σ.W_ne_zero_of_seminorm_lt_one C W hW hP hFne
  have hpert₂_lo :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₂ →
        a - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) < a - ε₀ + 1 := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert₂ F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hpert₂_hi :
      ∀ (F : C) (φ : ℝ), (σ.slicing.P φ) F → ¬IsZero F →
        a < φ → φ < b₂ →
        b₂ + ε₀ - 1 < wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b₂) / 2) < b₂ + ε₀ := by
    intro F φ hP hFne haφ hφb
    obtain ⟨hlo, hhi⟩ := hpert₂ F φ hP hFne haφ hφb
    exact ⟨by linarith, by linarith⟩
  have hWindow₂ :
      ∀ {G : C}, σ.slicing.intervalProp C a b₂ G → ¬IsZero G →
        a - ε₀ < wPhaseOf (W (K₀.of C G)) ((a + b₂) / 2) ∧
          wPhaseOf (W (K₀.of C G)) ((a + b₂) / 2) < b₂ + ε₀ := by
    intro G hG hGne
    exact ⟨wPhaseOf_gt_of_intervalProp C σ hGne W (by linarith) hG hW_ne₂ hpert₂_lo,
      wPhaseOf_lt_of_intervalProp C σ hGne W (by linarith) hG hW_ne₂ hpert₂_hi⟩
  have hW_ne_big :
      ∀ {G : C}, σ.slicing.intervalProp C a b₂ G → ¬IsZero G → W (K₀.of C G) ≠ 0 := by
    intro G hG hGne
    exact σ.W_ne_zero_of_intervalProp C W hthin₂' hsmall₂ hGne hG
  refine semistable_of_target_envelope_triangleTest
    (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hSS hab₂ hEI₂ hε₀ henv_lo henv_hi₂
    hthin₂ ?_
  intro K Q f₁ f₂ f₃ hT hKI hQI hKne
  letI : Fact (a < b₂) := ⟨hab₂⟩
  letI : Fact (b₂ - a ≤ 1) := ⟨by linarith⟩
  let KI₂ : σ.slicing.IntervalCat C a b₂ := ⟨K, hKI⟩
  let EI₂ : σ.slicing.IntervalCat C a b₂ := ⟨E, hEI₂⟩
  let QI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Q, hQI⟩
  let iK : KI₂ ⟶ EI₂ := ObjectProperty.homMk f₁
  let qE : EI₂ ⟶ QI₂ := ObjectProperty.homMk f₂
  let hcomp₀ : iK ≫ qE = 0 := by
    ext
    simpa [iK, qE] using comp_distTriang_mor_zero₁₂ _ hT
  let S₀ : ShortComplex (σ.slicing.IntervalCat C a b₂) := ShortComplex.mk iK qE hcomp₀
  have hT₀ : Triangle.mk S₀.f.hom S₀.g.hom f₃ ∈ distTriang C := by
    simpa [S₀, iK, qE] using hT
  have hS₀ : StrictShortExact S₀ :=
    Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b₂) hT₀
  have hS₀Ker : IsLimit (KernelFork.ofι iK hcomp₀) := by
    simpa [S₀] using
      interval_fIsKernel_of_strictShortExact
        (C := C) (s := σ.slicing) (a := a) (b := b₂) hS₀
  obtain ⟨X, Y, fX, gY, δY, hTQ, hX_ge, hY₁⟩ :=
    exists_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb hQI
  have hX₂ : σ.slicing.intervalProp C a b₂ X :=
    intervalProp_of_upper_boundary_triangle (C := C) (s := σ.slicing)
      hab₁ hab₂ hb₁_le hQI hX_ge hY₁ hTQ
  have hY₂ : σ.slicing.intervalProp C a b₂ Y :=
    σ.slicing.intervalProp_mono C (show a ≤ a by linarith) hb hY₁
  let XI₂ : σ.slicing.IntervalCat C a b₂ := ⟨X, hX₂⟩
  let YI₂ : σ.slicing.IntervalCat C a b₂ := ⟨Y, hY₂⟩
  let xQ : XI₂ ⟶ QI₂ := ObjectProperty.homMk fX
  let qY : QI₂ ⟶ YI₂ := ObjectProperty.homMk gY
  let hcomp₁ : xQ ≫ qY = 0 := by
    ext
    simpa [xQ, qY] using comp_distTriang_mor_zero₁₂ _ hTQ
  let S₁ : ShortComplex (σ.slicing.IntervalCat C a b₂) := ShortComplex.mk xQ qY hcomp₁
  have hT₁ : Triangle.mk S₁.f.hom S₁.g.hom δY ∈ distTriang C := by
    simpa [S₁, xQ, qY] using hTQ
  have hS₁ : StrictShortExact S₁ :=
    Slicing.IntervalCat.strictShortExact_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b₂) hT₁
  by_cases hX_zero : IsZero X
  · have hQ₁ : σ.slicing.intervalProp C a b₁ Q :=
      σ.slicing.intervalProp_of_triangle C (Or.inl hX_zero) hY₁ hTQ
    have hQ_le : σ.slicing.leProp C (a + 1) Q := by
      exact ((σ.slicing.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁_le) Q)
        (σ.slicing.leProp_of_intervalProp C hQ₁)
    have hK_gt : σ.slicing.gtProp C a K := σ.slicing.gtProp_of_intervalProp C hKI
    have hK₁ : σ.slicing.intervalProp C a b₁ K :=
      σ.slicing.first_intervalProp_of_triangle C hab₁ hSS.1 hQ_le hK_gt hT
    have hK_phase₁ :
        wPhaseOf (W (K₀.of C K)) ((a + b₁) / 2) ≤ ψ :=
      hSS.2.2.2.2 hT hK₁ hQ₁ hKne
    have hK_eq :
        wPhaseOf (W (K₀.of C K)) ((a + b₁) / 2) =
          wPhaseOf (W (K₀.of C K)) ((a + b₂) / 2) :=
      wPhaseOf_eq_of_intervalProp_upper_inclusion
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hb hK₁ hKne
        hε₀ hε₀2 hthin₂ hsin
    rw [← hK_eq]
    exact hK_phase₁
  · haveI : Mono xQ := hS₁.shortExact.mono_f
    have hxQ_strict : IsStrictMono xQ := ⟨hS₁.shortExact.mono_f, hS₁.strict_f⟩
    have hqY_strict : IsStrictEpi qY := ⟨hS₁.shortExact.epi_g, hS₁.strict_g⟩
    have hqE_strict : IsStrictEpi qE := ⟨hS₀.shortExact.epi_g, hS₀.strict_g⟩
    let BX : Subobject QI₂ := Subobject.mk xQ
    let PB : Subobject EI₂ := (Subobject.pullback qE).obj BX
    let hBXfac : BX.Factors (iK ≫ qE) := by
      rw [hcomp₀]
      exact (Subobject.factors_zero : BX.Factors (0 : KI₂ ⟶ QI₂))
    let hPBfac : PB.Factors iK := Limits.pullback_factors qE BX iK hBXfac
    let mPB : KI₂ ⟶ PB := PB.factorThru iK hPBfac
    let hcompL : mPB ≫ Subobject.pullbackπ qE BX = 0 := by
      apply (cancel_mono BX.arrow).mp
      calc
        (mPB ≫ Subobject.pullbackπ qE BX) ≫ BX.arrow
            = mPB ≫ (Subobject.pullbackπ qE BX ≫ BX.arrow) := by
                simp [Category.assoc]
        _ = mPB ≫ (PB.arrow ≫ qE) := by rw [(Subobject.isPullback qE BX).w]
        _ = (mPB ≫ PB.arrow) ≫ qE := by simp [Category.assoc]
        _ = iK ≫ qE := by
            simpa [mPB, hPBfac] using Subobject.factorThru_arrow PB iK hPBfac
        _ = 0 := hcomp₀
        _ = 0 ≫ BX.arrow := by simp
    let SL : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
      ShortComplex.mk mPB (Subobject.pullbackπ qE BX) hcompL
    have hLeft : StrictShortExact SL := by
      simpa [SL, PB, BX, mPB, hcompL] using
        interval_strictShortExact_pullback_left
          (C := C) (s := σ.slicing) (a := a) (b := b₂)
          (i := iK) (q := qE) hcomp₀ hS₀Ker hqE_strict BX
    have hBXcomp : BX.arrow ≫ qY = 0 := by
      calc
        BX.arrow ≫ qY = ((Subobject.underlyingIso xQ).hom ≫ xQ) ≫ qY := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk xQ]
        _ = (Subobject.underlyingIso xQ).hom ≫ (xQ ≫ qY) := by simp [Category.assoc]
        _ = 0 := by simp [hcomp₁]
    have hBXKer : IsLimit (KernelFork.ofι BX.arrow hBXcomp) := by
      have hS₁Ker : IsLimit (KernelFork.ofι xQ hcomp₁) := by
        simpa [S₁] using
          interval_fIsKernel_of_strictShortExact
            (C := C) (s := σ.slicing) (a := a) (b := b₂) hS₁
      refine KernelFork.IsLimit.ofι' BX.arrow hBXcomp (fun {W} k hk ↦ ?_)
      let uX : W ⟶ XI₂ := hS₁Ker.lift (KernelFork.ofι k hk)
      refine ⟨uX ≫ (Subobject.underlyingIso xQ).inv, ?_⟩
      calc
        (uX ≫ (Subobject.underlyingIso xQ).inv) ≫ BX.arrow
            = uX ≫ xQ := by simp [Category.assoc, BX]
        _ = k := hS₁Ker.fac _ Limits.WalkingParallelPair.zero
    let pE : EI₂ ⟶ YI₂ := qE ≫ qY
    let hcompR : PB.arrow ≫ pE = 0 := by
      calc
        PB.arrow ≫ pE = PB.arrow ≫ qE ≫ qY := by simp [pE, Category.assoc]
        _ = (PB.arrow ≫ qE) ≫ qY := by simp [Category.assoc]
        _ = (Subobject.pullbackπ qE BX ≫ BX.arrow) ≫ qY := by
            rw [(Subobject.isPullback qE BX).w]
        _ = Subobject.pullbackπ qE BX ≫ BX.arrow ≫ qY := by
            simp [Category.assoc]
        _ = Subobject.pullbackπ qE BX ≫ (BX.arrow ≫ qY) := by simp [Category.assoc]
        _ = 0 := by simp [hBXcomp]
    let SR : ShortComplex (σ.slicing.IntervalCat C a b₂) :=
      ShortComplex.mk PB.arrow pE hcompR
    have hRight : StrictShortExact SR := by
      simpa [SR, PB, BX, pE, hcompR] using
        interval_strictShortExact_pullback_right
          (C := C) (s := σ.slicing) (a := a) (b := b₂) qE hqE_strict BX qY hBXcomp
          hBXKer hqY_strict
    haveI : Mono mPB := hLeft.shortExact.mono_f
    have hPB_ne : ¬IsZero (PB : σ.slicing.IntervalCat C a b₂).obj := by
      intro hPBZ
      have hm_zero_hom : mPB.hom = 0 := hPBZ.eq_of_tgt mPB.hom 0
      have hm_zero : mPB = 0 := by
        apply ObjectProperty.hom_ext
        simpa using hm_zero_hom
      have hId : 𝟙 KI₂ = 0 := by
        apply (cancel_mono mPB).1
        simpa [hm_zero]
      have hKZ : IsZero KI₂ := (IsZero.iff_id_eq_zero KI₂).mpr hId
      exact hKne (((σ.slicing.intervalProp C a b₂).ι).map_isZero hKZ)
    obtain ⟨δR, hTR⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := σ.slicing) (a := a) (b := b₂) hRight
    have hY_le : σ.slicing.leProp C (a + 1) Y := by
      exact ((σ.slicing.leProp_mono (C := C) (t₁ := b₁) (t₂ := a + 1) hb₁_le) Y)
        (σ.slicing.leProp_of_intervalProp C hY₁)
    have hPB_gt : σ.slicing.gtProp C a (PB : σ.slicing.IntervalCat C a b₂).obj :=
      σ.slicing.gtProp_of_intervalProp C
        (show σ.slicing.intervalProp C a b₂ (PB : σ.slicing.IntervalCat C a b₂).obj from
          (PB : σ.slicing.IntervalCat C a b₂).property)
    have hPB₁ : σ.slicing.intervalProp C a b₁ (PB : σ.slicing.IntervalCat C a b₂).obj :=
      σ.slicing.first_intervalProp_of_triangle C hab₁ hSS.1 hY_le hPB_gt
        (by simpa [SR, pE] using hTR)
    have hPB_phase₁ :
        wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₁) / 2) ≤ ψ :=
      hSS.2.2.2.2 (by simpa [SR, pE] using hTR) hPB₁ hY₁ hPB_ne
    have hPB_eq :
        wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₁) / 2) =
          wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₂) / 2) :=
      wPhaseOf_eq_of_intervalProp_upper_inclusion
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hb hPB₁ hPB_ne
        hε₀ hε₀2 hthin₂ hsin
    have hPB_phase_le :
        wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₂) / 2) ≤ ψ := by
      rw [← hPB_eq]
      exact hPB_phase₁
    have hX_phase_gt :
        ψ < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) :=
      wPhaseOf_gt_of_upper_boundary_triangle
        (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab₂ hb hQI hX_ge hY₁ hX_zero
        hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTQ
    have hPB_window := hWindow₂
      (show σ.slicing.intervalProp C a b₂ (PB : σ.slicing.IntervalCat C a b₂).obj from
        (PB : σ.slicing.IntervalCat C a b₂).property) hPB_ne
    have hK_window := hWindow₂ hKI hKne
    have hX_window := hWindow₂ hX₂ hX_zero
    let ψPB : ℝ := wPhaseOf (W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj)) ((a + b₂) / 2)
    have hBXW :
        W (K₀.of C (Subobject.underlying.obj BX).obj) = W (K₀.of C X) := by
      simpa [BX, XI₂] using
        congrArg W
          (K₀.of_iso C (((σ.slicing.intervalProp C a b₂).ι).mapIso (Subobject.underlyingIso xQ)))
    have hX_phase_gt_pb :
        ψPB < wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) := by
      dsimp [ψPB]
      linarith
    have hX_range_pb :
        wPhaseOf (W (K₀.of C X)) ((a + b₂) / 2) ∈ Set.Ioo (ψPB - 1) (ψPB + 1) := by
      constructor <;> dsimp [ψPB] <;> linarith [hX_window.1, hX_window.2, hPB_window.1,
        hPB_window.2, hthin₂]
    have hK_range_pb :
        wPhaseOf (W (K₀.of C K)) ((a + b₂) / 2) ∈ Set.Ioo (ψPB - 1) (ψPB + 1) := by
      constructor <;> dsimp [ψPB] <;> linarith [hK_window.1, hK_window.2, hPB_window.1,
        hPB_window.2, hthin₂]
    let ssf₂ := σ.skewedStabilityFunction_of_near C W hW hab₂
    have hsumL :
        W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj) =
          W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
            W (K₀.of C (XI₂ : σ.slicing.IntervalCat C a b₂).obj) := by
      have hsumL' :
          W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj) =
            W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
              W (K₀.of C (Subobject.underlying.obj BX).obj) := by
        simpa [StabilityCondition.skewedStabilityFunction_of_near, SL, PB, KI₂, map_add] using
          ssf₂.strict_additive (C := C) (s := σ.slicing) (a := a) (b := b₂) hLeft
      calc
        W (K₀.of C (PB : σ.slicing.IntervalCat C a b₂).obj) =
            W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
              W (K₀.of C (Subobject.underlying.obj BX).obj) := hsumL'
        _ = W (K₀.of C (KI₂ : σ.slicing.IntervalCat C a b₂).obj) +
              W (K₀.of C (XI₂ : σ.slicing.IntervalCat C a b₂).obj) := by
            rw [hBXW]
    have hX_Wne : W (K₀.of C X) ≠ 0 := hW_ne_big hX₂ hX_zero
    have hK_phase_lt_pb :
        wPhaseOf (W (K₀.of C K)) ((a + b₂) / 2) < ψPB := by
      dsimp [ψPB]
      exact wPhaseOf_seesaw_dual
        (by simpa [KI₂, XI₂, add_comm] using hsumL.symm)
        rfl hX_phase_gt_pb hX_Wne hX_range_pb hK_range_pb
    linarith

private theorem SkewedStabilityFunction.semistable_of_iso
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    {E E' : C} (e : E ≅ E') {ψ : ℝ} (h : ssf.Semistable C E ψ) :
    ssf.Semistable C E' ψ := by
  refine ⟨(s.intervalProp C a b).prop_of_iso e h.1, ?_, ?_, ?_, ?_⟩
  · exact fun hE' ↦ h.2.1 ((Iso.isZero_iff e).mpr hE')
  · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
    exact h.2.2.1
  · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
    exact h.2.2.2.1
  · intro K Q f₁ f₂ f₃ hT hK hQ hKne
    have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
      isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
          (by simp) (by simp) (by simp))
    exact h.2.2.2.2 hT' hK hQ hKne

variable [IsTriangulated C] in
/-- A maximal-phase strict subobject of a non-semistable interval object cannot be `⊤`. -/
private theorem SkewedStabilityFunction.maxPhase_strictSubobject_ne_top_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    M ≠ ⊤ := by
  intro hM_top
  apply hns
  have hM_ss :=
    ssf.semistable_of_maxPhase_strictSubobject (C := C) (σ := σ)
      (a := a) (b := b) hM_ne hM_strict hM_max hW_interval
  subst hM_top
  have hphase :
      wPhaseOf
          (ssf.W
            (K₀.of C (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj))) ssf.α =
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    let eC :
        (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj) ≅ X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
    simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
  let eC :
      (((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj) ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (asIso (⊤ : Subobject X).arrow)
  have hTop_ss := semistable_of_iso
    (C := C) (s := σ.slicing) (a := a) (b := b)
    eC hM_ss
  simpa [hphase] using hTop_ss

variable [IsTriangulated C] in
/-- In a non-semistable interval object, a maximal-phase strict subobject has strictly
larger phase than the ambient object. -/
private theorem SkewedStabilityFunction.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hX : ¬IsZero X)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hM_ne : M ≠ ⊥) (hM_strict : IsStrictMono M.arrow)
    (hM_max : ∀ B : Subobject X, B ≠ ⊥ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
  let phaseObj : σ.slicing.IntervalCat C a b → ℝ := fun Y ↦
    wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hX_obj : ¬IsZero X.obj := by
    intro hZ
    exact hX (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  by_contra hle
  push_neg at hle
  apply hns
  refine ⟨X.property, hX_obj, hW_interval X.property hX_obj, rfl, ?_⟩
  intro K Q f₁ f₂ f₃ hT hK hQ hKne
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iKX : KI ⟶ X := ObjectProperty.homMk f₁
  let gXQ : X ⟶ QI := ObjectProperty.homMk f₂
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iKX gXQ (by
      ext
      simpa [iKX, gXQ] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT' : Triangle.mk S.f.hom S.g.hom f₃ ∈ distTriang C := by
    simpa [S, iKX, gXQ] using hT
  have hK_strict : IsStrictMono iKX :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a) (b := b) hT').1
  letI : Mono iKX := hK_strict.mono
  let B : Subobject X := Subobject.mk iKX
  have hKI_ne : ¬IsZero KI := by
    intro hZ
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  have hB_ne : B ≠ ⊥ := by
    intro hB
    have hzero : iKX = 0 := by
      exact (Subobject.mk_eq_bot_iff_zero).mp
        (show Subobject.mk iKX = ⊥ by simpa [B] using hB)
    have hId : 𝟙 KI = 0 := by
      apply (cancel_mono iKX).1
      simpa [hzero]
    exact hKI_ne ((IsZero.iff_id_eq_zero KI).mpr hId)
  have hB_strict : IsStrictMono B.arrow := by
    simpa [B] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) iKX hK_strict)
  have hPhaseB : phaseObj KI ≤ phaseObj M := by
    have hPhaseSub : phaseObj (B : σ.slicing.IntervalCat C a b) ≤ phaseObj M :=
      hM_max B hB_ne hB_strict
    have hIsoK :
        phaseObj KI = phaseObj (B : σ.slicing.IntervalCat C a b) := by
      let eC : (B : σ.slicing.IntervalCat C a b).obj ≅ KI.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (Subobject.underlyingIso iKX)
      simpa [phaseObj] using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α)
        (K₀.of_iso C eC).symm
    exact hIsoK.trans_le hPhaseSub
  simpa [phaseObj, KI] using hPhaseB.trans hle

variable [IsTriangulated C] in
/-- Strict-Artinian descent for the first strict short exact sequence: starting from a
non-semistable thin-interval object, repeatedly pass to a proper strict subobject of larger
phase until the descent terminates at a semistable strict subobject. This is the faithful
Section 7 substitute for the older finite-enumeration wrapper. -/
private theorem SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} [IsStrictArtinianObject X] (hX : ¬IsZero X)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ∃ M : Subobject X,
      M ≠ ⊥ ∧
      M ≠ ⊤ ∧
      IsStrictMono M.arrow ∧
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) := by
  let phaseSub : StrictSubobject X → ℝ := fun B ↦
    wPhaseOf (ssf.W (K₀.of C ((B.1 : σ.slicing.IntervalCat C a b).obj))) ssf.α
  let P : StrictSubobject X → Prop := fun B =>
    ∀ hBne : ¬IsZero (B.1 : σ.slicing.IntervalCat C a b),
      ¬ ssf.Semistable C ((B.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub B) →
      ∃ D : StrictSubobject X,
        D < B ∧
        ssf.Semistable C ((D.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub D) ∧
        phaseSub B < phaseSub D
  have hP : ∀ B : StrictSubobject X, P B := by
    intro B
    refine (show WellFounded ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
      wellFounded_lt).induction B ?_
    intro B ih hBne hnsB
    obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hphaseBA⟩ :=
      ssf.exists_phase_gt_strictSubobject_of_not_semistable
        (C := C) (σ := σ) (a := a) (b := b) (X := (B.1 : σ.slicing.IntervalCat C a b))
        hBne hW_interval hnsB
    let Csub : Subobject X := intervalLiftSub (C := C) (X := X) B.1 A
    have hC_ne_bot : Csub ≠ ⊥ :=
      intervalLiftSub_ne_bot (C := C) (X := X) B.1 hA_ne_bot
    have hC_strict : IsStrictMono Csub.arrow :=
      intervalLiftSub_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.2 hA_strict
    let Cstr : StrictSubobject X := ⟨Csub, hC_strict⟩
    have hC_lt_B : Cstr < B := by
      simpa [Cstr, Csub] using
        (intervalLiftSub_lt (C := C) (X := X) B.1 hA_ne_top)
    have hC_ne : ¬IsZero (Cstr.1 : σ.slicing.IntervalCat C a b) :=
      intervalSubobject_not_isZero_of_ne_bot
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hC_ne_bot
    have hphaseBC : phaseSub B < phaseSub Cstr := by
      dsimp [phaseSub, Cstr, Csub]
      rw [intervalLiftSub_wPhase_eq (C := C) (s := σ.slicing) (ssf := ssf) B.1 A]
      exact hphaseBA
    by_cases hssC :
        ssf.Semistable C ((Cstr.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub Cstr)
    · exact ⟨Cstr, hC_lt_B, hssC, hphaseBC⟩
    · obtain ⟨D, hD_lt_C, hssD, hphaseCD⟩ := ih Cstr hC_lt_B hC_ne hssC
      exact ⟨D, lt_trans hD_lt_C hC_lt_B, hssD, lt_trans hphaseBC hphaseCD⟩
  obtain ⟨B, hB_ne_bot, hB_ne_top, hB_strict, hphaseXB⟩ :=
    ssf.exists_phase_gt_strictSubobject_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hW_interval hns
  let Bstr : StrictSubobject X := ⟨B, hB_strict⟩
  have hB_ne : ¬IsZero (Bstr.1 : σ.slicing.IntervalCat C a b) :=
    intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hB_ne_bot
  have hphaseXB' :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α < phaseSub Bstr := by
    simpa [phaseSub, Bstr] using hphaseXB
  by_cases hssB :
      ssf.Semistable C ((Bstr.1 : σ.slicing.IntervalCat C a b).obj) (phaseSub Bstr)
  · refine ⟨B, hB_ne_bot, hB_ne_top, hB_strict, ?_, hphaseXB, ?_⟩
    · simpa [phaseSub, Bstr] using hssB
    · exact interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.arrow hB_strict
  · obtain ⟨D, hD_lt_B, hssD, hphaseBD⟩ := hP Bstr hB_ne hssB
    have hD_ne_top : D.1 ≠ ⊤ := by
      intro hD
      have htop_le : (⊤ : Subobject X) ≤ B := by
        have hle : D.1 ≤ B := hD_lt_B.le
        simpa [hD] using hle
      exact hB_ne_top (top_le_iff.mp htop_le)
    have hD_ne_bot : D.1 ≠ ⊥ := by
      intro hD
      exact hssD.2.1
        (((σ.slicing.intervalProp C a b).ι).map_isZero
          ((intervalSubobject_isZero_iff_eq_bot
            (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) D.1).mpr hD))
    refine ⟨D.1, hD_ne_bot, hD_ne_top, D.2, ?_, ?_, ?_⟩
    · simpa [phaseSub] using hssD
    · exact lt_trans hphaseXB' hphaseBD
    · exact interval_strictShortExact_cokernel_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) D.1.arrow D.2

variable [IsTriangulated C] in
/-- Finiteness of subobjects in the left-heart image of an interval object implies finiteness of
its strict-subobject set in the thin interval category. This is the paper-faithful local
finite-length input for the first strict short exact sequence. -/
private theorem Slicing.IntervalCat.finite_strictSubobjects_of_finite_leftHeartSubobjects
    (s : Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b}
    (hX : Finite (Subobject ((Slicing.IntervalCat.toLeftHeart
      (C := C) (s := s) a b (Fact.out : b - a ≤ 1)).obj X))) :
    Finite {B : Subobject X // B ≠ ⊥ ∧ IsStrictMono B.arrow} := by
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let φ : {B : Subobject X // B ≠ ⊥ ∧ IsStrictMono B.arrow} → Subobject (FL.obj X) :=
    fun B ↦ by
      letI : Mono (FL.map B.1.arrow) :=
        Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
          (C := C) (s := s) (a := a) (b := b) B.1.arrow B.2.2
      exact Subobject.mk (FL.map B.1.arrow)
  exact Finite.of_injective φ (fun B₁ B₂ hEq ↦ by
    letI : Mono (FL.map B₁.1.arrow) :=
      Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B₁.1.arrow B₁.2.2
    letI : Mono (FL.map B₂.1.arrow) :=
      Slicing.IntervalCat.mono_toLeftHeart_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B₂.1.arrow B₂.2.2
    apply Subtype.ext
    simpa [Subobject.mk_arrow] using Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
      (FL.preimageIso (Subobject.isoOfMkEqMk _ _ hEq))
      (FL.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp hEq.le)))

variable [IsTriangulated C] in
/-- Bridgeland's first strict short exact sequence in a thin category: if an interval object is
not `W`-semistable, there is a proper strict subobject of maximal `W`-phase, and its inclusion
gives a strict short exact sequence `0 → A → E → B → 0`.

The faithful local-finiteness input here is finiteness of the thin category's
strict-subobject set, not an ambient `Finite (Subobject X.obj)` statement in `C`. -/
private theorem SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hT_fin : Set.Finite {M : Subobject X | M ≠ ⊥ ∧ IsStrictMono M.arrow})
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ∃ M : Subobject X,
      M ≠ ⊥ ∧
      M ≠ ⊤ ∧
      IsStrictMono M.arrow ∧
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) := by
  obtain ⟨M, hM_ne, hM_strict, hM_max, _⟩ :=
    ssf.exists_maxPhase_maximal_strictSubobject_of_finite
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hT_fin
  have hM_ne_top : M ≠ ⊤ :=
    ssf.maxPhase_strictSubobject_ne_top_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hns hM_ne hM_strict hM_max hW_interval
  have hM_ss :
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) :=
    ssf.semistable_of_maxPhase_strictSubobject
      (C := C) (σ := σ) (a := a) (b := b) hM_ne hM_strict hM_max hW_interval
  have hphase_gt :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
    ssf.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := X) hX hns hM_ne hM_strict hM_max hW_interval
  have hS : StrictShortExact
      (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) :=
    interval_strictShortExact_cokernel_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) M.arrow hM_strict
  exact ⟨M, hM_ne, hM_ne_top, hM_strict, hM_ss, hphase_gt, hS⟩

variable [IsTriangulated C] in
/-- A convenient left-heart version of the first strict short exact sequence wrapper. If the
left-heart image of `X` has finite subobject lattice, then `X` admits Bridgeland's first strict
short exact sequence whenever it is not `W`-semistable. -/
private theorem SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable_of_finite_leftHeartSubobjects
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hX_left : Finite (Subobject ((Slicing.IntervalCat.toLeftHeart
      (C := C) (s := σ.slicing) a b (Fact.out : b - a ≤ 1)).obj X)))
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0) :
    ∃ M : Subobject X,
      M ≠ ⊥ ∧
      M ≠ ⊤ ∧
      IsStrictMono M.arrow ∧
      ssf.Semistable C (M : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)) := by
  let T : Set (Subobject X) := {M | M ≠ ⊥ ∧ IsStrictMono M.arrow}
  have hT_type : Finite T := by
    simpa [T] using
      (Slicing.IntervalCat.finite_strictSubobjects_of_finite_leftHeartSubobjects
        (C := C) (s := σ.slicing) (a := a) (b := b) hX_left)
  have hT_fin : T.Finite := by
    letI : Finite T := hT_type
    letI : Fintype T := Fintype.ofFinite T
    exact T.toFinite
  exact ssf.exists_first_strictShortExact_of_not_semistable
    (C := C) (σ := σ) (a := a) (b := b) hX hT_fin hns hW_interval

private lemma interval_pullback_cokernel_bot_eq
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow) :
    (Subobject.pullback (cokernel.π M.arrow)).obj ⊥ = M := by
  apply le_antisymm
  · set P := (Subobject.pullback (cokernel.π M.arrow)).obj ⊥
    have hP : P.arrow ≫ cokernel.π M.arrow = 0 := by
      have := (Subobject.isPullback (cokernel.π M.arrow)
        (⊥ : Subobject (cokernel M.arrow))).w
      simp only [Subobject.bot_arrow, comp_zero] at this
      rw [this]
    exact Subobject.le_of_comm
      (hM.isLimitKernelFork.lift (KernelFork.ofι P.arrow hP))
      (hM.isLimitKernelFork.fac _ Limits.WalkingParallelPair.zero)
  · exact interval_le_pullback_cokernel
      (C := C) (s := s) (a := a) (b := b) M ⊥

private lemma interval_cokernel_nonzero_of_ne_top
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X} (hM : M ≠ ⊤)
    (hM_strict : IsStrictMono M.arrow) :
    ¬IsZero (cokernel M.arrow) := by
  intro hZ
  haveI : Epi M.arrow := Preadditive.epi_of_isZero_cokernel M.arrow hZ
  haveI : IsIso M.arrow := hM_strict.isIso
  exact hM (Subobject.eq_top_of_isIso_arrow M)

private lemma interval_pullback_ofLE_comm
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    {A' B' : Subobject (cokernel M.arrow)} (h : A' ≤ B') :
    let q := cokernel.π M.arrow
    let pbA := (Subobject.pullback q).obj A'
    let pbB := (Subobject.pullback q).obj B'
    let hpb : pbA ≤ pbB := (Subobject.pullback q).monotone h
    Subobject.ofLE pbA pbB hpb ≫ Subobject.pullbackπ q B' =
      Subobject.pullbackπ q A' ≫ Subobject.ofLE A' B' h := by
  let q := cokernel.π M.arrow
  let pbA := (Subobject.pullback q).obj A'
  let pbB := (Subobject.pullback q).obj B'
  let hpb : pbA ≤ pbB := (Subobject.pullback q).monotone h
  apply (cancel_mono B'.arrow).mp
  simp only [Category.assoc, Subobject.ofLE_arrow]
  calc
    Subobject.ofLE pbA pbB hpb ≫ (Subobject.pullbackπ q B' ≫ B'.arrow)
        = Subobject.ofLE pbA pbB hpb ≫ (pbB.arrow ≫ q) := by
            rw [(Subobject.isPullback q B').w]
    _ = (Subobject.ofLE pbA pbB hpb ≫ pbB.arrow) ≫ q := by
          rw [Category.assoc]
    _ = pbA.arrow ≫ q := by rw [Subobject.ofLE_arrow]
    _ = Subobject.pullbackπ q A' ≫ A'.arrow := (Subobject.isPullback q A').w.symm

private lemma SkewedStabilityFunction.Wobj_pullback_eq_add
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    (B : Subobject (cokernel M.arrow)) :
    ssf.W (K₀.of C (((Subobject.pullback (cokernel.π M.arrow)).obj B : Subobject X) :
      s.IntervalCat C a b).obj) =
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
        ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) := by
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk
      (Subobject.ofLE M _ (interval_le_pullback_cokernel
        (C := C) (s := s) (a := a) (b := b) M B))
      (Subobject.pullbackπ (cokernel.π M.arrow) B)
      (interval_ofLE_pullbackπ_eq_zero (C := C) (s := s) (a := a) (b := b) M B)
  have hS :
      StrictShortExact S :=
    interval_strictShortExact_ofLE_pullbackπ_cokernel
      (C := C) (s := s) (a := a) (b := b) M hM B
  simpa [S] using ssf.strict_additive (C := C) (s := s) (a := a) (b := b) hS

private lemma interval_lt_pullback_cokernel_of_ne_bot
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    {B : Subobject (cokernel M.arrow)} (hB : B ≠ ⊥) :
    M < (Subobject.pullback (cokernel.π M.arrow)).obj B := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  have hle : M ≤ pbB :=
    interval_le_pullback_cokernel (C := C) (s := s) (a := a) (b := b) M B
  have hne : M ≠ pbB := by
    intro hEq
    let heqObj : Subobject.underlying.obj M = Subobject.underlying.obj pbB :=
      congrArg Subobject.underlying.obj hEq
    have hi : Subobject.ofLE M pbB hle = eqToHom heqObj := by
      apply (cancel_mono pbB.arrow).1
      calc
        Subobject.ofLE M pbB hle ≫ pbB.arrow = M.arrow := Subobject.ofLE_arrow hle
        _ = eqToHom heqObj ≫ pbB.arrow := (Subobject.arrow_congr M pbB hEq).symm
    have hzero :
        Subobject.pullbackπ q B = 0 := by
      have hcomp := interval_ofLE_pullbackπ_eq_zero
        (C := C) (s := s) (a := a) (b := b) M B
      rw [hi] at hcomp
      letI : Epi (eqToHom heqObj) := by infer_instance
      exact (cancel_epi (eqToHom heqObj)).1 (by simpa using hcomp)
    have hπ : IsStrictEpi (Subobject.pullbackπ q B) :=
      interval_pullbackπ_strictEpi_of_strictEpi
        (C := C) (s := s) (a := a) (b := b) q (isStrictEpi_cokernel M.arrow) B
    haveI : Epi (Subobject.pullbackπ q B) := hπ.epi
    have hBZ : IsZero (B : s.IntervalCat C a b) :=
      (IsZero.iff_id_eq_zero _).mpr <|
        (cancel_epi (Subobject.pullbackπ q B)).1 (by simpa [hzero])
    exact hB ((intervalSubobject_isZero_iff_eq_bot
      (C := C) (s := s) (a := a) (b := b) (X := cokernel M.arrow) B).mp hBZ)
  exact lt_of_le_of_ne hle hne

private lemma interval_pullback_cokernel_ne_top_of_ne_top
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} {M : Subobject X}
    {B : Subobject (cokernel M.arrow)} (hB : B ≠ ⊤) (hB_strict : IsStrictMono B.arrow) :
    (Subobject.pullback (cokernel.π M.arrow)).obj B ≠ ⊤ := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  intro hpb_top
  have hpb_iso : IsIso pbB.arrow := by
    let heqObj : Subobject.underlying.obj pbB = Subobject.underlying.obj (⊤ : Subobject X) :=
      congrArg Subobject.underlying.obj hpb_top
    have harr : pbB.arrow = eqToHom heqObj ≫ (⊤ : Subobject X).arrow := by
      simpa using (Subobject.arrow_congr pbB ⊤ hpb_top).symm
    rw [harr]
    infer_instance
  let r : X ⟶ (B : s.IntervalCat C a b) :=
    inv pbB.arrow ≫ Subobject.pullbackπ q B
  have hr : r ≫ B.arrow = q := by
    calc
      r ≫ B.arrow = inv pbB.arrow ≫ (Subobject.pullbackπ q B ≫ B.arrow) := by
        simp [r]
      _ = inv pbB.arrow ≫ (pbB.arrow ≫ q) := by rw [(Subobject.isPullback q B).w]
      _ = q := by simp
  haveI : Epi q := by infer_instance
  haveI : Epi B.arrow := epi_of_epi_fac hr
  haveI : IsIso B.arrow := hB_strict.isIso
  exact hB (Subobject.eq_top_of_isIso_arrow B)

private lemma SkewedStabilityFunction.Wobj_cokernel_pullback_eq
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    {B : Subobject (cokernel M.arrow)} (hB : IsStrictMono B.arrow) :
    ssf.W (K₀.of C (cokernel ((Subobject.pullback (cokernel.π M.arrow)).obj B).arrow).obj) =
      ssf.W (K₀.of C (cokernel B.arrow).obj) := by
  let q := cokernel.π M.arrow
  let pbB := (Subobject.pullback q).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := s) (a := a) (b := b) q B hB
  have hXM :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) M.arrow hM)
  have hXpb :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (pbB : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel pbB.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) pbB.arrow hpb_strict)
  have hQB :
      ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) B.arrow hB)
  have hpb_add :
      ssf.W (K₀.of C (pbB : s.IntervalCat C a b).obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) :=
    Wobj_pullback_eq_add
      (C := C) (s := s) (a := a) (b := b) (ssf := ssf) M hM B
  rw [hpb_add, add_assoc] at hXpb
  have hsum₁ :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := by
    calc
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj)
          = ssf.W (K₀.of C X.obj) := hXM.symm
      _ = ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := hXpb
  have hsum₂ :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel B.arrow).obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := by
    rw [hQB] at hsum₁
    simpa [add_assoc] using hsum₁
  have hsum₃ :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel B.arrow).obj)) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
            ssf.W (K₀.of C (cokernel pbB.arrow).obj)) := by
    simpa [add_assoc] using hsum₂
  have hsum₄ :
      ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) =
        ssf.W (K₀.of C (B : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel pbB.arrow).obj) := by
    exact add_left_cancel hsum₃
  have hsum₅ :
      ssf.W (K₀.of C (cokernel B.arrow).obj) =
        ssf.W (K₀.of C (cokernel pbB.arrow).obj) := by
    exact add_left_cancel hsum₄
  exact hsum₅.symm

private lemma SkewedStabilityFunction.Wobj_liftSub_cokernel_eq_add
    {s : Slicing C} [IsTriangulated C] {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : s.IntervalCat C a b} (M : Subobject X) (hM : IsStrictMono M.arrow)
    {A : Subobject (M : s.IntervalCat C a b)} (hA : IsStrictMono A.arrow) :
    let liftA := intervalLiftSub (C := C) (X := X) M A
    ssf.W (K₀.of C (cokernel liftA.arrow).obj) =
      ssf.W (K₀.of C (cokernel A.arrow).obj) +
        ssf.W (K₀.of C (cokernel M.arrow).obj) := by
  let liftA := intervalLiftSub (C := C) (X := X) M A
  have hcomp : IsStrictMono (A.arrow ≫ M.arrow) :=
    Slicing.IntervalCat.comp_strictMono
      (C := C) (s := s) (a := a) (b := b) A.arrow M.arrow hA hM
  have hLift : IsStrictMono liftA.arrow := by
    simpa [liftA, intervalLiftSub] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s) (a := a) (b := b) (A.arrow ≫ M.arrow) hcomp)
  have hXM :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) M.arrow hM)
  have hMA :
      ssf.W (K₀.of C (M : s.IntervalCat C a b).obj) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) A.arrow hA)
  have hXA :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (liftA : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := s) (a := a) (b := b) liftA.arrow hLift)
  have hAeq :
      ssf.W (K₀.of C (liftA : s.IntervalCat C a b).obj) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) := by
    let eC : (liftA : s.IntervalCat C a b).obj ≅ (A : s.IntervalCat C a b).obj :=
      (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso
        (Subobject.underlyingIso (A.arrow ≫ M.arrow))
    simpa [liftA, intervalLiftSub] using congrArg ssf.W (K₀.of_iso C eC)
  rw [hMA, add_assoc] at hXM
  rw [hAeq] at hXA
  have hsum :
      ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) +
            ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    calc
      ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) +
            ssf.W (K₀.of C (cokernel M.arrow).obj)
          = ssf.W (K₀.of C X.obj) := by simpa [add_assoc] using hXM.symm
      _ = ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := hXA
  have hsumA :
      ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          (ssf.W (K₀.of C (cokernel A.arrow).obj) +
            ssf.W (K₀.of C (cokernel M.arrow).obj)) =
        ssf.W (K₀.of C (A : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    simpa [add_assoc] using hsum
  have hsum' :
      ssf.W (K₀.of C (cokernel A.arrow).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) =
        ssf.W (K₀.of C (cokernel liftA.arrow).obj) := by
    exact add_left_cancel hsumA
  simpa [liftA, add_comm, add_left_comm, add_assoc] using hsum'.symm

variable [IsTriangulated C] in
/-- The strict quotient attached to a minimal-phase strict kernel is semistable, provided
all nonzero objects in the thin interval have `W`-phases in a common open window of width `< 1`.
-/
private theorem SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hFinSub : ∀ Y : σ.slicing.IntervalCat C a b, Finite (Subobject Y))
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_lt : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → M < B →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1) :
    ssf.Semistable C (cokernel M.arrow).obj
      (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α) := by
  let Y : σ.slicing.IntervalCat C a b := cokernel M.arrow
  have hY_ne : ¬IsZero Y :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict
  have hY_obj_ne : ¬IsZero Y.obj := by
    intro hZ
    exact hY_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hY_window : L < ψY ∧ ψY < U := by
    simpa [Y, ψY] using hWindow Y.property hY_obj_ne
  by_contra hns
  haveI : Finite (Subobject Y) := hFinSub Y
  obtain ⟨B, hB_ne, hB_strict, hB_max, _⟩ :=
    ssf.exists_maxPhase_maximal_strictSubobject
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hY_ne
  have hB_ne_top : B ≠ ⊤ :=
    ssf.maxPhase_strictSubobject_ne_top_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hns hB_ne hB_strict hB_max hW_interval
  have hB_phase_gt :
      ψY < wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
    simpa [Y, ψY] using
      ssf.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
        (C := C) (σ := σ) (a := a) (b := b) (X := Y) (M := B)
        hY_ne hns hB_ne hB_strict hB_max hW_interval
  let pbB : Subobject X := (Subobject.pullback (cokernel.π M.arrow)).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π M.arrow) B hB_strict
  have hpb_ne_top : pbB ≠ ⊤ :=
    interval_pullback_cokernel_ne_top_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hMltpb : M < pbB :=
    interval_lt_pullback_cokernel_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne
  have hpb_quot_gt :
      ψY < wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α := by
    simpa [Y, ψY] using hM_lt pbB hpb_ne_top hpb_strict hMltpb
  have hcokB_ne : ¬IsZero (cokernel B.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_obj_ne : ¬IsZero (cokernel B.arrow).obj := by
    intro hZ
    exact hcokB_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokB_phase_gt :
      ψY < wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α := by
    rw [← ssf.Wobj_cokernel_pullback_eq
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict
      (B := B) hB_strict]
    exact hpb_quot_gt
  have hB_obj_ne : ¬IsZero (B : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hB_ne <|
        Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  have hB_window :
      L < wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α < U := by
    exact hWindow (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have hcokB_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel B.arrow).property hcokB_obj_ne
  have hUpper : U < ψY + 1 := by
    linarith [hWidth, hY_window.1]
  have hLower : ψY - 1 < L := by
    linarith [hWidth, hY_window.2]
  have hB_range :
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hcokB_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∈ Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hB_Wne : ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) ≠ 0 :=
    hW_interval (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have haddY :
      ssf.W (K₀.of C Y.obj) =
        ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) := by
    simpa [Y, map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.arrow hB_strict)
  have hcokB_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < ψY := by
    exact wPhaseOf_seesaw_dual haddY.symm rfl hB_phase_gt hB_Wne hB_range hcokB_range
  linarith

private theorem semistable_of_lower_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b ψ ε₀ : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b) (ha : a₂ ≤ a₁)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW ha₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₁ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b - ε₀)
    (hthin₂ : b - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW ha₂).Semistable C E ψ := by
  have hEI₂ : σ.slicing.intervalProp C a₂ b E :=
    σ.slicing.intervalProp_mono C ha (show b ≤ b by linarith) hSS.1
  have henv_lo₂ : a₂ + ε₀ ≤ ψ := by
    linarith
  have hthin₂' : b - a₂ < 1 := by
    linarith
  refine semistable_of_target_envelope_triangleTest
    (C := C) (σ := σ) (W := W) (hW := hW) ha₁ hSS ha₂ hEI₂ hε₀ henv_lo₂ henv_hi
    hthin₂ ?_
  intro K Q f₁ f₂ f₃ hT hKI hQI hKne
  letI : Fact (a₂ < b) := ⟨ha₂⟩
  letI : Fact (b - a₂ ≤ 1) := ⟨by linarith⟩
  letI : Fact (a₁ < b) := ⟨ha₁⟩
  letI : Fact (b - a₁ ≤ 1) := ⟨by linarith⟩
  let KI₂ : σ.slicing.IntervalCat C a₂ b := ⟨K, hKI⟩
  let EI₂ : σ.slicing.IntervalCat C a₂ b := ⟨E, hEI₂⟩
  let QI₂ : σ.slicing.IntervalCat C a₂ b := ⟨Q, hQI⟩
  let iK : KI₂ ⟶ EI₂ := ObjectProperty.homMk f₁
  let qE : EI₂ ⟶ QI₂ := ObjectProperty.homMk f₂
  let S₀ : ShortComplex (σ.slicing.IntervalCat C a₂ b) :=
    ShortComplex.mk iK qE (by
      ext
      simpa [iK, qE] using comp_distTriang_mor_zero₁₂ _ hT)
  have hT₂ : Triangle.mk iK.hom qE.hom f₃ ∈ distTriang C := by
    simpa [iK, qE] using hT
  have hiK_strict : IsStrictMono iK :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a₂) (b := b) (S := S₀) hT₂).1
  obtain ⟨X, Y, fX, gY, δY, hTK, hX₁, hY_le⟩ :=
    exists_lower_boundary_triangle (C := C) (s := σ.slicing) ha₁ ha₂ ha hKI
  have hX₂ : σ.slicing.intervalProp C a₂ b X :=
    σ.slicing.intervalProp_mono C ha (show b ≤ b by linarith) hX₁
  have hY₂ : σ.slicing.intervalProp C a₂ b Y :=
    intervalProp_of_lower_boundary_triangle (C := C) (s := σ.slicing)
      ha₂ ha₁ ha hKI hX₁ hY_le hTK
  let XI₁ : σ.slicing.IntervalCat C a₁ b := ⟨X, hX₁⟩
  let XI₂ : σ.slicing.IntervalCat C a₂ b := ⟨X, hX₂⟩
  let YI₂ : σ.slicing.IntervalCat C a₂ b := ⟨Y, hY₂⟩
  let EI₁ : σ.slicing.IntervalCat C a₁ b := ⟨E, hSS.1⟩
  let xK : XI₂ ⟶ KI₂ := ObjectProperty.homMk fX
  let kY : KI₂ ⟶ YI₂ := ObjectProperty.homMk gY
  let S₁ : ShortComplex (σ.slicing.IntervalCat C a₂ b) :=
    ShortComplex.mk xK kY (by
      ext
      simpa [xK, kY] using comp_distTriang_mor_zero₁₂ _ hTK)
  have hTK₂ : Triangle.mk xK.hom kY.hom δY ∈ distTriang C := by
    simpa [xK, kY] using hTK
  have hxK_strict : IsStrictMono xK :=
    (Slicing.IntervalCat.strictMono_strictEpi_of_distTriang
      (C := C) (s := σ.slicing) (a := a₂) (b := b) (S := S₁) hTK₂).1
  by_cases hYZ : IsZero Y
  · have hK₁ : σ.slicing.intervalProp C a₁ b K :=
      σ.slicing.intervalProp_of_triangle C hX₁ (Or.inl hYZ) hTK
    have hK_ge₁ : σ.slicing.geProp C (b - 1) K :=
      (σ.slicing.intervalProp_implies_rightWindow
        (C := C) (a := a₁) (b := b) (by linarith) hK₁).1
    have hQ_lt : σ.slicing.ltProp C b Q :=
      (σ.slicing.intervalProp_implies_rightWindow
        (C := C) (a := a₂) (b := b) (by linarith) hQI).2
    have hQ₁ : σ.slicing.intervalProp C a₁ b Q :=
      σ.slicing.third_intervalProp_of_triangle C ha₁ hSS.1 hK_ge₁ hQ_lt hT
    have hK_phase₁ :
        wPhaseOf (W (K₀.of C K)) ((a₁ + b) / 2) ≤ ψ :=
      hSS.2.2.2.2 hT hK₁ hQ₁ hKne
    have hK_eq :
        wPhaseOf (W (K₀.of C K)) ((a₁ + b) / 2) =
          wPhaseOf (W (K₀.of C K)) ((a₂ + b) / 2) :=
      wPhaseOf_eq_of_intervalProp_lower_inclusion
        (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha₂ ha hK₁ hKne
        hε₀ hε₀2 hthin₂ hsin
    rw [← hK_eq]
    exact hK_phase₁
  · by_cases hXZ : IsZero X
    · have hY_phase_lt :
          wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) < ψ :=
        wPhaseOf_lt_of_lower_boundary_triangle
          (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha₂ ha
          hKI hX₁ hY_le hYZ hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTK
      haveI : IsIso gY :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk fX gY δY) hTK).mp hXZ
      have hKY : W (K₀.of C K) = W (K₀.of C Y) := by
        simpa using congrArg W (K₀.of_iso C (asIso gY))
      rw [hKY]
      exact le_of_lt hY_phase_lt
    · let xE₂ : XI₂ ⟶ EI₂ := xK ≫ iK
      have hxE₂_strict : IsStrictMono xE₂ :=
        Slicing.IntervalCat.comp_strictMono
          (C := C) (s := σ.slicing) (a := a₂) (b := b) xK iK hxK_strict hiK_strict
      let xE₁ : XI₁ ⟶ EI₁ := ObjectProperty.homMk (fX ≫ f₁)
      have hmonoRH :
          Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := σ.slicing) a₁ b
            (Fact.out : b - a₁ ≤ 1)).map xE₁) := by
        simpa [Slicing.IntervalCat.toRightHeart, xE₁, xE₂] using
          (Slicing.IntervalCat.mono_toRightHeart_of_strictMono
            (C := C) (s := σ.slicing) (a := a₂) (b := b) xE₂ hxE₂_strict)
      have hxE₁_strict : IsStrictMono xE₁ := by
        letI :
            Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := σ.slicing) a₁ b
              (Fact.out : b - a₁ ≤ 1)).map xE₁) := hmonoRH
        exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart
          (C := C) (s := σ.slicing) (a := a₁) (b := b) xE₁
      let SX : ShortComplex (σ.slicing.IntervalCat C a₁ b) :=
        ShortComplex.mk xE₁ (cokernel.π xE₁) (cokernel.condition xE₁)
      have hSX : StrictShortExact SX :=
        interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := σ.slicing) (a := a₁) (b := b) xE₁ hxE₁_strict
      obtain ⟨δX, hTX⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
        (C := C) (s := σ.slicing) (a := a₁) (b := b) hSX
      have hX_phase₁ :
          wPhaseOf (W (K₀.of C X)) ((a₁ + b) / 2) ≤ ψ :=
        hSS.2.2.2.2 hTX hX₁ (cokernel xE₁).property hXZ
      have hX_eq :
          wPhaseOf (W (K₀.of C X)) ((a₁ + b) / 2) =
            wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) :=
        wPhaseOf_eq_of_intervalProp_lower_inclusion
          (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha₂ ha hX₁ hXZ
          hε₀ hε₀2 hthin₂ hsin
      have hX_phase_le :
          wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) ≤ ψ := by
        rw [← hX_eq]
        exact hX_phase₁
      have hY_phase_lt :
          wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) < ψ :=
        wPhaseOf_lt_of_lower_boundary_triangle
          (C := C) (σ := σ) (W := W) (hW := hW) ha₁ ha₂ ha
          hKI hX₁ hY_le hYZ hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin hTK
      have hsum :
          W (K₀.of C K) = W (K₀.of C X) + W (K₀.of C Y) := by
        simpa [map_add] using congrArg W
          (K₀.of_triangle C (Triangle.mk fX gY δY) hTK)
      have hX_range :
          wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hX₂ hXZ hε₀ hε₀2 henv_lo₂ henv_hi
          hthin₂ hsin
      have hY_range :
          wPhaseOf (W (K₀.of C Y)) ((a₂ + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hY₂ hYZ hε₀ hε₀2 henv_lo₂ henv_hi
          hthin₂ hsin
      have hK_range :
          wPhaseOf (W (K₀.of C K)) ((a₂ + b) / 2) ∈ Set.Ioo (ψ - 1) (ψ + 1) :=
        wPhaseOf_mem_Ioo_of_intervalProp_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hKI hKne hε₀ hε₀2 henv_lo₂ henv_hi
          hthin₂ hsin
      have hX_range' :
          wPhaseOf (W (K₀.of C X)) ((a₂ + b) / 2) ∈ Set.Ioc (ψ - 1) ψ := by
        exact ⟨hX_range.1, hX_phase_le⟩
      have hYW_ne : W (K₀.of C Y) ≠ 0 := by
        exact σ.W_ne_zero_of_intervalProp C W hthin₂'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) ha₂ hε₀ hε₀2 hthin₂ hsin) hYZ hY₂
      have hK_phase_lt :
          wPhaseOf (W (K₀.of C K)) ((a₂ + b) / 2) < ψ :=
        wPhaseOf_lt_of_add_le_lt hsum.symm hX_range' hY_phase_lt hYW_ne hY_range hK_range
      exact le_of_lt hK_phase_lt

private theorem semistable_of_interval_inclusion
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b₁ b₂ ψ ε₀ : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv_lo : a₁ + ε₀ ≤ ψ) (henv_hi : ψ ≤ b₁ - ε₀)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
  (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  have hthin_mid : b₂ - a₁ + 2 * ε₀ < 1 := by
    linarith
  have hab_mid : a₁ < b₂ := by
    linarith
  have hmid :
      (σ.skewedStabilityFunction_of_near C W hW hab_mid).Semistable C E ψ :=
    semistable_of_upper_inclusion
      (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab_mid hb hSS
      hε₀ hε₀2 henv_lo henv_hi hthin_mid hsin
  exact semistable_of_lower_inclusion
    (C := C) (σ := σ) (W := W) (hW := hW) (ha₁ := by linarith) hab₂ ha hmid
    hε₀ hε₀2 (by linarith) (by linarith [henv_hi, hb]) hthin₂ hsin

private theorem semistable_of_target_subinterval
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b₂ b₁ ψ ε₀ : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₁ : b₁ - a₁ + 2 * ε₀ < 1)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  refine semistable_of_target_envelope_triangleTest
    (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hSS hab₂ hI₂ hε₀ henv₂_lo henv₂_hi
    hthin₂ ?_
  intro K Q f₁ f₂ f₃ hT hKI hQI hKne
  have ha₂b₁ : a₂ < b₁ := by
    linarith
  have hthin_mid : b₁ - a₂ + 2 * ε₀ < 1 := by
    linarith
  have hKI₁ : σ.slicing.intervalProp C a₁ b₁ K :=
    σ.slicing.intervalProp_mono C ha hb hKI
  have hQI₁ : σ.slicing.intervalProp C a₁ b₁ Q :=
    σ.slicing.intervalProp_mono C ha hb hQI
  have hKI_mid : σ.slicing.intervalProp C a₂ b₁ K :=
    σ.slicing.intervalProp_mono C (show a₂ ≤ a₂ by linarith) hb hKI
  have hK_phase₁ :
      wPhaseOf (W (K₀.of C K)) ((a₁ + b₁) / 2) ≤ ψ :=
    hSS.2.2.2.2 hT hKI₁ hQI₁ hKne
  have hK_eq_lower :
      wPhaseOf (W (K₀.of C K)) ((a₂ + b₁) / 2) =
        wPhaseOf (W (K₀.of C K)) ((a₁ + b₁) / 2) :=
    wPhaseOf_eq_of_intervalProp_lower_inclusion
      (C := C) (σ := σ) (W := W) (hW := hW) ha₂b₁ hab₁ ha hKI_mid hKne
      hε₀ hε₀2 hthin₁ hsin
  have hK_eq_upper :
      wPhaseOf (W (K₀.of C K)) ((a₂ + b₂) / 2) =
        wPhaseOf (W (K₀.of C K)) ((a₂ + b₁) / 2) :=
    wPhaseOf_eq_of_intervalProp_upper_inclusion
      (C := C) (σ := σ) (W := W) (hW := hW) hab₂ hb hKI hKne
      hε₀ hε₀2 hthin_mid hsin
  rw [hK_eq_upper, hK_eq_lower]
  exact hK_phase₁

private theorem semistable_of_target_envelope
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    [IsTriangulated C]
    {a₁ a₂ b₁ b₂ ψ ε₀ : ℝ}
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂)
    {E : C}
    (hSS : (σ.skewedStabilityFunction_of_near C W hW hab₁).Semistable C E ψ)
    (hI₂ : σ.slicing.intervalProp C a₂ b₂ E)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (henv₁_lo : a₁ + ε₀ ≤ ψ) (henv₁_hi : ψ ≤ b₁ - ε₀)
    (henv₂_lo : a₂ + ε₀ ≤ ψ) (henv₂_hi : ψ ≤ b₂ - ε₀)
    (hthin₁ : b₁ - a₁ + 2 * ε₀ < 1)
    (hthin₂ : b₂ - a₂ + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀))) :
    (σ.skewedStabilityFunction_of_near C W hW hab₂).Semistable C E ψ := by
  set a : ℝ := max a₁ a₂
  set b : ℝ := min b₁ b₂
  have ha₁ : a₁ ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have ha₂ : a₂ ≤ a := by
    dsimp [a]
    exact le_max_right _ _
  have hb₁ : b ≤ b₁ := by
    dsimp [b]
    exact min_le_left _ _
  have hb₂ : b ≤ b₂ := by
    dsimp [b]
    exact min_le_right _ _
  have hab : a < b := by
    have hlow₁ : a₁ ≤ ψ - ε₀ := by
      linarith
    have hlow₂ : a₂ ≤ ψ - ε₀ := by
      linarith
    have hlow : a ≤ ψ - ε₀ := by
      dsimp [a]
      exact max_le_iff.mpr ⟨hlow₁, hlow₂⟩
    have hhigh₁ : ψ + ε₀ ≤ b₁ := by
      linarith
    have hhigh₂ : ψ + ε₀ ≤ b₂ := by
      linarith
    have hhigh : ψ + ε₀ ≤ b := by
      dsimp [b]
      exact le_min_iff.mpr ⟨hhigh₁, hhigh₂⟩
    linarith
  have hI : σ.slicing.intervalProp C a b E := by
    by_cases hEZ : IsZero E
    · exact Or.inl hEZ
    · refine σ.slicing.intervalProp_of_intrinsic_phases C hEZ ?_ ?_
      · dsimp [a]
        exact max_lt_iff.mpr
          ⟨σ.slicing.phiMinus_gt_of_intervalProp C hEZ hSS.1,
            σ.slicing.phiMinus_gt_of_intervalProp C hEZ hI₂⟩
      · dsimp [b]
        exact lt_min_iff.mpr
          ⟨σ.slicing.phiPlus_lt_of_intervalProp C hEZ hSS.1,
            σ.slicing.phiPlus_lt_of_intervalProp C hEZ hI₂⟩
  have henv_lo : a + ε₀ ≤ ψ := by
    have hlow : a ≤ ψ - ε₀ := by
      dsimp [a]
      exact max_le_iff.mpr ⟨by linarith [henv₁_lo], by linarith [henv₂_lo]⟩
    linarith
  have henv_hi : ψ ≤ b - ε₀ := by
    have hhigh : ψ + ε₀ ≤ b := by
      dsimp [b]
      exact le_min_iff.mpr ⟨by linarith [henv₁_hi], by linarith [henv₂_hi]⟩
    linarith
  have hthin : b - a + 2 * ε₀ < 1 := by
    have hthin₁' : b - a + 2 * ε₀ ≤ b₁ - a₁ + 2 * ε₀ := by
      linarith
    have hthin₂' : b - a + 2 * ε₀ ≤ b₂ - a₂ + 2 * ε₀ := by
      linarith
    exact lt_of_le_of_lt hthin₁' hthin₁
  have hmid :
      (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E ψ :=
    semistable_of_target_subinterval
      (C := C) (σ := σ) (W := W) (hW := hW) hab₁ hab
      (show a₁ ≤ a by dsimp [a]; exact le_max_left _ _) (show b ≤ b₁ by
        dsimp [b]
        exact min_le_left _ _) hSS hI hε₀ hε₀2 henv_lo henv_hi hthin₁ hthin hsin
  exact semistable_of_interval_inclusion
    (C := C) (σ := σ) (W := W) (hW := hW) hab hab₂
    (show a₂ ≤ a by dsimp [a]; exact le_max_right _ _) (show b ≤ b₂ by
      dsimp [b]
      exact min_le_right _ _) hmid hε₀ hε₀2 henv_lo henv_hi hthin₂ hsin

variable [IsTriangulated C] in
/-- A nonzero strict quotient of a `W`-semistable interval object has `W`-phase at least
that of the source object, assuming all nonzero interval objects lie in a common branch
window of width `< 1`. This is the thin-category analogue of the quotient-side
semistability inequality in Proposition 2.4. -/
private theorem SkewedStabilityFunction.phase_le_of_strictQuotient_of_window
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : σ.slicing.IntervalCat C a b} {ψ : ℝ}
    (hX : ssf.Semistable C X.obj ψ)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (p : X ⟶ Y) (hp : IsStrictEpi p)
    (hY : ¬IsZero Y.obj) :
    ψ ≤ wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α := by
  by_cases hKz : IsZero (kernel p).obj
  · have hKz' : IsZero (kernel p) :=
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hKz
    have hkernel_zero : kernel.ι p = 0 := zero_of_source_iso_zero _ hKz'.isoZero
    haveI : Mono p := Preadditive.mono_of_kernel_zero hkernel_zero
    haveI : IsIso p := IsStrictEpi.isIso hp
    let eC : X.obj ≅ Y.obj :=
      ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso (asIso p))
    rw [← hX.2.2.2.1, ← K₀.of_iso C eC]
  · have hK : ¬IsZero (kernel p).obj := hKz
    let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
      ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : StrictShortExact S :=
      interval_strictShortExact_of_kernel_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) S (kernelIsKernel p) hp
    obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := σ.slicing) (a := a) (b := b) hS
    have hK_le :
        wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ≤ ψ :=
      hX.2.2.2.2 hT (kernel p).property Y.property hK
    have hX_phase :
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α = ψ := hX.2.2.2.1
    have hX_window :
        L < wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α ∧
          wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α < U := by
      exact hWindow X.property hX.2.1
    have hK_window :
        L < wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ∧
          wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α < U := by
      exact hWindow (kernel p).property hK
    have hY_window :
        L < wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α ∧
          wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α < U := by
      exact hWindow Y.property hY
    have hK_range :
        wPhaseOf (ssf.W (K₀.of C (kernel p).obj)) ssf.α ∈ Set.Ioc (ψ - 1) ψ := by
      constructor
      · linarith [hK_window.1, hX_window.2, hWidth, hX_phase]
      · exact hK_le
    have hY_range :
        wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α ∈ Set.Ioo (ψ - 1) (ψ + 1) := by
      constructor
      · linarith [hY_window.1, hX_window.2, hWidth, hX_phase]
      · linarith [hY_window.2, hX_window.1, hWidth, hX_phase]
    have hY_Wne : ssf.W (K₀.of C Y.obj) ≠ 0 := hW_interval Y.property hY
    have hadd :
        ssf.W (K₀.of C X.obj) =
          ssf.W (K₀.of C (kernel p).obj) +
            ssf.W (K₀.of C Y.obj) := by
      simpa [S, map_add] using congrArg ssf.W
        (Slicing.IntervalCat.K0_of_strictShortExact (C := C) (s := σ.slicing)
          (a := a) (b := b) hS)
    exact wPhaseOf_seesaw hadd.symm hX.2.2.2.1 hK_range hY_Wne hY_range

variable [IsTriangulated C] in
/-- A minimal-phase strict kernel has semistable strict quotient. This is the mdq step used
for the thin-interval HN recursion. The only quotient-side hypothesis needed is plain
phase minimality among proper strict kernels. -/
private theorem SkewedStabilityFunction.phase_cokernel_lt_of_phase_gt_strictSubobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {Y : σ.slicing.IntervalCat C a b} {A : Subobject Y}
    (hA_ne_bot : A ≠ ⊥) (hA_ne_top : A ≠ ⊤) (hA_strict : IsStrictMono A.arrow)
    (hA_phase_gt :
      wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1) :
    wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α := by
  let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hA_obj_ne : ¬IsZero (A : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hA_ne_bot <|
        Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  have hY_obj_ne : ¬IsZero Y.obj := by
    intro hZ
    have hY_zero : IsZero Y :=
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ
    have hA_zero : IsZero (A : σ.slicing.IntervalCat C a b) := IsZero.of_mono A.arrow hY_zero
    exact hA_obj_ne (((σ.slicing.intervalProp C a b).ι).map_isZero hA_zero)
  have hY_window : L < ψY ∧ ψY < U := by
    simpa [ψY] using hWindow Y.property hY_obj_ne
  have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hA_window :
      L < wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α < U := by
    exact hWindow (A : σ.slicing.IntervalCat C a b).property hA_obj_ne
  have hcokA_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel A.arrow).property hcokA_obj_ne
  have hA_Wne : ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj) ≠ 0 :=
    hW_interval (A : σ.slicing.IntervalCat C a b).property hA_obj_ne
  have hA_range :
      wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> dsimp [ψY] <;> linarith [hA_window.1, hA_window.2, hY_window.1, hY_window.2,
      hWidth]
  have hcokA_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> dsimp [ψY] <;> linarith [hcokA_window.1, hcokA_window.2, hY_window.1,
      hY_window.2, hWidth]
  have haddY :
      ssf.W (K₀.of C Y.obj) =
        ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel A.arrow).obj) := by
    simpa [map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow hA_strict)
  exact wPhaseOf_seesaw_dual haddY.symm rfl hA_phase_gt hA_Wne hA_range hcokA_range

private def ThinFiniteLengthInInterval (σ : StabilityCondition C) (a b : ℝ)
    [Fact (a < b)] [Fact (b - a ≤ 1)] : Prop :=
  ∀ Y : σ.slicing.IntervalCat C a b,
    IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y

private theorem ThinFiniteLengthInInterval.of_wide
    (σ : StabilityCondition C) {ε₀ t a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (ha : t - 4 * ε₀ ≤ a) (hb : b ≤ t + 4 * ε₀)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8) :
    ThinFiniteLengthInInterval (C := C) σ a b := by
  let a' : ℝ := t - 4 * ε₀
  let b' : ℝ := t + 4 * ε₀
  letI : Fact (a' < b') := ⟨by
    dsimp [a', b']
    linarith [hε₀]⟩
  letI : Fact (b' - a' ≤ 1) := ⟨by
    dsimp [a', b']
    linarith [hε₀8]⟩
  let hIncl : σ.slicing.intervalProp C a b ≤ σ.slicing.intervalProp C a' b' := by
    intro F hF
    exact σ.slicing.intervalProp_mono C ha hb hF
  intro X
  exact interval_thinFiniteLength_of_inclusion_strict
    (C := C) (s₁ := σ.slicing) (s₂ := σ.slicing)
    (a₁ := a) (b₁ := b) (a₂ := a') (b₂ := b') hIncl (hWide t) X

private theorem ThinFiniteLengthInInterval.of_ambient
    (σ : StabilityCondition C) {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : σ.slicing.intervalProp C a₁ b₁ ≤ σ.slicing.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : σ.slicing.IntervalCat C a₂ b₂,
      IsArtinianObject Y ∧ IsNoetherianObject Y) :
    ThinFiniteLengthInInterval (C := C) σ a₁ b₁ := by
  intro X
  exact interval_thinFiniteLength_of_inclusion
    (C := C) (s₁ := σ.slicing) (s₂ := σ.slicing)
    (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) h hFinite X

private theorem thinFiniteLength_of_node78_window
    (σ : StabilityCondition C) {ε₀ t : ℝ}
    [Fact (t - 3 * ε₀ < t + 5 * ε₀)]
    [Fact ((t + 5 * ε₀) - (t - 3 * ε₀) ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8) :
    ThinFiniteLengthInInterval (C := C) σ (t - 3 * ε₀) (t + 5 * ε₀) := by
  refine ThinFiniteLengthInInterval.of_wide
    (C := C) σ (t := t + ε₀) hε₀ hε₀8 ?_ ?_ hWide
  · dsimp
    linarith
  · dsimp
    linarith

variable [IsTriangulated C] in
/-- Faithful strict finite-length quotient selection for thin interval categories:
every nonzero interval object admits a semistable strict quotient whose phase is at most
that of the object. This is the strict-kernel analogue of Proposition 2.4's first
quotient-selection step, and uses only strict chain conditions, not finite enumeration
of all subobjects. -/
private theorem SkewedStabilityFunction.exists_semistable_strictQuotient_le_phase_of_finiteLength
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      ssf.Semistable C (cokernel M.arrow).obj
        (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α) ∧
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
  let phaseQ : Subobject X → ℝ := fun M ↦
    wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  have h :
      ∀ S : StrictSubobject X, ¬IsZero (cokernel S.1.arrow) →
        ∃ T : StrictSubobject X,
          S.1 ≤ T.1 ∧
          ssf.Semistable C (cokernel T.1.arrow).obj (phaseQ T.1) ∧
          phaseQ T.1 ≤ phaseQ S.1 := by
    intro S hQS_ne
    revert hQS_ne
    induction S using IsWellFounded.induction (· > · : StrictSubobject X → StrictSubobject X → Prop) with
    | ind S ih =>
        intro hQS_ne
        have hS_ne_top : S.1 ≠ ⊤ := by
          intro hS_top
          haveI : IsIso S.1.arrow := (Subobject.isIso_iff_mk_eq_top S.1.arrow).2
            (by simpa [Subobject.mk_arrow] using hS_top)
          exact hQS_ne (isZero_cokernel_of_epi S.1.arrow)
        let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
        letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
        by_cases hQS_ss : ssf.Semistable C QS.obj (phaseQ S.1)
        · exact ⟨S, le_rfl, hQS_ss, le_rfl⟩
        · obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
            ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
              (C := C) (σ := σ) (a := a) (b := b) (X := QS) hQS_ne hQS_ss hW_interval
          let pbA : Subobject X := (Subobject.pullback (cokernel.π S.1.arrow)).obj A
          have hpb_strict : IsStrictMono pbA.arrow :=
            interval_pullback_arrow_strictMono_of_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π S.1.arrow) A hA_strict
          let T : StrictSubobject X := ⟨pbA, hpb_strict⟩
          have hS_lt_T : S < T := by
            apply lt_of_lt_of_le
              (interval_lt_pullback_cokernel_of_ne_bot
                (C := C) (s := σ.slicing) (a := a) (b := b) (M := S.1) (B := A) hA_ne_bot)
            exact le_rfl
          have hpb_ne_top : pbA ≠ ⊤ :=
            interval_pullback_cokernel_ne_top_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict
          have hQT_ne : ¬IsZero (cokernel pbA.arrow) :=
            interval_cokernel_nonzero_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hpb_ne_top hpb_strict
          obtain ⟨U, hTU_le, hU_ss, hU_phase⟩ := ih T hS_lt_T hQT_ne
          have hpb_phase_eq :
              phaseQ pbA =
                wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
            dsimp [phaseQ, pbA]
            rw [ssf.Wobj_cokernel_pullback_eq
              (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) S.1 S.2
              (B := A) hA_strict]
          have hpb_phase_lt : phaseQ pbA < phaseQ S.1 := by
            rw [hpb_phase_eq]
            exact ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
              (C := C) (σ := σ) (a := a) (b := b)
              hA_ne_bot hA_ne_top hA_strict hA_phase_gt hW_interval hWindow hWidth
          exact ⟨U, le_trans hS_lt_T.le hTU_le, hU_ss, le_trans hU_phase hpb_phase_lt.le⟩
  let S0 : StrictSubobject X := ⟨⊥,
    intervalSubobject_bot_arrow_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b)⟩
  have hS0_ne : ¬IsZero (cokernel S0.1.arrow) := by
    let eI : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    intro hZ
    exact hX (hZ.of_iso eI.symm)
  obtain ⟨T, _, hT_ss, hT_phase_le⟩ := h S0 hS0_ne
  have hT_ne_top : T.1 ≠ ⊤ := by
    intro hT_top
    haveI : IsIso T.1.arrow := (Subobject.isIso_iff_mk_eq_top T.1.arrow).2
      (by simpa [Subobject.mk_arrow] using hT_top)
    have hzero_obj : IsZero (cokernel T.1.arrow).obj := by
      exact ((σ.slicing.intervalProp C a b).ι).map_isZero (isZero_cokernel_of_epi T.1.arrow)
    exact hT_ss.2.1 hzero_obj
  have hphase0 :
      phaseQ S0.1 = wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
    let eI : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    let eC : (cokernel ((⊥ : Subobject X).arrow)).obj ≅ X.obj :=
      (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
    simpa [phaseQ, S0] using
      congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
  exact ⟨T.1, hT_ne_top, T.2, hT_ss, hT_phase_le.trans_eq hphase0⟩

variable [IsTriangulated C] in
/-- A strict maximally destabilizing quotient in a thin interval category. This is the
quasi-abelian analogue of `StabilityFunction.IsMDQ`: the quotient is strict epi, nonzero,
semistable, minimal among semistable strict quotients, and equality of phase forces
factorization through it. -/
private structure IsStrictMDQ
    (σ : StabilityCondition C) {a b : ℝ}
    (ssf : SkewedStabilityFunction C σ.slicing a b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X B : σ.slicing.IntervalCat C a b} (q : X ⟶ B) : Prop where
  strictEpi : IsStrictEpi q
  nonzero : ¬IsZero B.obj
  semistable :
    ssf.Semistable C B.obj
      (wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α)
  minimal :
    ∀ {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B'), IsStrictEpi q' →
      ¬IsZero B'.obj →
      ssf.Semistable C B'.obj
        (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α) →
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α ∧
        (wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α =
            wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α →
          ∃ t : B ⟶ B', q' = q ≫ t)

variable [IsTriangulated C] in
/-- A semistable interval object is its own strict mdq. -/
private theorem IsStrictMDQ.id_of_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X : σ.slicing.IntervalCat C a b}
    (hss : ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)) :
    IsStrictMDQ (C := C) σ ssf (𝟙 X) where
  strictEpi := by
    simpa using (isStrictEpi_of_isIso (f := 𝟙 X))
  nonzero := hss.2.1
  semistable := hss
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    refine ⟨?_, ?_⟩
    · exact ssf.phase_le_of_strictQuotient_of_window
        (C := C) (σ := σ) (a := a) (b := b) hss hW_interval hWindow hWidth q' hq' hB'_nz
    · intro hEq
      exact ⟨q', by simpa [hEq] using (Category.id_comp q').symm⟩

variable [IsTriangulated C] in
/-- Precomposing a strict mdq with an isomorphism of sources preserves the strict mdq property. -/
private theorem IsStrictMDQ.precomposeIso
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X X' B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q) (e : X' ≅ X) :
    IsStrictMDQ (C := C) σ ssf (e.hom ≫ q) where
  strictEpi := by
    exact Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) e.hom q
      (isStrictEpi_of_isIso (f := e.hom)) hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    let q'' : X ⟶ B' := e.inv ≫ q'
    have hq'' : IsStrictEpi q'' := by
      exact Slicing.IntervalCat.comp_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) e.inv q'
        (isStrictEpi_of_isIso (f := e.inv)) hq'
    refine ⟨(hq.minimal q'' hq'' hB'_nz hB'_ss).1, ?_⟩
    intro hEq
    obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
    refine ⟨t, ?_⟩
    change q' = (e.hom ≫ q) ≫ t
    calc
      q' = e.hom ≫ (e.inv ≫ q') := by simp [Category.assoc]
      _ = e.hom ≫ (q ≫ t) := by simpa [q''] using congrArg (fun f : X ⟶ B' => e.hom ≫ f) ht
      _ = (e.hom ≫ q) ≫ t := by rw [Category.assoc]

variable [IsTriangulated C] in
/-- If `p` and `p ≫ q` are strict epimorphisms in a thin interval category, then `q` is a
strict epimorphism. This is detected in the left heart, where it reduces to the usual
epimorphism factor property in an abelian category. -/
private theorem interval_strictEpi_of_strictEpi_comp
    (σ : StabilityCondition C) {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Q B : σ.slicing.IntervalCat C a b}
    (p : X ⟶ Q) (q : Q ⟶ B)
    (hp : IsStrictEpi p) (hpq : IsStrictEpi (p ≫ q)) :
    IsStrictEpi q := by
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := σ.slicing) a b (Fact.out : b - a ≤ 1)
  haveI : Epi (FL.map p) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) p hp
  haveI : Epi (FL.map (p ≫ q)) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) (p ≫ q) hpq
  have hfac : FL.map p ≫ FL.map q = FL.map (p ≫ q) := by simp
  haveI : Epi (FL.map q) := epi_of_epi_fac hfac
  exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
    (C := C) (s := σ.slicing) (a := a) (b := b) q

variable [IsTriangulated C] in
/-- If a strict mdq factors through a strict epi `X ↠ Q`, then the induced quotient `Q ↠ B`
is again a strict mdq. -/
private theorem IsStrictMDQ.of_strictEpi_factor
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Q B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q) {p : X ⟶ Q}
    (hp : IsStrictEpi p) {πQ : Q ⟶ B} (hfac : p ≫ πQ = q) :
    IsStrictMDQ (C := C) σ ssf πQ where
  strictEpi := by
    apply interval_strictEpi_of_strictEpi_comp (C := C) (σ := σ) (a := a) (b := b) p πQ hp
    simpa [hfac] using hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    have hcomp : IsStrictEpi (p ≫ q') := by
      exact Slicing.IntervalCat.comp_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) p q' hp hq'
    refine ⟨(hq.minimal (p ≫ q') hcomp hB'_nz hB'_ss).1, ?_⟩
    intro hEq
    obtain ⟨t, ht⟩ := (hq.minimal (p ≫ q') hcomp hB'_nz hB'_ss).2 hEq
    refine ⟨t, ?_⟩
    haveI : Epi p := hp.epi
    apply (cancel_epi p).1
    calc
      p ≫ q' = q ≫ t := ht
      _ = (p ≫ πQ) ≫ t := by simpa [hfac]
      _ = p ≫ (πQ ≫ t) := by rw [Category.assoc]

variable [IsTriangulated C] in
/-- The phase of a strict mdq is bounded above by the phase of any nonzero strict quotient
of its source. -/
private theorem IsStrictMDQ.phase_le_of_strictQuotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B Q : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (p : X ⟶ Q) (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj) :
    wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
      wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α := by
  obtain ⟨M, hM_ne_top, hM_strict, hM_ss, hM_phase⟩ :=
    ssf.exists_semistable_strictQuotient_le_phase_of_finiteLength
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      (X := Q) (fun hZ => hQ (((σ.slicing.intervalProp C a b).ι).map_isZero hZ))
  have hcomp : IsStrictEpi (p ≫ cokernel.π M.arrow) := by
    exact Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) p (cokernel.π M.arrow) hp
      (isStrictEpi_cokernel M.arrow)
  have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
    intro hZ
    exact (interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict)
      (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  exact (hq.minimal (p ≫ cokernel.π M.arrow) hcomp
    hcokM_obj_ne
    hM_ss).1.trans hM_phase

variable [IsTriangulated C] in
/-- If a nonzero strict quotient of the source has the same phase as a strict mdq, then it is
already semistable. Otherwise a destabilizing semistable strict subobject would produce a
smaller-phase strict quotient, contradicting mdq minimality. -/
private theorem IsStrictMDQ.isSemistable_of_strictQuotient_phase_eq
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B Q : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (p : X ⟶ Q) (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj)
    (hEq :
      wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α =
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α) :
    ssf.Semistable C Q.obj
      (wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α) := by
  letI : IsStrictArtinianObject Q := (hFiniteLength Q).1
  by_contra hQ_ns
  obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
    ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
      (C := C) (σ := σ) (a := a) (b := b) (X := Q)
      (fun hZ => hQ (((σ.slicing.intervalProp C a b).ι).map_isZero hZ))
      hQ_ns hW_interval
  have hcomp : IsStrictEpi (p ≫ cokernel.π A.arrow) := by
    exact Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) p (cokernel.π A.arrow) hp
      (isStrictEpi_cokernel A.arrow)
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact (interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict)
      (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hmin :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α :=
    IsStrictMDQ.phase_le_of_strictQuotient
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      hq (p ≫ cokernel.π A.arrow) hcomp hcokA_obj_ne
  have hlt :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α := by
    calc
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α :=
        ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
          (C := C) (σ := σ) (a := a) (b := b)
          hA_ne_bot hA_ne_top hA_strict hA_phase_gt hW_interval hWindow hWidth
      _ = wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α := hEq
  exact (not_lt_of_ge hmin) hlt

variable [IsTriangulated C] in
/-- Equality of phase with a strict mdq forces factorization through that mdq. -/
private theorem IsStrictMDQ.factor_of_phase_eq_of_strictQuotient
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B Q : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (p : X ⟶ Q) (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj)
    (hEq :
      wPhaseOf (ssf.W (K₀.of C Q.obj)) ssf.α =
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α) :
    ∃ t : B ⟶ Q, p = q ≫ t := by
  have hQ_ss := IsStrictMDQ.isSemistable_of_strictQuotient_phase_eq
    (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
    hq p hp hQ hEq
  obtain ⟨t, ht⟩ := (hq.minimal p hp hQ hQ_ss).2 hEq
  exact ⟨t, ht⟩

variable [IsTriangulated C] in
/-- Recursive mdq step in a thin interval category: if `0 → A → X → X' → 0` is a strict short
exact sequence with `A` semistable of larger phase, then any strict mdq of `X'` pulls back to a
strict mdq of `X`, provided maps from higher-phase semistables to lower-phase semistables vanish.

This is the quasi-abelian analogue of the Proposition 2.4/Bridgeland 7.7b transport step. -/
private theorem IsStrictMDQ.comp_of_destabilizing_semistable_subobject
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (hE : ssf.Semistable C E.obj
          (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
        (hF : ssf.Semistable C F.obj
          (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
        wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α →
        ∀ f : E ⟶ F, f = 0)
    {X : σ.slicing.IntervalCat C a b} {A : Subobject X}
    (hA_ss :
      ssf.Semistable C (A : σ.slicing.IntervalCat C a b).obj
        (wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α))
    (hA_strict : IsStrictMono A.arrow)
    (hA_phase :
      wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α)
    (hA_top : A ≠ ⊤)
    {B : σ.slicing.IntervalCat C a b} {q : cokernel A.arrow ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q) :
    IsStrictMDQ (C := C) σ ssf (cokernel.π A.arrow ≫ q) where
  strictEpi := by
    exact Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π A.arrow) q
      (isStrictEpi_cokernel A.arrow) hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB'_nz hB'_ss
    have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
      intro hZ
      letI : Epi q := hq.strictEpi.epi
      have hzero : q = 0 := zero_of_source_iso_zero _ <|
        (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ).isoZero
      exact hq.nonzero (((σ.slicing.intervalProp C a b).ι).map_isZero (IsZero.of_epi_eq_zero q hzero))
    have hB_le_cok :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α :=
      IsStrictMDQ.phase_le_of_strictQuotient
        (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
        hq (𝟙 (cokernel A.arrow)) (isStrictEpi_of_isIso (f := 𝟙 _)) hcokA_obj_ne
    have hA_ne_bot : A ≠ ⊥ := by
      intro hA_bot
      exact hA_ss.2.1 (((σ.slicing.intervalProp C a b).ι).map_isZero
        ((intervalSubobject_isZero_iff_eq_bot
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) A).mpr hA_bot))
    have hCok_lt_A :
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
      lt_trans
        (ssf.phase_cokernel_lt_of_phase_gt_strictSubobject
          (C := C) (σ := σ) (a := a) (b := b)
          hA_ne_bot hA_top hA_strict
          hA_phase hW_interval hWindow hWidth)
        hA_phase
    have hB_lt_A :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
      lt_of_le_of_lt hB_le_cok hCok_lt_A
    by_cases hle :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α
    · refine ⟨hle, ?_⟩
      intro hEq
      have hB'_lt_A :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
        rw [hEq]
        exact hB_lt_A
      have hzero : A.arrow ≫ q' = 0 := hHom hA_ss hB'_ss hB'_lt_A (A.arrow ≫ q')
      let q'' : cokernel A.arrow ⟶ B' := cokernel.desc A.arrow q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
          (isStrictEpi_cokernel A.arrow)
        simpa [q''] using hq'
      obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB'_nz hB'_ss).2 hEq
      refine ⟨t, ?_⟩
      calc
        q' = cokernel.π A.arrow ≫ q'' := by
          symm
          exact cokernel.π_desc A.arrow q' hzero
        _ = cokernel.π A.arrow ≫ (q ≫ t) := by rw [ht]
        _ = (cokernel.π A.arrow ≫ q) ≫ t := by rw [Category.assoc]
    · have hlt :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α :=
        lt_of_not_ge hle
      have hB'_lt_A :
          wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α <
            wPhaseOf (ssf.W (K₀.of C (A : σ.slicing.IntervalCat C a b).obj)) ssf.α :=
        lt_trans hlt hB_lt_A
      have hzero : A.arrow ≫ q' = 0 := hHom hA_ss hB'_ss hB'_lt_A (A.arrow ≫ q')
      let q'' : cokernel A.arrow ⟶ B' := cokernel.desc A.arrow q' hzero
      have hq'' : IsStrictEpi q'' := by
        apply interval_strictEpi_of_strictEpi_comp
          (C := C) (σ := σ) (a := a) (b := b) (cokernel.π A.arrow) q''
          (isStrictEpi_cokernel A.arrow)
        simpa [q''] using hq'
      have hmin :
          wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
            wPhaseOf (ssf.W (K₀.of C B'.obj)) ssf.α :=
        (hq.minimal q'' hq'' hB'_nz hB'_ss).1
      exact False.elim ((not_lt_of_ge hmin) hlt)

variable [IsTriangulated C] in
/-- Existence of strict maximally destabilizing quotients under the paper-faithful strict
finite-length hypothesis on the thin interval category. -/
private theorem SkewedStabilityFunction.exists_strictMDQ_of_finiteLength
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (hE : ssf.Semistable C E.obj
          (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
        (hF : ssf.Semistable C F.obj
          (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
        wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α →
        ∀ f : E ⟶ F, f = 0)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ (B : σ.slicing.IntervalCat C a b) (q : X ⟶ B), IsStrictMDQ (C := C) σ ssf q := by
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  suffices h :
      ∀ (S : StrictSubobject X), ¬IsZero (cokernel S.1.arrow) →
        ∃ (B : σ.slicing.IntervalCat C a b) (q : cokernel S.1.arrow ⟶ B),
          IsStrictMDQ (C := C) σ ssf q by
    let S0 : StrictSubobject X := ⟨⊥,
      intervalSubobject_bot_arrow_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b)⟩
    have hS0_ne : ¬IsZero (cokernel S0.1.arrow) := by
      let e0 : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      intro hZ
      exact hX (hZ.of_iso e0.symm)
    obtain ⟨B, q, hq⟩ := h S0 hS0_ne
    let e0 : cokernel S0.1.arrow ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simpa [S0, Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    exact ⟨B, e0.inv ≫ q, IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hq e0.symm⟩
  intro S
  induction S using IsWellFounded.induction
      (· > · : StrictSubobject X → StrictSubobject X → Prop) with
  | ind S ih =>
      intro hQS_ne
      let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
      letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
      letI : IsStrictNoetherianObject QS := (hFiniteLength QS).2
      let ψQS : ℝ := wPhaseOf (ssf.W (K₀.of C QS.obj)) ssf.α
      by_cases hQS_ss : ssf.Semistable C QS.obj ψQS
      · exact ⟨QS, 𝟙 _, IsStrictMDQ.id_of_semistable
          (C := C) (σ := σ) (a := a) (b := b) hW_interval hWindow hWidth hQS_ss⟩
      · obtain ⟨A, hA_ne_bot, hA_ne_top, hA_strict, hA_ss, hA_phase_gt, _⟩ :=
          ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
            (C := C) (σ := σ) (a := a) (b := b) (X := QS) hQS_ne hQS_ss hW_interval
        let Tsub : Subobject X := (Subobject.pullback (cokernel.π S.1.arrow)).obj A
        have hT_strict : IsStrictMono Tsub.arrow :=
          interval_pullback_arrow_strictMono_of_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π S.1.arrow) A hA_strict
        let T : StrictSubobject X := ⟨Tsub, hT_strict⟩
        have hS_lt_T : S < T := by
          apply lt_of_lt_of_le
            (interval_lt_pullback_cokernel_of_ne_bot
              (C := C) (s := σ.slicing) (a := a) (b := b) (M := S.1) (B := A) hA_ne_bot)
          exact le_rfl
        have hQT_ne : ¬IsZero (cokernel Tsub.arrow) :=
          interval_cokernel_nonzero_of_ne_top
            (C := C) (s := σ.slicing) (a := a) (b := b)
            (interval_pullback_cokernel_ne_top_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hA_ne_top hA_strict)
            hT_strict
        obtain ⟨B, qT, hqT⟩ := ih T hS_lt_T hQT_ne
        let eT : cokernel Tsub.arrow ≅ cokernel A.arrow :=
          interval_cokernel_pullbackTopIso
            (C := C) (s := σ.slicing) (a := a) (b := b) S.1 hA_strict
        let qA : cokernel A.arrow ⟶ B := eT.inv ≫ qT
        have hqA : IsStrictMDQ (C := C) σ ssf qA :=
          IsStrictMDQ.precomposeIso (C := C) (σ := σ) (a := a) (b := b) hqT eT.symm
        exact ⟨B, cokernel.π A.arrow ≫ qA,
          IsStrictMDQ.comp_of_destabilizing_semistable_subobject
            (C := C) (σ := σ) (a := a) (b := b)
            hFiniteLength hW_interval hWindow hWidth hHom hA_ss hA_strict hA_phase_gt hA_ne_top hqA⟩

variable [IsTriangulated C] in
private noncomputable def interval_kernelSubobject_isLimitKernelFork
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (q : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelSubobject q).arrow (kernelSubobject_arrow_comp (f := q))) := by
  refine KernelFork.IsLimit.ofι' (kernelSubobject q).arrow (kernelSubobject_arrow_comp (f := q))
    (fun {W} g hg ↦ ?_)
  let u : W ⟶ kernel q := kernel.lift q g hg
  refine ⟨u ≫ (kernelSubobjectIso q).inv, ?_⟩
  calc
    (u ≫ (kernelSubobjectIso q).inv) ≫ (kernelSubobject q).arrow
        = u ≫ kernel.ι q := by simp [Category.assoc]
    _ = g := kernel.lift_ι q g hg

variable [IsTriangulated C] in
private theorem interval_strictShortExact_of_kernelSubobject_strictEpi
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (q : X ⟶ Y) (hq : IsStrictEpi q) :
    StrictShortExact
      (ShortComplex.mk (kernelSubobject q).arrow q (kernelSubobject_arrow_comp (f := q))) := by
  exact interval_strictShortExact_of_kernel_strictEpi
    (C := C) (s := s) (a := a) (b := b)
    (ShortComplex.mk (kernelSubobject q).arrow q (kernelSubobject_arrow_comp (f := q)))
    (interval_kernelSubobject_isLimitKernelFork (C := C) (s := s) (a := a) (b := b) q) hq

private theorem Subobject.map_eq_mk {D : Type*} [Category D] {E : D}
    (K : Subobject E) (S : Subobject (K : D)) :
    (Subobject.map K.arrow).obj S = Subobject.mk (S.arrow ≫ K.arrow) := by
  calc
    (Subobject.map K.arrow).obj S = (Subobject.map K.arrow).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ K.arrow) := by
      simpa using (Subobject.map_mk S.arrow K.arrow)

private noncomputable def Subobject.mapSubIso {D : Type*} [Category D] {E : D}
    (K : Subobject E) (S : Subobject (K : D)) :
    ((Subobject.map K.arrow).obj S : D) ≅ (S : D) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ K.arrow) (Subobject.map_eq_mk K S)

variable [IsTriangulated C] in
private theorem interval_kernelSubobject_ne_top_of_strictEpi_nonzero
    {s : Slicing C} {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} {q : X ⟶ Y} (hq : IsStrictEpi q) (hY : ¬IsZero Y.obj) :
    kernelSubobject q ≠ ⊤ := by
  intro hK
  haveI : Epi q := hq.epi
  haveI : IsIso (kernelSubobject q).arrow := (Subobject.isIso_iff_mk_eq_top _).2
    (by simpa [Subobject.mk_arrow] using hK)
  have hzero : q = 0 := by
    apply (cancel_epi ((kernelSubobject q).arrow)).1
    simpa using (kernelSubobject_arrow_comp (f := q))
  have hY_zero : IsZero Y := IsZero.of_epi_eq_zero q hzero
  exact hY (((s.intervalProp C a b).ι).map_isZero hY_zero)

variable [IsTriangulated C] in
/-- Lemma 3.4 in the quotient form needed for Bridgeland's class `G`: a nonzero strict
quotient of an object from the inner strip `P((a + 2ε₀, b - 4ε₀))`, taken inside the
thin category `P((a, b))`, has `W`-phase strictly bigger than `a + ε₀`. -/
private theorem wPhaseOf_gt_of_strictQuotient_of_inner_strip
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {X B : σ.slicing.IntervalCat C a b}
    (hX_inner : σ.slicing.intervalProp C (a + 2 * ε₀) (b - 4 * ε₀) X.obj)
    (q : X ⟶ B) (hq : IsStrictEpi q) (hBne : ¬IsZero B.obj) :
    a + ε₀ < wPhaseOf (W (K₀.of C B.obj)) ((a + b) / 2) := by
  have hXne : ¬IsZero X.obj := by
    intro hXZ
    have hXI : IsZero X :=
      Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hXZ
    letI : Epi q := hq.epi
    have hq0 : q = 0 := zero_of_source_iso_zero _ hXI.isoZero
    exact hBne (((σ.slicing.intervalProp C a b).ι).map_isZero (IsZero.of_epi_eq_zero q hq0))
  have hinner_lo := σ.slicing.phiMinus_gt_of_intervalProp C hXne hX_inner
  have hinner_hi := σ.slicing.phiPlus_lt_of_intervalProp C hXne hX_inner
  have hab_inner : a + 2 * ε₀ < b - 4 * ε₀ := by
    have hmono := σ.slicing.phiMinus_le_phiPlus C (E := X.obj) hXne
    linarith
  let K : σ.slicing.IntervalCat C a b := kernelSubobject q
  have hK_gt : σ.slicing.gtProp C a K.obj :=
    σ.slicing.gtProp_of_intervalProp C K.property
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      (C := C) (s := σ.slicing) (a := a) (b := b)
      (interval_strictShortExact_of_kernelSubobject_strictEpi
        (C := C) (s := σ.slicing) (a := a) (b := b) q hq)
  have hBminus :
      a + 2 * ε₀ < σ.slicing.phiMinus C B.obj hBne := by
    refine σ.slicing.phiMinus_gt_of_triangle_with_gtProp C (hQ := hBne)
      (a := a + 2 * ε₀)
      (hE_gt := fun _ ↦ σ.slicing.phiMinus_gt_of_intervalProp C hXne hX_inner)
      (c := a) (hK_gt := hK_gt) ?_ hT
    linarith
  have hBge : σ.slicing.geProp C (a + 2 * ε₀) B.obj :=
    σ.slicing.geProp_of_phiMinus_ge C hBne (le_of_lt hBminus)
  have hBge' : σ.slicing.geProp C ((a + ε₀) + ε₀) B.obj := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hBge
  exact wPhaseOf_gt_of_geProp_target
    (C := C) (σ := σ) (W := W) (hW := hW) (a := a) (b := b) (ψ := a + ε₀) (ε₀ := ε₀)
    (E := B.obj)
    (hab := Fact.out) (hI := B.property) (hEne := hBne) (hGe := hBge') hε₀ hε₀2
    (by linarith) (by linarith [hab_inner]) hthin hsin

variable [IsTriangulated C] in
private theorem IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    (hns : ¬ ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α)) :
    kernelSubobject q ≠ ⊥ := by
  intro hK
  have hker_zero : IsZero (kernelSubobject q : σ.slicing.IntervalCat C a b) :=
    (intervalSubobject_isZero_iff_eq_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) (kernelSubobject q)).mpr hK
  have hzero : (kernelSubobject q).arrow = 0 := hker_zero.eq_of_src _ _
  haveI : Mono q := Preadditive.mono_of_kernel_zero <|
    zero_of_source_iso_zero _ (hker_zero.of_iso (kernelSubobjectIso q).symm).isoZero
  haveI : IsIso q := IsStrictEpi.isIso hq.strictEpi
  have eX : X.obj ≅ B.obj := ((σ.slicing.intervalProp C a b).ι).mapIso (asIso q)
  have hssX : ssf.Semistable C X.obj
      (wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α) := by
    have hphase :
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α =
          wPhaseOf (ssf.W (K₀.of C X.obj)) ssf.α := by
      simpa using congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eX).symm
    exact hphase ▸
      (ssf.semistable_of_iso
        (C := C) (s := σ.slicing) (a := a) (b := b) eX.symm hq.semistable)
  exact hns hssX

variable [IsTriangulated C] in
private theorem IsStrictMDQ.phase_lt_of_strictQuotient_of_kernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}
    (hq : IsStrictMDQ (C := C) σ ssf q)
    {A : Subobject (kernelSubobject q : σ.slicing.IntervalCat C a b)}
    (hA_top : A ≠ ⊤) (hA_strict : IsStrictMono A.arrow) :
    wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
  let M : Subobject X := kernelSubobject q
  have hM_strict : IsStrictMono M.arrow := by
    simpa [M] using intervalSubobject_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (kernel.ι q) (isStrictMono_kernel q)
  let liftA : Subobject X := intervalLiftSub (C := C) (X := X) M A
  have hLift_strict : IsStrictMono liftA.arrow := by
    simpa [liftA, M] using
      intervalLiftSub_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) (M := M) hM_strict (A := A) hA_strict
  have hLift_lt : liftA < M := by
    simpa [liftA, M] using intervalLiftSub_lt (C := C) (X := X) M hA_top
  have hLift_ne_top : liftA ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hLift_lt le_top)
  have hcokLift_ne : ¬IsZero (cokernel liftA.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hLift_ne_top hLift_strict
  have hcokLift_obj_ne : ¬IsZero (cokernel liftA.arrow).obj := by
    intro hZ
    exact hcokLift_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hLift_phase_ge :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α :=
    IsStrictMDQ.phase_le_of_strictQuotient
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      hq (cokernel.π liftA.arrow) (isStrictEpi_cokernel liftA.arrow) hcokLift_obj_ne
  have hMp_nonzero : M.arrow ≫ cokernel.π liftA.arrow ≠ 0 := by
    intro hzero
    have hKer : IsLimit (KernelFork.ofι liftA.arrow (cokernel.condition liftA.arrow)) :=
      interval_fIsKernel_of_strictShortExact
        (C := C) (s := σ.slicing) (a := a) (b := b)
        (interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) liftA.arrow hLift_strict)
    let u : (M : σ.slicing.IntervalCat C a b) ⟶ (liftA : σ.slicing.IntervalCat C a b) :=
      hKer.lift (KernelFork.ofι M.arrow hzero)
    have hu : u ≫ liftA.arrow = M.arrow := hKer.fac _ Limits.WalkingParallelPair.zero
    have hM_le_lift : M ≤ liftA := Subobject.le_of_comm u hu
    exact (not_le_of_gt hLift_lt) hM_le_lift
  have hLift_phase_gt :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α := by
    refine lt_of_le_of_ne hLift_phase_ge ?_
    intro hEq
    obtain ⟨t, ht⟩ := IsStrictMDQ.factor_of_phase_eq_of_strictQuotient
      (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
      hq (cokernel.π liftA.arrow) (isStrictEpi_cokernel liftA.arrow) hcokLift_obj_ne hEq.symm
    apply hMp_nonzero
    calc
      M.arrow ≫ cokernel.π liftA.arrow = M.arrow ≫ (q ≫ t) := by rw [ht]
      _ = (M.arrow ≫ q) ≫ t := by simp [Category.assoc]
      _ = 0 := by simp [M]
  have hcokM_ne : ¬IsZero (cokernel M.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b)
      (interval_kernelSubobject_ne_top_of_strictEpi_nonzero
        (C := C) (s := σ.slicing) (a := a) (b := b) hq.strictEpi hq.nonzero) hM_strict
  have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
    intro hZ
    exact hcokM_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hB_window :
      L < wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α < U := hWindow B.property hq.nonzero
  have hLift_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel liftA.arrow).property hcokLift_obj_ne
  have hA_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel A.arrow).property hcokA_obj_ne
  have hUpper : U <
      wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1 := by
    linarith [hWidth, hLift_window.1]
  have hLower :
      wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1 < L := by
    linarith [hWidth, hLift_window.2]
  have hB_range :
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α ∈
        Set.Ioo
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1)
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1) := by
    constructor <;> linarith
  have hA_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∈
        Set.Ioo
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1)
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1) := by
    constructor <;> linarith
  have hB_Wne : ssf.W (K₀.of C B.obj) ≠ 0 := by
    exact hW_interval B.property hq.nonzero
  have hsumX :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C B.obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := σ.slicing) (a := a) (b := b)
        (interval_strictShortExact_of_kernelSubobject_strictEpi
          (C := C) (s := σ.slicing) (a := a) (b := b) q hq.strictEpi)
  have hsumC :
      ssf.W (K₀.of C X.obj) =
        ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := σ.slicing) (a := a) (b := b)
        (interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) M.arrow hM_strict)
  have hWB_eq :
      ssf.W (K₀.of C B.obj) = ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    apply add_left_cancel (a := ssf.W (K₀.of C (M : σ.slicing.IntervalCat C a b).obj))
    exact hsumX.symm.trans hsumC
  have hM_Wne : ssf.W (K₀.of C (cokernel M.arrow).obj) ≠ 0 := by
    intro hzero
    exact hB_Wne (hWB_eq.trans hzero)
  let ψM : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
  have hM_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ∈
        Set.Ioo
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α - 1)
          (wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α + 1) := by
    simpa [hWB_eq] using hB_range
  have hLift_phase_gt_M :
      ψM < wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α := by
    dsimp [ψM]
    rw [← hWB_eq]
    exact hLift_phase_gt
  have hsum :
      ssf.W (K₀.of C (cokernel liftA.arrow).obj) =
        ssf.W (K₀.of C (cokernel A.arrow).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [liftA, M] using
      ssf.Wobj_liftSub_cokernel_eq_add
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict hA_strict
  have hA_phase_gt_lift :
      wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
    exact wPhaseOf_seesaw_strict hsum.symm rfl hLift_phase_gt_M hM_Wne hM_range hA_range
  exact lt_trans hLift_phase_gt hA_phase_gt_lift

variable [IsTriangulated C] in
/-- A minimal-phase strict kernel has semistable strict quotient. This is the mdq step used
for the thin-interval HN recursion. The only quotient-side hypothesis needed is plain
phase minimality among proper strict kernels. -/
private structure IsStrictMDQKernel
    (σ : StabilityCondition C) {a b : ℝ}
    (ssf : SkewedStabilityFunction C σ.slicing a b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} (M : Subobject X) : Prop where
  ne_top : M ≠ ⊤
  strict : IsStrictMono M.arrow
  semistable :
    ssf.Semistable C (cokernel M.arrow).obj
      (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α)
  minimal : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
    wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α

variable [IsTriangulated C] in
/-- A proper strict kernel with semistable quotient of minimal quotient phase packages into the
strict-kernel mdq object used in the faithful Node 7.7 refactor. -/
private theorem SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_ss :
      ssf.Semistable C (cokernel M.arrow).obj
        (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α))
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α) :
    IsStrictMDQKernel (C := C) σ ssf M := by
  exact ⟨hM_ne_top, hM_strict, hM_ss, hM_min⟩

variable [IsTriangulated C] in
private theorem SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hFinSub : ∀ Y : σ.slicing.IntervalCat C a b, Finite (Subobject Y))
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1) :
    ssf.Semistable C (cokernel M.arrow).obj
      (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α) := by
  let Y : σ.slicing.IntervalCat C a b := cokernel M.arrow
  have hY_ne : ¬IsZero Y :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict
  have hY_obj_ne : ¬IsZero Y.obj := by
    intro hZ
    exact hY_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hY_window : L < ψY ∧ ψY < U := by
    simpa [Y, ψY] using hWindow Y.property hY_obj_ne
  by_contra hns
  haveI : Finite (Subobject Y) := hFinSub Y
  obtain ⟨B, hB_ne, hB_strict, hB_max, _⟩ :=
    ssf.exists_maxPhase_maximal_strictSubobject
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hY_ne
  have hB_ne_top : B ≠ ⊤ :=
    ssf.maxPhase_strictSubobject_ne_top_of_not_semistable
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hns hB_ne hB_strict hB_max hW_interval
  have hB_phase_gt :
      ψY < wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α := by
    simpa [Y, ψY] using
      ssf.phase_gt_of_maxPhase_strictSubobject_of_not_semistable
        (C := C) (σ := σ) (a := a) (b := b) (X := Y) (M := B)
        hY_ne hns hB_ne hB_strict hB_max hW_interval
  let pbB : Subobject X := (Subobject.pullback (cokernel.π M.arrow)).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π M.arrow) B hB_strict
  have hpb_ne_top : pbB ≠ ⊤ :=
    interval_pullback_cokernel_ne_top_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_ne : ¬IsZero (cokernel B.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_obj_ne : ¬IsZero (cokernel B.arrow).obj := by
    intro hZ
    exact hcokB_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hB_obj_ne : ¬IsZero (B : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hB_ne <|
        Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  have hB_window :
      L < wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α < U := by
    exact hWindow (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have hcokB_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel B.arrow).property hcokB_obj_ne
  have hUpper : U < ψY + 1 := by
    linarith [hWidth, hY_window.1]
  have hLower : ψY - 1 < L := by
    linarith [hWidth, hY_window.2]
  have hB_range :
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hcokB_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∈ Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hB_Wne : ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) ≠ 0 :=
    hW_interval (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have haddY :
      ssf.W (K₀.of C Y.obj) =
        ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) := by
    simpa [Y, map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.arrow hB_strict)
  have hcokB_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < ψY := by
    exact wPhaseOf_seesaw_dual haddY.symm rfl hB_phase_gt hB_Wne hB_range hcokB_range
  have hpb_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α < ψY := by
    rw [ssf.Wobj_cokernel_pullback_eq
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict
      (B := B) hB_strict]
    exact hcokB_phase_lt
  have hpb_phase_ge :
      ψY ≤ wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α :=
    hM_min pbB hpb_ne_top hpb_strict
  linarith

variable [IsTriangulated C] in
/-- The quotient-semistability step for Node 7.7 using the paper-faithful strict-Artinian
input. If a proper strict kernel has minimal quotient phase, then its strict quotient is
semistable. The proof follows the same pullback contradiction as the legacy finite-subobject
version, but the destabilising strict subobject of the quotient is now chosen by
strict-Artinian descent rather than by finite enumeration. -/
private theorem SkewedStabilityFunction.semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    [IsStrictArtinianObject (cokernel M.arrow)] :
    ssf.Semistable C (cokernel M.arrow).obj
      (wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α) := by
  let Y : σ.slicing.IntervalCat C a b := cokernel M.arrow
  have hY_ne : ¬IsZero Y :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict
  have hY_obj_ne : ¬IsZero Y.obj := by
    intro hZ
    exact hY_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
  have hY_window : L < ψY ∧ ψY < U := by
    simpa [Y, ψY] using hWindow Y.property hY_obj_ne
  by_contra hns
  obtain ⟨B, hB_ne, hB_ne_top, hB_strict, _, hB_phase_gt, _⟩ :=
    ssf.exists_first_strictShortExact_of_not_semistable_of_strictArtinian
      (C := C) (σ := σ) (a := a) (b := b) (X := Y) hY_ne hns hW_interval
  let pbB : Subobject X := (Subobject.pullback (cokernel.π M.arrow)).obj B
  have hpb_strict : IsStrictMono pbB.arrow :=
    interval_pullback_arrow_strictMono_of_strictMono
      (C := C) (s := σ.slicing) (a := a) (b := b) (cokernel.π M.arrow) B hB_strict
  have hpb_ne_top : pbB ≠ ⊤ :=
    interval_pullback_cokernel_ne_top_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_ne : ¬IsZero (cokernel B.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hB_ne_top hB_strict
  have hcokB_obj_ne : ¬IsZero (cokernel B.arrow).obj := by
    intro hZ
    exact hcokB_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hB_obj_ne : ¬IsZero (B : σ.slicing.IntervalCat C a b).obj := by
    intro hZ
    exact intervalSubobject_not_isZero_of_ne_bot
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hB_ne <|
        Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ
  have hB_window :
      L < wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α < U := by
    exact hWindow (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have hcokB_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel B.arrow).property hcokB_obj_ne
  have hUpper : U < ψY + 1 := by
    linarith [hWidth, hY_window.1]
  have hLower : ψY - 1 < L := by
    linarith [hWidth, hY_window.2]
  have hB_range :
      wPhaseOf (ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj)) ssf.α ∈
        Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hcokB_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α ∈ Set.Ioo (ψY - 1) (ψY + 1) := by
    constructor <;> linarith
  have hB_Wne : ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) ≠ 0 :=
    hW_interval (B : σ.slicing.IntervalCat C a b).property hB_obj_ne
  have haddY :
      ssf.W (K₀.of C Y.obj) =
        ssf.W (K₀.of C (B : σ.slicing.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel B.arrow).obj) := by
    simpa [Y, map_add] using congrArg ssf.W
      (interval_K0_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) B.arrow hB_strict)
  have hcokB_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α < ψY := by
    exact wPhaseOf_seesaw_dual haddY.symm rfl hB_phase_gt hB_Wne hB_range hcokB_range
  have hpb_phase_lt :
      wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α < ψY := by
    rw [ssf.Wobj_cokernel_pullback_eq
      (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict
      (B := B) hB_strict]
    exact hcokB_phase_lt
  have hpb_phase_ge :
      ψY ≤ wPhaseOf (ssf.W (K₀.of C (cokernel pbB.arrow).obj)) ssf.α :=
    hM_min pbB hpb_ne_top hpb_strict
  linarith

variable [IsTriangulated C] in
/-- The strict-Artinian quotient-semistability step packages a minimal-phase strict kernel into
the mdq-kernel structure used by the faithful Lemma 7.7 recursion. -/
private theorem SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    [IsStrictArtinianObject (cokernel M.arrow)] :
    IsStrictMDQKernel (C := C) σ ssf M := by
  refine ssf.isStrictMDQKernel_of_minPhase_strictKernel
    (C := C) (σ := σ) (a := a) (b := b) hM_ne_top hM_strict ?_ hM_min
  exact ssf.semistable_cokernel_of_minPhase_strictKernel_of_minimal_of_strictArtinian
    (C := C) (σ := σ) (a := a) (b := b) hM_ne_top hM_strict hM_min
    hW_interval hWindow hWidth

variable [IsTriangulated C] in
/-- Every proper strict quotient of a minimal-phase minimal strict kernel has phase strictly
larger than the phase of the ambient minimal quotient. This is the kernel-recursion step
for thin-interval HN existence. -/
private theorem SkewedStabilityFunction.phase_lt_of_strictQuotient_of_minPhase_strictKernel
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_lt : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow → B < M →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    {A : Subobject (M : σ.slicing.IntervalCat C a b)} (hA_top : A ≠ ⊤)
    (hA_strict : IsStrictMono A.arrow) :
    wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α <
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
  let liftA := intervalLiftSub (C := C) (X := X) M A
  have hLift_strict : IsStrictMono liftA.arrow := by
    simpa [liftA, intervalLiftSub] using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := σ.slicing) (a := a) (b := b) (A.arrow ≫ M.arrow)
        (Slicing.IntervalCat.comp_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow M.arrow hA_strict hM_strict))
  have hLift_lt : liftA < M :=
    intervalLiftSub_lt (C := C) (X := X) M hA_top
  have hLift_ne_top : liftA ≠ ⊤ := ne_top_of_lt hLift_lt
  let ψM : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
  let ψLift : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel liftA.arrow).obj)) ssf.α
  have hLift_phase_gt : ψM < ψLift := by
    simpa [ψM, ψLift] using hM_lt liftA hLift_ne_top hLift_strict hLift_lt
  have hcokM_ne : ¬IsZero (cokernel M.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hM_ne_top hM_strict
  have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict
  have hcokLift_ne : ¬IsZero (cokernel liftA.arrow) :=
    interval_cokernel_nonzero_of_ne_top
      (C := C) (s := σ.slicing) (a := a) (b := b) hLift_ne_top hLift_strict
  have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
    intro hZ
    exact hcokM_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
    intro hZ
    exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hcokLift_obj_ne : ¬IsZero (cokernel liftA.arrow).obj := by
    intro hZ
    exact hcokLift_ne (Slicing.IntervalCat.isZero_of_obj_isZero
      (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
  have hLift_window : L < ψLift ∧ ψLift < U := by
    simpa [ψLift] using hWindow (cokernel liftA.arrow).property hcokLift_obj_ne
  have hM_window : L < ψM ∧ ψM < U := by
    simpa [ψM] using hWindow (cokernel M.arrow).property hcokM_obj_ne
  have hA_window :
      L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α < U := by
    exact hWindow (cokernel A.arrow).property hcokA_obj_ne
  have hUpper : U < ψLift + 1 := by
    linarith [hWidth, hLift_window.1]
  have hLower : ψLift - 1 < L := by
    linarith [hWidth, hLift_window.2]
  have hM_range : ψM ∈ Set.Ioo (ψLift - 1) (ψLift + 1) := by
    constructor <;> linarith
  have hA_range :
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α ∈
        Set.Ioo (ψLift - 1) (ψLift + 1) := by
    constructor <;> linarith
  have hM_Wne : ssf.W (K₀.of C (cokernel M.arrow).obj) ≠ 0 :=
    hW_interval (cokernel M.arrow).property hcokM_obj_ne
  have hsum :
      ssf.W (K₀.of C (cokernel liftA.arrow).obj) =
        ssf.W (K₀.of C (cokernel A.arrow).obj) +
          ssf.W (K₀.of C (cokernel M.arrow).obj) := by
    simpa [liftA] using
      ssf.Wobj_liftSub_cokernel_eq_add
        (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) M hM_strict hA_strict
  have hA_phase_gt_lift :
      ψLift < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
    exact wPhaseOf_seesaw_strict hsum.symm rfl hLift_phase_gt hM_Wne hM_range hA_range
  linarith

variable [IsTriangulated C] in
private theorem thinFiniteLength_cokernel
    (σ : StabilityCondition C) {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow) :
    IsStrictArtinianObject (cokernel M.arrow) ∧
      IsStrictNoetherianObject (cokernel M.arrow) := by
  exact hFiniteLength (cokernel M.arrow)

variable [IsTriangulated C] in
private theorem SkewedStabilityFunction.isStrictMDQKernel_of_minPhase_strictKernel_of_finiteLength
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    {X : σ.slicing.IntervalCat C a b} {M : Subobject X}
    (hM_ne_top : M ≠ ⊤) (hM_strict : IsStrictMono M.arrow)
    (hM_min : ∀ B : Subobject X, B ≠ ⊤ → IsStrictMono B.arrow →
      wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α ≤
        wPhaseOf (ssf.W (K₀.of C (cokernel B.arrow).obj)) ssf.α)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1) :
    IsStrictMDQKernel (C := C) σ ssf M := by
  letI : IsStrictArtinianObject (cokernel M.arrow) :=
    (thinFiniteLength_cokernel (C := C) (σ := σ) (a := a) (b := b)
      hFiniteLength hM_ne_top hM_strict).1
  refine ssf.isStrictMDQKernel_of_minPhase_strictKernel_of_strictArtinian
    (C := C) (σ := σ) (a := a) (b := b) hM_ne_top hM_strict hM_min
    hW_interval hWindow hWidth

variable [IsTriangulated C] in
/-- Legacy thin-interval HN existence, kept temporarily while Node 7.7 is refactored to the
paper-faithful finite-length interface.

This proof still runs on the stronger surrogate hypothesis `Finite (Subobject Y)` for every
interval object `Y`. Bridgeland's Lemma 7.7 is instead stated for a thin quasi-abelian category
of finite length, i.e. chain conditions on strict subobjects / strict quotients in
`P((a, b))` itself. Do not use this theorem on the critical path of the Section 7 proof. -/
private theorem SkewedStabilityFunction.hn_exists_in_thin_interval_of_finiteSubobjects
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFinSub : ∀ Y : σ.slicing.IntervalCat C a b, Finite (Subobject Y))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X) :
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, L < G.φ j ∧ G.φ j < U := by
  let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
  suffices h :
      ∀ (k : ℕ) (Y : σ.slicing.IntervalCat C a b), ¬IsZero Y →
        Nat.card (Subobject Y) ≤ k →
        ∀ (t : ℝ),
          (∀ A : Subobject Y, A ≠ ⊤ → IsStrictMono A.arrow →
            t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α) →
          ∃ G : HNFiltration C Psem Y.obj,
            ∀ j, t < G.φ j ∧ G.φ j < U by
    have hL : ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
        L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
      intro A hA_top hA_strict
      have hcokA_ne : ¬IsZero (cokernel A.arrow) :=
        interval_cokernel_nonzero_of_ne_top
          (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict
      have hcokA_obj_ne : ¬IsZero (cokernel A.arrow).obj := by
        intro hZ
        exact hcokA_ne (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
      exact (hWindow (cokernel A.arrow).property hcokA_obj_ne).1
    exact h _ X hX le_rfl L hL
  intro k
  induction k with
  | zero =>
      intro Y hY hcard t hquot
      haveI : Finite (Subobject Y) := hFinSub Y
      haveI := Fintype.ofFinite (Subobject Y)
      have : 0 < Nat.card (Subobject Y) := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos
      omega
  | succ k ih =>
      intro Y hY hcard t hquot
      let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
      have hY_obj_ne : ¬IsZero Y.obj := by
        intro hZ
        exact hY (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
      by_cases hss : ssf.Semistable C Y.obj ψY
      · refine ⟨HNFiltration.single C Y.obj ψY hss, ?_⟩
        intro j
        have hbot_ne_top : (⊥ : Subobject Y) ≠ ⊤ := by
          intro h
          exact (intervalSubobject_top_ne_bot_of_not_isZero
            (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hY) h.symm
        have hbot_strict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
          intervalSubobject_bot_arrow_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b)
        have hbot_phase_gt :
            t < wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α := by
          exact hquot ⊥ hbot_ne_top hbot_strict
        have hbot_zero :
            ((⊥ : Subobject Y).arrow) =
              (0 : ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) ⟶ Y) := by
          simpa using (Subobject.bot_arrow : (⊥ : Subobject Y).arrow = 0)
        let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
          rw [hbot_zero]
          exact cokernelZeroIsoTarget
        let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
          (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
        have hbot_phase_eq :
            wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α = ψY := by
          simpa [ψY] using
            congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
        have hψY_hi : ψY < U := (hWindow Y.property hY_obj_ne).2
        have hj_lt : j.val < 1 := by
          simpa [HNFiltration.single] using j.is_lt
        have hj0 : j.val = 0 := by
          omega
        have hj : j = ⟨0, by simpa [HNFiltration.single] using (show 0 < 1 by omega)⟩ :=
          Fin.ext hj0
        subst j
        have hbot_phase_gt_zero :
            t < wPhaseOf
              (ssf.W (K₀.of C
                (cokernel
                  (0 : ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) ⟶ Y)).obj)) ssf.α := by
          simpa [hbot_zero] using hbot_phase_gt
        have hbot_phase_eq_zero :
            wPhaseOf
              (ssf.W (K₀.of C
                (cokernel
                  (0 : ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) ⟶ Y)).obj)) ssf.α = ψY := by
          simpa [hbot_zero] using hbot_phase_eq
        have hψY_gt : t < ψY := by
          exact hbot_phase_eq_zero ▸ hbot_phase_gt_zero
        exact ⟨by simpa [HNFiltration.single] using hψY_gt, hψY_hi⟩
      · obtain ⟨M, hM_top, hM_strict, hM_min, hM_lt⟩ :=
          ssf.exists_minPhase_minimal_strictKernel
            (C := C) (σ := σ) (a := a) (b := b) hY hW_interval hss
        by_cases hM_bot : M = ⊥
        · subst hM_bot
          have hss_bot :
              ssf.Semistable C (cokernel ((⊥ : Subobject Y).arrow)).obj
                (wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α) :=
            ssf.semistable_cokernel_of_minPhase_strictKernel_of_minimal
              (C := C) (σ := σ) (a := a) (b := b) hFinSub hM_top hM_strict hM_min
              hW_interval hWindow hWidth
          let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
            rw [show ((⊥ : Subobject Y).arrow) = 0 by simp [Subobject.bot_arrow]]
            exact cokernelZeroIsoTarget
          let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
            (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
          have hphase_bot :
              wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α = ψY := by
            simpa [ψY] using
              congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
          have hssY : ssf.Semistable C Y.obj ψY := by
            exact hphase_bot ▸
              (ssf.semistable_of_iso
                (C := C) (s := σ.slicing) (a := a) (b := b) eC hss_bot)
          exact absurd hssY hss
        · have hM_ne : ¬IsZero (M : σ.slicing.IntervalCat C a b) :=
            intervalSubobject_not_isZero_of_ne_bot
              (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hM_bot
          have hcard_M :
              Nat.card (Subobject (M : σ.slicing.IntervalCat C a b)) <
                Nat.card (Subobject Y) :=
            interval_card_subobject_lt_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hM_top
          let ψQ : ℝ := wPhaseOf (ssf.W (K₀.of C (cokernel M.arrow).obj)) ssf.α
          have hψQ_gt : t < ψQ := by
            simpa [ψQ] using hquot M hM_top hM_strict
          have hψQ_ss :
              ssf.Semistable C (cokernel M.arrow).obj ψQ :=
            ssf.semistable_cokernel_of_minPhase_strictKernel_of_minimal
              (C := C) (σ := σ) (a := a) (b := b) hFinSub hM_top hM_strict hM_min
              hW_interval hWindow hWidth
          have hcokM_ne : ¬IsZero (cokernel M.arrow) :=
            interval_cokernel_nonzero_of_ne_top
              (C := C) (s := σ.slicing) (a := a) (b := b) hM_top hM_strict
          have hcokM_obj_ne : ¬IsZero (cokernel M.arrow).obj := by
            intro hZ
            exact hcokM_ne (Slicing.IntervalCat.isZero_of_obj_isZero
              (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
          have hψQ_hi : ψQ < U := by
            simpa [ψQ] using (hWindow (cokernel M.arrow).property hcokM_obj_ne).2
          have hquot_M :
              ∀ A : Subobject (M : σ.slicing.IntervalCat C a b), A ≠ ⊤ → IsStrictMono A.arrow →
                ψQ < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
            intro A hA_top hA_strict
            simpa [ψQ] using
              (ssf.phase_lt_of_strictQuotient_of_minPhase_strictKernel
                (C := C) (σ := σ) (a := a) (b := b) hM_top hM_strict hM_lt
                hW_interval hWindow hWidth hA_top hA_strict)
          have hcard_M_le : Nat.card (Subobject (M : σ.slicing.IntervalCat C a b)) ≤ k := by
            exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hcard_M hcard)
          obtain ⟨G, hG⟩ := ih (M : σ.slicing.IntervalCat C a b) hM_ne hcard_M_le ψQ hquot_M
          let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
            ShortComplex.mk M.arrow (cokernel.π M.arrow) (cokernel.condition M.arrow)
          have hS : StrictShortExact S :=
            interval_strictShortExact_cokernel_of_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) M.arrow hM_strict
          let H : HNFiltration C Psem Y.obj :=
            HNFiltration.appendStrictFactor (C := C) (s := σ.slicing) (a := a) (b := b)
              (P := Psem) (S := S) G hS ψQ hψQ_ss (fun j => (hG j).1)
          refine ⟨H, ?_⟩
          intro j
          by_cases hj : j.val < G.n
          · have hGj := hG ⟨j.val, hj⟩
            have hGj' : t < G.φ ⟨j.val, hj⟩ ∧ G.φ ⟨j.val, hj⟩ < U := by
              exact ⟨lt_trans hψQ_gt hGj.1, hGj.2⟩
            simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hj] using hGj'
          · have hj_lt : j.val < G.n + 1 := by
              simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using j.is_lt
            have hjEq : j.val = G.n := by
              omega
            have hG_last : G.n < H.n := by
              simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using
                (show G.n < G.n + 1 by omega)
            have hjLast : j = ⟨G.n, hG_last⟩ := Fin.ext hjEq
            subst j
            have hjFalse : ¬G.n < G.n := by omega
            simpa [H, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hjFalse,
              ψQ] using ⟨hψQ_gt, hψQ_hi⟩

variable [IsTriangulated C] in
/-- **Node 7.7 (paper-facing statement).** This is the thin-interval HN theorem in the
shape required by Bridgeland's Lemma 7.7: the thin quasi-abelian category `P((a, b))`
itself is assumed to have finite length, encoded as ACC/DCC on strict subobjects.
The remaining input is the semistable Hom-vanishing supplied by Lemma 7.6. -/
private theorem Subobject.map_eq_mk_mono
    {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (Subobject.map f).obj S = Subobject.mk (S.arrow ≫ f) := by
  calc
    (Subobject.map f).obj S = (Subobject.map f).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ f) := by
      simpa using (Subobject.map_mk S.arrow f)

private noncomputable def Subobject.mapMonoIso
    {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    ((Subobject.map f).obj S : D) ≅ (S : D) :=
  Subobject.isoOfEqMk _ (S.arrow ≫ f) (Subobject.map_eq_mk_mono f S)

private theorem Subobject.ofLE_map_comp_mapMonoIso_hom
    {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
        ((Subobject.map f).monotone h) ≫ (Subobject.mapMonoIso f T).hom =
      (Subobject.mapMonoIso f S).hom ≫ Subobject.ofLE S T h := by
  apply Subobject.eq_of_comp_arrow_eq
  apply (cancel_mono f).1
  simp [Subobject.mapMonoIso, Subobject.map_eq_mk_mono, Category.assoc]

private noncomputable def Subobject.cokernelMapMonoIso
    {D : Type*} [Category D] [HasZeroMorphisms D] [HasCokernels D]
    {X Y : D} (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
      ((Subobject.map f).monotone h)) ≅
      cokernel (Subobject.ofLE S T h) :=
  cokernel.mapIso _ _ (Subobject.mapMonoIso f S) (Subobject.mapMonoIso f T)
    (by simpa [Category.assoc] using (Subobject.ofLE_map_comp_mapMonoIso_hom f h))

private theorem wPhaseOf_cokernel_mapMono_eq
    {s : Slicing C} {a b : ℝ}
    {ssf : SkewedStabilityFunction C s a b}
    [HasCokernels (s.IntervalCat C a b)]
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) [Mono f] {S T : Subobject X} (h : S ≤ T) :
    wPhaseOf
        (ssf.W
          (K₀.of C
            (cokernel (Subobject.ofLE ((Subobject.map f).obj S) ((Subobject.map f).obj T)
              ((Subobject.map f).monotone h))).obj)) ssf.α =
      wPhaseOf
        (ssf.W (K₀.of C (cokernel (Subobject.ofLE S T h)).obj)) ssf.α := by
  let eC :=
    (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso
      (Subobject.cokernelMapMonoIso f h)
  simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)

private noncomputable def interval_cokernelTopIso
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    [HasCokernels (s.IntervalCat C a b)]
    {X : s.IntervalCat C a b} (A : Subobject X) :
    cokernel (Subobject.ofLE A ⊤ le_top) ≅ cokernel A.arrow :=
  (cokernelCompIsIso (Subobject.ofLE A ⊤ le_top) (⊤ : Subobject X).arrow).symm ≪≫
    cokernelIsoOfEq (Subobject.ofLE_arrow (X := A) (Y := ⊤) le_top)

private theorem wPhaseOf_cokernel_ofLE_top_eq
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ssf : SkewedStabilityFunction C s a b}
    [HasCokernels (s.IntervalCat C a b)]
    {X : s.IntervalCat C a b} (A : Subobject X) :
    wPhaseOf (ssf.W (K₀.of C (cokernel (Subobject.ofLE A ⊤ le_top)).obj)) ssf.α =
      wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
  let eC :=
    (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso
      (interval_cokernelTopIso (C := C) (s := s) (a := a) (b := b) A)
  simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)

private theorem wPhaseOf_cokernel_kernelSubobject_eq
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {ssf : SkewedStabilityFunction C s a b}
    {E B : s.IntervalCat C a b} (q : E ⟶ B) (hq : IsStrictEpi q) :
    wPhaseOf (ssf.W (K₀.of C (cokernel (kernelSubobject q).arrow).obj)) ssf.α =
      wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α := by
  have hK_strict : IsStrictMono (kernelSubobject q).arrow := by
    simpa using
      (intervalSubobject_arrow_strictMono_of_strictMono
        (C := C) (s := s) (a := a) (b := b) (kernel.ι q) (isStrictMono_kernel q))
  have hsumB :
      ssf.W (K₀.of C E.obj) =
        ssf.W (K₀.of C (kernelSubobject q : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C B.obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := s) (a := a) (b := b)
        (interval_strictShortExact_of_kernelSubobject_strictEpi
          (C := C) (s := s) (a := a) (b := b) q hq)
  have hsumC :
      ssf.W (K₀.of C E.obj) =
        ssf.W (K₀.of C (kernelSubobject q : s.IntervalCat C a b).obj) +
          ssf.W (K₀.of C (cokernel (kernelSubobject q).arrow).obj) := by
    simpa [map_add] using
      ssf.strict_additive
        (C := C) (s := s) (a := a) (b := b)
        (interval_strictShortExact_cokernel_of_strictMono
          (C := C) (s := s) (a := a) (b := b) (kernelSubobject q).arrow hK_strict)
  have hWB :
      ssf.W (K₀.of C B.obj) =
        ssf.W (K₀.of C (cokernel (kernelSubobject q).arrow).obj) := by
    apply add_left_cancel
      (a := ssf.W (K₀.of C (kernelSubobject q : s.IntervalCat C a b).obj))
    exact hsumB.symm.trans hsumC
  simpa [hWB] using congrArg (fun x ↦ wPhaseOf x ssf.α) hWB.symm

/- The faithful 7.7 recursion with the paper's `G/H`-style input exposed explicitly:
for a fixed interval object `X`, it is enough to know a lower phase bound for all
proper strict quotients of `X`; the recursive kernel step propagates that bound to
smaller strict subobjects. The older `hn_exists_in_thin_interval` theorem is recovered
by feeding in the global lower window bound. -/
set_option maxHeartbeats 800000 in
private theorem SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (hE : ssf.Semistable C E.obj
          (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
        (hF : ssf.Semistable C F.obj
          (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
        wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α →
        ∀ f : E ⟶ F, f = 0)
    (t : ℝ)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X) :
    (∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
      t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α) →
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  intro hquot
  let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
  letI : IsStrictArtinianObject X := (hFiniteLength X).1
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  let S0 : StrictSubobject X := ⟨⊤, isStrictMono_of_isIso⟩
  let Psub : StrictSubobject X → Prop := fun S =>
      ¬IsZero (S.1 : σ.slicing.IntervalCat C a b) →
        ∀ t : ℝ,
          (∀ A : Subobject (S.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
            IsStrictMono A.arrow →
            t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α) →
          ∃ G : HNFiltration C Psem (S.1 : σ.slicing.IntervalCat C a b).obj,
            ∀ j, t < G.φ j ∧ G.φ j < U
  have h :
      ∀ S : StrictSubobject X, Psub S := by
    intro S
    refine (show WellFounded ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
      wellFounded_lt).induction S ?_
    intro S ih hS t hquot
    let Y : σ.slicing.IntervalCat C a b := S.1
    have hS_obj : ¬IsZero Y.obj := by
      intro hZ
      exact hS (Slicing.IntervalCat.isZero_of_obj_isZero
        (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    let ψY : ℝ := wPhaseOf (ssf.W (K₀.of C Y.obj)) ssf.α
    by_cases hss : ssf.Semistable C Y.obj ψY
    · refine ⟨HNFiltration.single C Y.obj ψY hss, ?_⟩
      intro j
      have hbot_ne_top : (⊥ : Subobject Y) ≠ ⊤ := by
        intro hEq
        exact (intervalSubobject_top_ne_bot_of_not_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := Y) hS) hEq.symm
      have hbot_strict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
        intervalSubobject_bot_arrow_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b)
      have hbot_gt :
          t < wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α :=
        hquot ⊥ hbot_ne_top hbot_strict
      have hbot_eq :
          wPhaseOf (ssf.W (K₀.of C (cokernel ((⊥ : Subobject Y).arrow)).obj)) ssf.α = ψY := by
        let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
          rw [show ((⊥ : Subobject Y).arrow) = 0 by simpa [Subobject.bot_arrow]]
          exact cokernelZeroIsoTarget
        let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
          (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
        simpa [ψY] using
          congrArg (fun x => wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC)
      have hψY_hi : ψY < U := (hWindow Y.property hS_obj).2
      have hj_lt : j.val < 1 := by
        simpa [HNFiltration.single] using j.is_lt
      have hj0 : j.val = 0 := by omega
      have hj : j = ⟨0, by simpa [HNFiltration.single] using (show 0 < 1 by omega)⟩ :=
        Fin.ext hj0
      subst j
      have hψY_gt : t < ψY := by
        exact hbot_eq ▸ hbot_gt
      exact ⟨by simpa [HNFiltration.single] using hψY_gt, hψY_hi⟩
    · letI : IsStrictArtinianObject Y := (hFiniteLength Y).1
      letI : IsStrictNoetherianObject Y := (hFiniteLength Y).2
      obtain ⟨B, q, hq⟩ := ssf.exists_strictMDQ_of_finiteLength
        (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth hHom
        (X := Y) hS
      let K : Subobject Y := kernelSubobject q
      have hK_ne_bot : K ≠ ⊥ :=
        IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable
          (C := C) (σ := σ) (a := a) (b := b) hq hss
      have hK_ne_top : K ≠ ⊤ :=
        interval_kernelSubobject_ne_top_of_strictEpi_nonzero
          (C := C) (s := σ.slicing) (a := a) (b := b) hq.strictEpi hq.nonzero
      have hK_strict : IsStrictMono K.arrow := by
        simpa [K] using
          (intervalSubobject_arrow_strictMono_of_strictMono
            (C := C) (s := σ.slicing) (a := a) (b := b) (kernel.ι q) (isStrictMono_kernel q))
      let T : Subobject X := intervalLiftSub (C := C) (X := X) S.1 K
      have hT_ne_bot : T ≠ ⊥ :=
        intervalLiftSub_ne_bot (C := C) (X := X) S.1 hK_ne_bot
      have hT_strict : IsStrictMono T.arrow :=
        intervalLiftSub_arrow_strictMono_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) S.2 hK_strict
      let Tstr : StrictSubobject X := ⟨T, hT_strict⟩
      have hT_lt : Tstr < S := by
        simpa [Tstr, T] using
          (intervalLiftSub_lt (C := C) (X := X) S.1 hK_ne_top)
      have hT_ne : ¬IsZero (T : σ.slicing.IntervalCat C a b) :=
        intervalSubobject_not_isZero_of_ne_bot
          (C := C) (s := σ.slicing) (a := a) (b := b) (X := X) hT_ne_bot
      let ψB : ℝ := wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α
      have hψB_gt : t < ψB := by
        have hgtK :
            t < wPhaseOf (ssf.W (K₀.of C (cokernel K.arrow).obj)) ssf.α :=
          hquot K hK_ne_top hK_strict
        simpa [ψB] using hgtK.trans_eq
          (wPhaseOf_cokernel_kernelSubobject_eq
            (C := C) (s := σ.slicing) (a := a) (b := b) (ssf := ssf) q hq.strictEpi)
      have hψB_hi : ψB < U := by
        simpa [ψB] using (hWindow B.property hq.nonzero).2
      have hquot_T :
          ∀ A : Subobject (T : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
            IsStrictMono A.arrow →
            ψB < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
        intro A hA_top hA_strict
        let eK : (T : σ.slicing.IntervalCat C a b) ≅ (K : σ.slicing.IntervalCat C a b) := by
          dsimp [T, intervalLiftSub]
          exact Subobject.isoOfEqMk _ (K.arrow ≫ S.1.arrow) rfl
        let A' : Subobject (K : σ.slicing.IntervalCat C a b) := (Subobject.map eK.hom).obj A
        have hA'_top : A' ≠ ⊤ := by
          intro hA'
          apply hA_top
          apply (Subobject.map_obj_injective eK.hom)
          calc
            (Subobject.map eK.hom).obj A = A' := by rfl
            _ = ⊤ := hA'
            _ = (Subobject.map eK.hom).obj (⊤ : Subobject (T : σ.slicing.IntervalCat C a b)) := by
              rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso eK.hom]
        have hA'_strict : IsStrictMono A'.arrow := by
          have hcomp : IsStrictMono (A.arrow ≫ eK.hom) :=
            Slicing.IntervalCat.comp_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow eK.hom
              hA_strict isStrictMono_of_isIso
          have hEq : A' = Subobject.mk (A.arrow ≫ eK.hom) := by
            simpa [A'] using (Subobject.map_eq_mk_mono eK.hom A)
          rw [hEq]
          simpa using
            (intervalSubobject_arrow_strictMono_of_strictMono
              (C := C) (s := σ.slicing) (a := a) (b := b) (A.arrow ≫ eK.hom) hcomp)
        have hphase_A :
            wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α =
              wPhaseOf (ssf.W (K₀.of C (cokernel A'.arrow).obj)) ssf.α := by
          let eA : (A : σ.slicing.IntervalCat C a b) ≅ (A' : σ.slicing.IntervalCat C a b) :=
            (Subobject.mapMonoIso eK.hom A).symm
          have hw : A.arrow ≫ eK.hom = eA.hom ≫ A'.arrow := by
            simpa [eA, A', Subobject.mapMonoIso, Subobject.map_eq_mk_mono, Category.assoc]
          let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
            cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA eK hw
          let eC' :=
            (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC
          simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC')
        have hgtA' :
            ψB < wPhaseOf (ssf.W (K₀.of C (cokernel A'.arrow).obj)) ssf.α := by
          simpa [ψB] using
            (IsStrictMDQ.phase_lt_of_strictQuotient_of_kernel
              (C := C) (σ := σ) (a := a) (b := b) hFiniteLength hW_interval hWindow hWidth
              hq (A := A') hA'_top hA'_strict)
        rw [hphase_A]
        exact hgtA'
      obtain ⟨GT, hGT⟩ := ih Tstr hT_lt hT_ne ψB hquot_T
      let eK : (T : σ.slicing.IntervalCat C a b) ≅ (K : σ.slicing.IntervalCat C a b) := by
        dsimp [T, intervalLiftSub]
        exact Subobject.isoOfEqMk _ (K.arrow ≫ S.1.arrow) rfl
      let GK : HNFiltration C Psem (K : σ.slicing.IntervalCat C a b).obj :=
        GT.ofIso C ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eK)
      have hGK : ∀ j, ψB < GK.φ j ∧ GK.φ j < U := by
        simpa [GK] using hGT
      let SQ : ShortComplex (σ.slicing.IntervalCat C a b) :=
        ShortComplex.mk K.arrow q (kernelSubobject_arrow_comp (f := q))
      have hSQ : StrictShortExact SQ :=
        interval_strictShortExact_of_kernelSubobject_strictEpi
          (C := C) (s := σ.slicing) (a := a) (b := b) q hq.strictEpi
      let H : HNFiltration C Psem Y.obj :=
        HNFiltration.appendStrictFactor (C := C) (s := σ.slicing) (a := a) (b := b)
          (P := Psem) (S := SQ) GK hSQ ψB hq.semistable (fun j ↦ (hGK j).1)
      refine ⟨H, ?_⟩
      intro j
      by_cases hj : j.val < GK.n
      · have hGj := hGK ⟨j.val, hj⟩
        have hGj' : t < GK.φ ⟨j.val, hj⟩ ∧ GK.φ ⟨j.val, hj⟩ < U := by
          exact ⟨lt_trans hψB_gt hGj.1, hGj.2⟩
        simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hj] using hGj'
      · have hj_lt : j.val < GK.n + 1 := by
          simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using j.is_lt
        have hjEq : j.val = GK.n := by
          omega
        have hG_last : GK.n < H.n := by
          simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor] using
            (show GK.n < GK.n + 1 by omega)
        have hjLast : j = ⟨GK.n, hG_last⟩ := Fin.ext hjEq
        subst j
        have hjFalse : ¬GK.n < GK.n := by omega
        simpa [H, GK, HNFiltration.appendStrictFactor, HNFiltration.appendFactor, hjFalse,
          ψB] using ⟨hψB_gt, hψB_hi⟩
  have hS0_ne : ¬IsZero (S0.1 : σ.slicing.IntervalCat C a b) := by
    intro hZ
    let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X := by
      exact asIso S0.1.arrow
    exact hX (hZ.of_iso e0.symm)
  have hS0_quot :
      ∀ A : Subobject (S0.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
        IsStrictMono A.arrow →
        t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
    intro A hA_top hA_strict
    let e0 : (S0.1 : σ.slicing.IntervalCat C a b) ≅ X := by
      exact asIso S0.1.arrow
    let A' : Subobject X := (Subobject.map e0.hom).obj A
    have hA'_top : A' ≠ ⊤ := by
      intro hA'
      apply hA_top
      apply (Subobject.map_obj_injective e0.hom)
      calc
        (Subobject.map e0.hom).obj A = A' := by rfl
        _ = ⊤ := hA'
        _ = (Subobject.map e0.hom).obj (⊤ : Subobject (S0.1 : σ.slicing.IntervalCat C a b)) := by
          rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso e0.hom]
    have hA'_strict : IsStrictMono A'.arrow := by
      have hcomp : IsStrictMono (A.arrow ≫ e0.hom) :=
        Slicing.IntervalCat.comp_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) A.arrow e0.hom
          hA_strict isStrictMono_of_isIso
      have hEq : A' = Subobject.mk (A.arrow ≫ e0.hom) := by
        simpa [A'] using (Subobject.map_eq_mk_mono e0.hom A)
      rw [hEq]
      simpa using
        (intervalSubobject_arrow_strictMono_of_strictMono
          (C := C) (s := σ.slicing) (a := a) (b := b) (A.arrow ≫ e0.hom) hcomp)
    have hphase_A :
        wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α =
          wPhaseOf (ssf.W (K₀.of C (cokernel A'.arrow).obj)) ssf.α := by
      let eA : (A : σ.slicing.IntervalCat C a b) ≅ (A' : σ.slicing.IntervalCat C a b) :=
        (Subobject.mapMonoIso e0.hom A).symm
      have hw : A.arrow ≫ e0.hom = eA.hom ≫ A'.arrow := by
        simpa [eA, A', Subobject.mapMonoIso, Subobject.map_eq_mk_mono, Category.assoc]
      let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
        cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA e0 hw
      let eC' :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC
      simpa using congrArg (fun x ↦ wPhaseOf (ssf.W x) ssf.α) (K₀.of_iso C eC')
    rw [hphase_A]
    exact hquot A' hA'_top hA'_strict
  obtain ⟨G0, hG0⟩ := h S0 hS0_ne t hS0_quot
  let eTop : (S0.1 : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso (asIso S0.1.arrow)
  refine ⟨G0.ofIso C eTop, ?_⟩
  intro j
  simpa using hG0 j

set_option maxHeartbeats 800000 in
private theorem SkewedStabilityFunction.hn_exists_in_thin_interval
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (hE : ssf.Semistable C E.obj
          (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
        (hF : ssf.Semistable C F.obj
          (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
        wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α →
        ∀ f : E ⟶ F, f = 0)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X) :
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, L < G.φ j ∧ G.φ j < U := by
  have hL :
      ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
        L < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
    intro A hA_top hA_strict
    have hcokA_ne : ¬IsZero (cokernel A.arrow).obj := by
      intro hZ
      exact (interval_cokernel_nonzero_of_ne_top
        (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict)
        (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    exact (hWindow (cokernel A.arrow).property hcokA_ne).1
  exact
    SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound
      (C := C) (σ := σ) (a := a) (b := b) (ssf := ssf)
      hFiniteLength hW_interval hWindow hWidth hHom L X hX hL

/- Quotient-form wrapper for the faithful 7.7 recursion. This is the interface closest
to Bridgeland's classes `G` and `H`: the lower phase bound is stated directly for
nonzero strict quotients `X ↠ B`, and converted internally to the kernel/cokernel
subobject language used by the recursion. -/
set_option maxHeartbeats 800000 in
private theorem SkewedStabilityFunction.hn_exists_in_thin_interval_of_strictQuotientLowerBound
    (σ : StabilityCondition C) {a b : ℝ}
    {ssf : SkewedStabilityFunction C σ.slicing a b}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      ssf.W (K₀.of C F) ≠ 0)
    {L U : ℝ}
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      L < wPhaseOf (ssf.W (K₀.of C F)) ssf.α ∧
        wPhaseOf (ssf.W (K₀.of C F)) ssf.α < U)
    (hWidth : U - L < 1)
    (hHom :
      ∀ {E F : σ.slicing.IntervalCat C a b}
        (hE : ssf.Semistable C E.obj
          (wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α))
        (hF : ssf.Semistable C F.obj
          (wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α)),
        wPhaseOf (ssf.W (K₀.of C F.obj)) ssf.α <
          wPhaseOf (ssf.W (K₀.of C E.obj)) ssf.α →
        ∀ f : E ⟶ F, f = 0)
    (t : ℝ)
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X)
    (hquot :
      ∀ {B : σ.slicing.IntervalCat C a b} (q : X ⟶ B), IsStrictEpi q → ¬IsZero B.obj →
        t < wPhaseOf (ssf.W (K₀.of C B.obj)) ssf.α) :
    let Psem : ℝ → ObjectProperty C := fun ψ E => ssf.Semistable C E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  have hquot' :
      ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
        t < wPhaseOf (ssf.W (K₀.of C (cokernel A.arrow).obj)) ssf.α := by
    intro A hA_top hA_strict
    have hcokA_ne : ¬IsZero (cokernel A.arrow).obj := by
      intro hZ
      exact (interval_cokernel_nonzero_of_ne_top
        (C := C) (s := σ.slicing) (a := a) (b := b) hA_top hA_strict)
        (Slicing.IntervalCat.isZero_of_obj_isZero
          (C := C) (s := σ.slicing) (a := a) (b := b) hZ)
    exact hquot (cokernel.π A.arrow) (isStrictEpi_cokernel A.arrow) hcokA_ne
  exact
    SkewedStabilityFunction.hn_exists_in_thin_interval_of_quotientLowerBound
      (C := C) (σ := σ) (a := a) (b := b) (ssf := ssf)
      hFiniteLength hW_interval hWindow hWidth hHom t X hX hquot'

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

/-- Extension-closure of `gtProp` over Postnikov towers. -/
private lemma gtProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E)
    (hfactors : ∀ i, s.gtProp C t (P.factor i)) :
    s.gtProp C t E := by
  suffices h : ∀ k (hk : k ≤ P.n),
      s.gtProp C t (P.chain.obj' k (by omega)) by
    have hchain := h P.n le_rfl
    rw [show P.chain.obj' P.n (by omega) = P.chain.right from rfl] at hchain
    exact (s.gtProp C t).prop_of_iso (Classical.choice P.top_iso) hchain
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
      have h₁ : s.gtProp C t T.obj₁ := (s.gtProp C t).prop_of_iso e₁.symm hchain_k
      have h₃ : s.gtProp C t T.obj₃ := hfactors ⟨k, by omega⟩
      have h₂ : s.gtProp C t T.obj₂ := s.gtProp_of_triangle C t h₁ h₃ hT
      exact (s.gtProp C t).prop_of_iso e₂ h₂

/-- Extension-closure of `ltProp` over Postnikov towers. -/
private lemma ltProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E)
    (hfactors : ∀ i, s.ltProp C t (P.factor i)) :
    s.ltProp C t E := by
  suffices h : ∀ k (hk : k ≤ P.n),
      s.ltProp C t (P.chain.obj' k (by omega)) by
    have hchain := h P.n le_rfl
    rw [show P.chain.obj' P.n (by omega) = P.chain.right from rfl] at hchain
    exact (s.ltProp C t).prop_of_iso (Classical.choice P.top_iso) hchain
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
      have h₁ : s.ltProp C t T.obj₁ := (s.ltProp C t).prop_of_iso e₁.symm hchain_k
      have h₃ : s.ltProp C t T.obj₃ := hfactors ⟨k, by omega⟩
      have h₂ : s.ltProp C t T.obj₂ := s.ltProp_of_triangle C t h₁ h₃ hT
      exact (s.ltProp C t).prop_of_iso e₂ h₂

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

lemma StabilityCondition.deformedPred_closedUnderIso (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) :
    (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ).IsClosedUnderIsomorphisms := by
  constructor
  intro E E' e h
  rcases h with hZ | ⟨a, b, hab, hthin, henv_lo, henv_hi, hSS⟩
  · exact Or.inl ((Iso.isZero_iff e).mp hZ)
  · refine Or.inr ⟨a, b, hab, hthin, henv_lo, henv_hi, ?_, ?_, ?_, ?_,
      fun K Q f₁ f₂ f₃ hT hK hQ hKne ↦ ?_⟩
    · rcases hSS.1 with hZ' | ⟨F, hF⟩
      · exact absurd hZ' hSS.2.1
      · exact Or.inr ⟨F.ofIso C e, hF⟩
    · exact fun hE' ↦ hSS.2.1 ((Iso.isZero_iff e.symm).mp hE')
    · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
      exact hSS.2.2.1
    · rw [show K₀.of C E' = K₀.of C E from (K₀.of_iso C e).symm]
      exact hSS.2.2.2.1
    · have hT' : Triangle.mk (f₁ ≫ e.inv) (e.hom ≫ f₂) f₃ ∈ distTriang C :=
        isomorphic_distinguished _ hT _
          (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
            (by simp) (by simp) (by simp))
      exact hSS.2.2.2.2 hT' hK hQ hKne

variable [IsTriangulated C] in
private theorem gtProp_of_lt_phiMinus_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : t < s.phiMinus C E hE) :
    s.gtProp C t E := by
  obtain ⟨F, hn, hlast⟩ := HNFiltration.exists_nonzero_last C s hE
  refine s.gtProp_of_hn C F t (fun j ↦ ?_) hn
  calc
    t < s.phiMinus C E hE := h
    _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C E hE F hn hlast
    _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))

variable [IsTriangulated C] in
private theorem leProp_of_phiPlus_le_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : s.phiPlus C E hE ≤ t) :
    s.leProp C t E := by
  obtain ⟨F, hn, hfirst⟩ := HNFiltration.exists_nonzero_first C s hE
  refine s.leProp_of_hn C F t (fun j ↦ ?_) hn
  calc
    F.φ j ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))
    _ = s.phiPlus C E hE := (s.phiPlus_eq C E hE F hn hfirst).symm
    _ ≤ t := h

variable [IsTriangulated C] in
private theorem geProp_of_phiMinus_ge_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (h : t ≤ s.phiMinus C E hE) :
    s.geProp C t E := by
  obtain ⟨F, hn, hlast⟩ := HNFiltration.exists_nonzero_last C s hE
  refine s.geProp_of_hn C F t (fun j ↦ ?_) hn
  calc
    t ≤ s.phiMinus C E hE := h
    _ = F.φ ⟨F.n - 1, by omega⟩ := s.phiMinus_eq C E hE F hn hlast
    _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))

variable [IsTriangulated C] in
private theorem mem_phaseShiftHeart_of_phaseBounds_smallGap
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (hgt : t < s.phiMinus C E hE)
    (hle : s.phiPlus C E hE ≤ t + 1) :
    ((s.phaseShift C t).toTStructure).heart E := by
  let ss := s.phaseShift C t
  let u := ss.toTStructure
  have cast_le : (-↑(0 : ℤ) : ℝ) = 0 := by simp
  have cast_ge : (1 - ↑(0 : ℤ) : ℝ) = 1 := by simp
  have hE_gt : s.gtProp C t E :=
    gtProp_of_lt_phiMinus_smallGap (C := C) (s := s) hE hgt
  have hE_le : s.leProp C (t + 1) E :=
    leProp_of_phiPlus_le_smallGap (C := C) (s := s) hE hle
  have hE_le' : s.leProp C (1 + t) E := by
    simpa [add_comm] using hE_le
  haveI : u.IsLE E 0 := ⟨by
    change ss.gtProp C (-↑(0 : ℤ)) E
    rw [cast_le]
    simpa [ss] using (s.phaseShift_gtProp_zero C t E).mpr hE_gt⟩
  haveI : u.IsGE E 0 := ⟨by
    change ss.leProp C (1 - ↑(0 : ℤ)) E
    rw [cast_ge]
    simpa [ss] using (s.phaseShift_leProp C t 1 E).mpr hE_le'⟩
  exact (u.mem_heart_iff E).mpr ⟨inferInstance, inferInstance⟩

variable [IsTriangulated C] in
private theorem gtProp_leProp_of_phaseShiftHeart
    (s : Slicing C) {E : C} {a u : ℝ}
    (hHeart : ((s.phaseShift C a).toTStructure).heart E)
    (hE : ¬IsZero E)
    (hu : s.phiPlus C E hE ≤ u) :
    s.gtProp C a E ∧ s.leProp C u E := by
  have hHeart' := hHeart
  rw [(s.phaseShift C a).toTStructure_heart_iff] at hHeart'
  constructor
  · exact (s.phaseShift_gtProp_zero C a E).mp hHeart'.1
  · exact leProp_of_phiPlus_le_smallGap (C := C) (s := s) hE hu

variable [IsTriangulated C] in
private theorem geProp_leProp_of_phaseShiftHeart
    (s : Slicing C) {E : C} {a l : ℝ}
    (hHeart : ((s.phaseShift C a).toTStructure).heart E)
    (hE : ¬IsZero E)
    (hl : l ≤ s.phiMinus C E hE) :
    s.geProp C l E ∧ s.leProp C (a + 1) E := by
  have hHeart' := hHeart
  rw [(s.phaseShift C a).toTStructure_heart_iff] at hHeart'
  constructor
  · exact geProp_of_phiMinus_ge_smallGap (C := C) (s := s) hE hl
  · have hle : s.leProp C (1 + a) E := by
      simpa [add_comm] using
        (s.phaseShift_leProp C a 1 E).mp hHeart'.2
    simpa [add_comm] using hle

private theorem midpoint_left_target_thin
    {ψ₁ ψ₂ ε₀ : ℝ} (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀8 : ε₀ < 1 / 8) :
    (ψ₁ + ε₀) - ((ψ₁ + ψ₂) / 2 - 1 / 2) + 2 * ε₀ < 1 := by
  linarith

private theorem midpoint_right_target_thin
    {ψ₁ ψ₂ ε₀ : ℝ} (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀8 : ε₀ < 1 / 8) :
    (((ψ₁ + ψ₂) / 2 - 1 / 2) + 1) - (ψ₂ - ε₀) + 2 * ε₀ < 1 := by
  linarith

private theorem midpoint_image_window_thin
    {ψ₁ ψ₂ ε₀ : ℝ} (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀)
    (hε₀8 : ε₀ < 1 / 8) :
    (ψ₂ + ε₀) - (ψ₁ - ε₀) + 2 * ε₀ < 1 := by
  linarith

variable [IsTriangulated C] in
private theorem mem_phaseShiftHeart_of_midpoint_left
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {ψ₁ ψ₂ ε₀ : ℝ}
    (hlo : ψ₁ - ε₀ ≤ s.phiMinus C E hE)
    (hhi : s.phiPlus C E hE ≤ ψ₁ + ε₀)
    (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀4 : ε₀ < 1 / 4) :
    (((s.phaseShift C ((ψ₁ + ψ₂) / 2 - 1 / 2)).toTStructure).heart E) := by
  refine mem_phaseShiftHeart_of_phaseBounds_smallGap (C := C) (s := s) hE ?_ ?_
  · have hmid : (ψ₁ + ψ₂) / 2 - 1 / 2 < s.phiMinus C E hE := by
      have h' : (ψ₁ + ψ₂) / 2 - 1 / 2 < ψ₁ - ε₀ := by
        linarith [hgap, hε₀4]
      exact lt_of_lt_of_le h' hlo
    exact hmid
  · have hmid : s.phiPlus C E hE ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
      have h' : ψ₁ + ε₀ ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
        linarith [hsmall, hε₀4]
      exact le_trans hhi h'
    exact hmid

variable [IsTriangulated C] in
private theorem mem_phaseShiftHeart_of_midpoint_right
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {ψ₁ ψ₂ ε₀ : ℝ}
    (hlo : ψ₂ - ε₀ ≤ s.phiMinus C E hE)
    (hhi : s.phiPlus C E hE ≤ ψ₂ + ε₀)
    (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε₀) (hε₀4 : ε₀ < 1 / 4) :
    (((s.phaseShift C ((ψ₁ + ψ₂) / 2 - 1 / 2)).toTStructure).heart E) := by
  refine mem_phaseShiftHeart_of_phaseBounds_smallGap (C := C) (s := s) hE ?_ ?_
  · have hmid : (ψ₁ + ψ₂) / 2 - 1 / 2 < s.phiMinus C E hE := by
      have h' : (ψ₁ + ψ₂) / 2 - 1 / 2 < ψ₂ - ε₀ := by
        linarith [hsmall, hε₀4]
      exact lt_of_lt_of_le h' hlo
    exact hmid
  · have hmid : s.phiPlus C E hE ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
      have h' : ψ₂ + ε₀ ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
        linarith [hgap, hε₀4]
      exact le_trans hhi h'
    exact hmid

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
    (hε₀8 : ε₀ < 1 / 8)
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
    -- Faithful Lemma 7.6 route:
    -- choose the midpoint heart A = P((a,a+1]) with a = (ψ₁ + ψ₂)/2 - 1/2,
    -- factor f in A, then compare the image in the paper's two thin target windows
    -- P((a, ψ₁ + ε₀)) and P((ψ₂ - ε₀, a + 1)).
    push_neg at hlargeGap
    by_cases hf : f = 0
    · exact hf
    · set a : ℝ := (ψ₁ + ψ₂) / 2 - 1 / 2
      have hsmallGap : ψ₁ ≤ ψ₂ + 2 * ε₀ := hlargeGap
      have hleftThin : (ψ₁ + ε₀) - a + 2 * ε₀ < 1 := by
        simpa [a] using midpoint_left_target_thin (ψ₁ := ψ₁) (ψ₂ := ψ₂) hsmallGap hε₀8
      have hrightThin : (a + 1) - (ψ₂ - ε₀) + 2 * ε₀ < 1 := by
        simpa [a] using midpoint_right_target_thin (ψ₁ := ψ₁) (ψ₂ := ψ₂) hsmallGap hε₀8
      have himageThin : (ψ₂ + ε₀) - (ψ₁ - ε₀) + 2 * ε₀ < 1 := by
        exact midpoint_image_window_thin (ψ₁ := ψ₁) (ψ₂ := ψ₂) hgap hsmallGap hε₀8
      set ss := σ.slicing.phaseShift C a
      let t := ss.toTStructure
      have hE_heart : t.heart E := by
        simpa [t, ss, a] using
          mem_phaseShiftHeart_of_midpoint_left (C := C) (s := σ.slicing) hSS₁.2.1
            hE_lo hE_hi hgap hsmallGap hε₀2
      have hF_heart : t.heart F := by
        simpa [t, ss, a] using
          mem_phaseShiftHeart_of_midpoint_right (C := C) (s := σ.slicing) hSS₂.2.1
            hF_lo hF_hi hgap hsmallGap hε₀2
      have hE_window :
          σ.slicing.gtProp C a E ∧ σ.slicing.leProp C (ψ₁ + ε₀) E := by
        exact gtProp_leProp_of_phaseShiftHeart (C := C) (s := σ.slicing)
          (a := a) hE_heart hSS₁.2.1 hE_hi
      have hF_window :
          σ.slicing.geProp C (ψ₂ - ε₀) F ∧ σ.slicing.leProp C (a + 1) F := by
        exact geProp_leProp_of_phaseShiftHeart (C := C) (s := σ.slicing)
          (a := a) hF_heart hSS₂.2.1 hF_lo
      have habE_left_src : a₁ < ψ₁ + ε₀ := by
        linarith [henv₁_lo]
      have hE_upper : σ.slicing.intervalProp C a₁ (ψ₁ + ε₀) E := by
        exact intervalProp_of_wSemistable_upper_target
          (C := C) (σ := σ) (W := W) (hW := hW) habE_left_src hab₁
          (by linarith [henv₁_hi]) hSS₁ hε₀ hε₀2 henv₁_lo (by linarith) hthin₁ hsin
      have habE_left : a < ψ₁ + ε₀ := by
        linarith
      have hE_left : σ.slicing.intervalProp C a (ψ₁ + ε₀) E := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hSS₁.2.1
          (σ.slicing.phiMinus_gt_of_gtProp C hSS₁.2.1 hE_window.1)
          (σ.slicing.phiPlus_lt_of_intervalProp C hSS₁.2.1 hE_upper)
      have henvE_left_lo : a + ε₀ ≤ ψ₁ := by
        dsimp [a]
        linarith
      have hSS₁_left :
          (σ.skewedStabilityFunction_of_near C W hW habE_left).Semistable C E ψ₁ := by
        exact semistable_of_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hab₁ habE_left hSS₁ hE_left
          hε₀ hε₀2 henv₁_lo henv₁_hi henvE_left_lo (by linarith) hthin₁ hleftThin hsin
      have habF_right_tgt : ψ₂ - ε₀ < b₂ := by
        linarith [henv₂_hi]
      have hF_lower : σ.slicing.intervalProp C (ψ₂ - ε₀) b₂ F := by
        exact intervalProp_of_wSemistable_lower_target
          (C := C) (σ := σ) (W := W) (hW := hW) hab₂ habF_right_tgt
          (by linarith [henv₂_lo]) hSS₂ hε₀ hε₀2 (by linarith) henv₂_hi hthin₂ hsin
      have habF_right : ψ₂ - ε₀ < a + 1 := by
        linarith
      have hF_right : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1) F := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hSS₂.2.1
          (σ.slicing.phiMinus_gt_of_intervalProp C hSS₂.2.1 hF_lower)
          (lt_of_le_of_lt hF_hi (by
            dsimp [a]
            linarith [hgap, hε₀2]))
      have henvF_right_hi : ψ₂ ≤ (a + 1) - ε₀ := by
        dsimp [a]
        linarith [hsmallGap]
      have hSS₂_right :
          (σ.skewedStabilityFunction_of_near C W hW habF_right).Semistable C F ψ₂ := by
        exact semistable_of_target_envelope
          (C := C) (σ := σ) (W := W) (hW := hW) hab₂ habF_right hSS₂ hF_right
          hε₀ hε₀2 henv₂_lo henv₂_hi (by linarith) henvF_right_hi hthin₂ hrightThin hsin
      letI := t.hasHeartFullSubcategory
      letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
      let EH : t.heart.FullSubcategory := ⟨E, hE_heart⟩
      let FH : t.heart.FullSubcategory := ⟨F, hF_heart⟩
      let fH : EH ⟶ FH := ObjectProperty.homMk f
      let ι := t.ιHeart (H := t.heart.FullSubcategory)
      have hι_simp : ∀ (X : t.heart.FullSubcategory), ι.obj X = X.obj := by
        intro X
        rfl
      obtain ⟨X₃, f₂, f₃, hT_hom⟩ := distinguished_cocone_triangle (ι.map fH)
      have hadm : AbelianSubcategory.admissibleMorphism
          (t.ιHeart (H := t.heart.FullSubcategory)) fH := by
        rw [TStructure.heart_admissible t]
        trivial
      obtain ⟨K, Q, α, β, γ, hT_adm⟩ := hadm f₂ f₃ hT_hom
      obtain ⟨I_H, i_I, δ_I, pH, m₃, hT_I, hT_pH, hpH⟩ :=
        Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_image_factorisation
          (ι := t.ιHeart (H := t.heart.FullSubcategory))
          (hι := TStructure.heart_hι t) (hA := TStructure.heart_admissible t)
          (X₁ := EH) (X₂ := FH) (f₁ := fH) (X₃ := X₃)
          (K := K) (Q := Q) f₂ f₃ hT_hom α β hT_adm
      let πQH : FH ⟶ Q := Triangulated.AbelianSubcategory.πQ f₂ β
      let hKerI := Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
        (TStructure.heart_hι t) i_I πQH δ_I hT_I
      haveI : Mono i_I := mono_of_isLimit_fork hKerI
      let hCoker_p :=
        Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
          (ι := t.ιHeart (H := t.heart.FullSubcategory))
          (hι := TStructure.heart_hι t)
          (Triangulated.AbelianSubcategory.ιK f₃ α) pH (-m₃) hT_pH
      haveI : Epi pH := Cofork.IsColimit.epi hCoker_p
      have hfH : fH ≠ 0 := by
        intro h
        apply hf
        simpa [fH] using congrArg (fun g => g.hom) h
      have hK_heart : t.heart K.obj := K.property
      have hQ_heart : t.heart Q.obj := Q.property
      have hI_heart : t.heart I_H.obj := I_H.property
      have hK_heart' := hK_heart
      have hQ_heart' := hQ_heart
      have hI_heart' := hI_heart
      rw [(σ.slicing.phaseShift C a).toTStructure_heart_iff] at hK_heart' hQ_heart' hI_heart'
      have hK_gt : σ.slicing.gtProp C a K.obj := by
        exact (σ.slicing.phaseShift_gtProp_zero C a K.obj).mp hK_heart'.1
      have hQ_le : σ.slicing.leProp C (a + 1) Q.obj := by
        simpa [add_comm] using
          (σ.slicing.phaseShift_leProp C a 1 Q.obj).mp hQ_heart'.2
      have hI_gt : σ.slicing.gtProp C a I_H.obj := by
        exact (σ.slicing.phaseShift_gtProp_zero C a I_H.obj).mp hI_heart'.1
      have hI_le : σ.slicing.leProp C (a + 1) I_H.obj := by
        simpa [add_comm] using
          (σ.slicing.phaseShift_leProp C a 1 I_H.obj).mp hI_heart'.2
      have hT_I' : Triangle.mk i_I.hom (f₂ ≫ β) δ_I ∈ distTriang C := by
        simpa using hT_I
      have hT_pH' :
          Triangle.mk (Triangulated.AbelianSubcategory.ιK f₃ α).hom pH.hom (-m₃) ∈
            distTriang C := by
        simpa [ι] using hT_pH
      have hIne : ¬IsZero I_H.obj := by
        intro hIZ
        have hIZH : IsZero I_H := by
          exact IsZero.of_full_of_faithful_of_isZero ι I_H (by simpa [hι_simp] using hIZ)
        have hiI_zero : i_I = 0 := zero_of_source_iso_zero _ hIZH.isoZero
        have hfH_zero : fH = 0 := by
          rw [← hpH, hiI_zero]
          simp
        exact hfH hfH_zero
      have hI_phiPlus_left : σ.slicing.phiPlus C I_H.obj hIne < ψ₁ + ε₀ := by
        exact σ.slicing.phiPlus_lt_of_triangle_with_leProp C hIne
          (fun hF' ↦ lt_of_le_of_lt hF_hi (by linarith [hgap])) hQ_le (by linarith) hT_I'
      have hI_left : σ.slicing.intervalProp C a (ψ₁ + ε₀) I_H.obj := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hIne
          (σ.slicing.phiMinus_gt_of_gtProp C hIne hI_gt)
          hI_phiPlus_left
      have hI_phiMinus_right : ψ₂ - ε₀ < σ.slicing.phiMinus C I_H.obj hIne := by
        exact σ.slicing.phiMinus_gt_of_triangle_with_gtProp C hIne
          (fun hE' ↦ lt_of_lt_of_le (by linarith [hgap]) hE_lo) hK_gt (by linarith) hT_pH'
      have hI_right : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1) I_H.obj := by
        exact σ.slicing.intervalProp_of_intrinsic_phases C hIne
          hI_phiMinus_right
          (lt_of_lt_of_le hI_phiPlus_left (by linarith [hsmallGap, hε₀2]))
      let αL : ℝ := (a + (ψ₁ + ε₀)) / 2
      let αR : ℝ := ((ψ₂ - ε₀) + (a + 1)) / 2
      have hleftThin' : (ψ₁ + ε₀) - a < 1 := by
        linarith
      have hab_left : a < ψ₁ + ε₀ := by
        linarith
      have hW_ne_left :
          ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
            a < θ → θ < ψ₁ + ε₀ → W (K₀.of C G) ≠ 0 := by
        intro G θ hG hGne _ _
        exact σ.W_ne_zero_of_seminorm_lt_one C W hW hG hGne
      have hpert_left := hperturb_of_stabSeminorm C σ W hW hleftThin' hε₀ hε₀2 hsin
      have hpert_left_lo :
          ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
            a < θ → θ < ψ₁ + ε₀ →
            a - ε₀ < wPhaseOf (W (K₀.of C G)) αL ∧
              wPhaseOf (W (K₀.of C G)) αL < a - ε₀ + 1 := by
        intro G θ hG hGne haθ hθ
        obtain ⟨hlo, hhi⟩ := hpert_left G θ hG hGne haθ hθ
        simpa [αL] using ⟨by linarith, by linarith⟩
      have hpert_left_hi :
          ∀ (G : C) (θ : ℝ), σ.slicing.P θ G → ¬IsZero G →
            a < θ → θ < ψ₁ + ε₀ →
            ψ₁ + ε₀ + ε₀ - 1 < wPhaseOf (W (K₀.of C G)) αL ∧
              wPhaseOf (W (K₀.of C G)) αL < ψ₁ + ε₀ + ε₀ := by
        intro G θ hG hGne haθ hθ
        obtain ⟨hlo, hhi⟩ := hpert_left G θ hG hGne haθ hθ
        simpa [αL] using ⟨by linarith, by linarith⟩
      have hI_phase_left_lo : a - ε₀ < wPhaseOf (W (K₀.of C I_H.obj)) αL := by
        have hαL_ge : a - ε₀ ≤ αL := by
          simp [αL]
          linarith
        exact wPhaseOf_gt_of_intervalProp C σ hIne W hαL_ge
          hI_left hW_ne_left hpert_left_lo
      have hI_phase_left_hi' : wPhaseOf (W (K₀.of C I_H.obj)) αL < ψ₁ + ε₀ + ε₀ := by
        have hαL_le : αL ≤ ψ₁ + ε₀ + ε₀ := by
          simp [αL]
          linarith
        exact wPhaseOf_lt_of_intervalProp (C := C) (σ := σ) (E := I_H.obj) hIne W
          (α := αL) (a := a) (b := ψ₁ + ε₀) (ε := ε₀) hαL_le
          hI_left hW_ne_left hpert_left_hi
      have hI_phase_left_hi : wPhaseOf (W (K₀.of C I_H.obj)) αL < ψ₁ + 2 * ε₀ := by
        linarith
      have hWneI : W (K₀.of C I_H.obj) ≠ 0 := by
        exact σ.W_ne_zero_of_intervalProp C W hleftThin'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) hab_left hε₀ hε₀2 hleftThin hsin) hIne hI_left
      have hI_phase_eq_left_right :
          wPhaseOf (W (K₀.of C I_H.obj)) αL =
            wPhaseOf (W (K₀.of C I_H.obj)) αR := by
        have hbranch :
            wPhaseOf (W (K₀.of C I_H.obj)) αL ∈ Set.Ioc (αR - 1) (αR + 1) := by
          constructor
          · simp [αL, αR] at *
            linarith
          · simp [αL, αR] at *
            linarith [hsmallGap, hε₀2]
        exact wPhaseOf_indep hWneI _ _ hbranch
      letI : Fact (a < ψ₁ + ε₀) := ⟨habE_left⟩
      letI : Fact (ψ₁ + ε₀ - a ≤ 1) := ⟨by linarith⟩
      let EL : σ.slicing.IntervalCat C a (ψ₁ + ε₀) := ⟨E, hE_left⟩
      let IL : σ.slicing.IntervalCat C a (ψ₁ + ε₀) := ⟨I_H.obj, hI_left⟩
      let pL : EL ⟶ IL := ObjectProperty.homMk pH.hom
      let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := σ.slicing) a (ψ₁ + ε₀)
        (Fact.out : ψ₁ + ε₀ - a ≤ 1)
      have hpL_epi : Epi (FL.map pL) := by
        simpa [FL, pL, EL, IL] using (inferInstance : Epi pH)
      have hpL_strict : IsStrictEpi pL := by
        letI : Epi (FL.map pL) := hpL_epi
        exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
          (C := C) (s := σ.slicing) (a := a) (b := ψ₁ + ε₀) pL
      have hW_interval_left :
          ∀ {G : C}, σ.slicing.intervalProp C a (ψ₁ + ε₀) G → ¬IsZero G →
            W (K₀.of C G) ≠ 0 := by
        intro G hG hGne
        exact σ.W_ne_zero_of_intervalProp C W hleftThin'
          (stabSeminorm_lt_cos_of_hsin_hthin
            (C := C) (σ := σ) (W := W) hab_left hε₀ hε₀2 hleftThin hsin) hGne hG
      have hI_phase_ge_left :
          ψ₁ ≤ wPhaseOf (W (K₀.of C I_H.obj)) αL := by
        let ssfL := σ.skewedStabilityFunction_of_near C W hW habE_left
        simpa [StabilityCondition.skewedStabilityFunction_of_near, EL, IL, pL] using
          (SkewedStabilityFunction.phase_le_of_strictQuotient
            (C := C) (σ := σ) (a := a) (b := ψ₁ + ε₀) (ssf := ssfL)
            (X := EL) (Y := IL) hSS₁_left hε₀ hleftThin hW_interval_left hpert_left pL
            hpL_strict hIne)
      have hK_left : σ.slicing.intervalProp C a (ψ₁ + ε₀) K.obj := by
        exact σ.slicing.first_intervalProp_of_triangle C habE_left hE_left hI_le hK_gt hT_pH'
      have hQ_phiMinus_right :
          ∀ (hQne : ¬IsZero Q.obj), ψ₂ - ε₀ < σ.slicing.phiMinus C Q.obj hQne := by
        intro hQne
        exact σ.slicing.phiMinus_gt_of_triangle_with_gtProp C hQne
          (fun hF' ↦ σ.slicing.phiMinus_gt_of_intervalProp C hF' hF_right)
          hI_gt (by
            dsimp [a]
            linarith [hε₀2]) hT_I'
      set δ := (1 - (((a + 1) - (ψ₂ - ε₀)) + 2 * ε₀)) / 2 with hδ_def
      have hδ_pos : 0 < δ := by
        have : ((a + 1) - (ψ₂ - ε₀)) + 2 * ε₀ < 1 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrightThin
        linarith
      have habF_big : ψ₂ - ε₀ < a + 1 + δ := by
        linarith
      have hthin_big : (a + 1 + δ) - (ψ₂ - ε₀) + 2 * ε₀ < 1 := by
        rw [hδ_def]
        linarith
      have hF_big : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1 + δ) F := by
        exact σ.slicing.intervalProp_mono C (show ψ₂ - ε₀ ≤ ψ₂ - ε₀ by linarith)
          (show a + 1 ≤ a + 1 + δ by linarith) hF_right
      have hSS₂_big :
          (σ.skewedStabilityFunction_of_near C W hW habF_big).Semistable C F ψ₂ := by
        exact semistable_of_upper_inclusion
          (C := C) (σ := σ) (W := W) (hW := hW)
          (hab₁ := habF_right) (hab₂ := habF_big)
          (hb := by linarith) hSS₂_right hε₀ hε₀2
          (by linarith) henvF_right_hi hthin_big hsin
      have hI_big : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1 + δ) I_H.obj := by
        exact σ.slicing.intervalProp_mono C (show ψ₂ - ε₀ ≤ ψ₂ - ε₀ by linarith)
          (show a + 1 ≤ a + 1 + δ by linarith) hI_right
      have hQ_big : σ.slicing.intervalProp C (ψ₂ - ε₀) (a + 1 + δ) Q.obj := by
        by_cases hQZ : IsZero Q.obj
        · exact Or.inl hQZ
        · exact σ.slicing.intervalProp_of_intrinsic_phases C hQZ
            (hQ_phiMinus_right hQZ)
            (lt_of_le_of_lt (σ.slicing.phiPlus_le_of_leProp C hQZ hQ_le) (by linarith))
      have hI_phase_le_big :
          wPhaseOf (W (K₀.of C I_H.obj)) ((ψ₂ - ε₀ + (a + 1 + δ)) / 2) ≤ ψ₂ := by
        simpa [StabilityCondition.skewedStabilityFunction_of_near] using
          hSS₂_big.2.2.2.2 hT_I' hI_big hQ_big hIne
      have hI_phase_eq_right_big :
          wPhaseOf (W (K₀.of C I_H.obj)) αR =
            wPhaseOf (W (K₀.of C I_H.obj)) ((ψ₂ - ε₀ + (a + 1 + δ)) / 2) := by
        simpa [αR] using
          (wPhaseOf_eq_of_intervalProp_upper_inclusion
            (C := C) (σ := σ) (W := W) (hW := hW) habF_right (by linarith)
            hI_right hIne hε₀ hε₀2 hthin_big hsin)
      have hI_phase_le_right :
          wPhaseOf (W (K₀.of C I_H.obj)) αR ≤ ψ₂ := by
        rw [hI_phase_eq_right_big]
        exact hI_phase_le_big
      rw [← hI_phase_eq_left_right] at hI_phase_le_right
      linarith

/-! ### Extension-closed subcategories Q(> t), Q(≤ t) (Node 7.8a) -/

variable [IsTriangulated C] in
/-- Auxiliary: any morphism from a `Q(ψ)`-semistable object to the `k`-th chain object of a
`Q`-HN filtration whose phases are all strictly less than `ψ` is zero. This is the direct
`deformedPred` analogue of `Slicing.chain_hom_eq_zero_of_gt`. -/
private lemma chain_hom_eq_zero_of_gt_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {A E : C} {ψ : ℝ}
    (hA : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ A)
    (F : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (hlt : ∀ i, F.φ i < ψ) :
    ∀ (k : ℕ) (hk : k < F.n + 1) (f : A ⟶ F.chain.obj ⟨k, hk⟩), f = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk f
      exact (F.base_isZero : IsZero F.chain.left).eq_of_tgt f 0
  | succ k ih =>
      intro hk f
      have hkn : k < F.n := by omega
      let T := F.triangle ⟨k, hkn⟩
      let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)
      let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)
      have hcomp : (f ≫ e₂.inv) ≫ T.mor₂ = 0 :=
        σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin
          hA (F.semistable ⟨k, hkn⟩) (hlt ⟨k, hkn⟩) _
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T
        (F.triangle_dist ⟨k, hkn⟩) (f ≫ e₂.inv) hcomp
      have hg0 : g ≫ e₁.hom = 0 := ih (by omega) (g ≫ e₁.hom)
      have hg_eq : g = 0 := by
        have : g = (g ≫ e₁.hom) ≫ e₁.inv := by
          rw [Category.assoc, e₁.hom_inv_id, Category.comp_id]
        rw [this, hg0, zero_comp]
      have hfe : f ≫ e₂.inv = 0 := by rw [hg, hg_eq, zero_comp]
      have : f = (f ≫ e₂.inv) ≫ e₂.hom := by
        rw [Category.assoc, e₂.inv_hom_id, Category.comp_id]
      rw [this, hfe, zero_comp]

variable [IsTriangulated C] in
/-- A morphism from a `Q(ψ)`-semistable object to an HN-filtered object whose phases are all
strictly less than `ψ` is zero. -/
private lemma hom_eq_zero_of_gt_phases_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {A E : C} {ψ : ℝ}
    (hA : σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin ψ A)
    (F : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (hlt : ∀ i, F.φ i < ψ) (f : A ⟶ E) : f = 0 := by
  let eE := Classical.choice F.top_iso
  have h1 : f ≫ eE.inv = 0 :=
    chain_hom_eq_zero_of_gt_deformed (C := C) (σ := σ) (W := W) (hW := hW)
      hε₀ hε₀2 hε₀8 hsin hA F hlt F.n (by omega) _
  have : f = (f ≫ eE.inv) ≫ eE.hom := by
    rw [Category.assoc, eE.inv_hom_id, Category.comp_id]
  rw [this, h1, zero_comp]

variable [IsTriangulated C] in
/-- Auxiliary: any morphism from the `k`-th chain object of a `Q`-HN filtration (with all
phases strictly greater than those of a second `Q`-HN filtration) to the target of the second
filtration is zero. This is the `deformedPred` analogue of
`Slicing.chain_hom_eq_zero_gap`. -/
private lemma chain_hom_eq_zero_gap_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {X Y : C}
    (Fx : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X)
    (Fy : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) Y)
    (hgap : ∀ i j, Fy.φ j < Fx.φ i) :
    ∀ (k : ℕ) (hk : k < Fx.n + 1) (f : Fx.chain.obj ⟨k, hk⟩ ⟶ Y), f = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk f
      exact (Fx.base_isZero : IsZero Fx.chain.left).eq_of_src f 0
  | succ k ih =>
      intro hk f
      have hkn : k < Fx.n := by omega
      let T := Fx.triangle ⟨k, hkn⟩
      let e₁ := Classical.choice (Fx.triangle_obj₁ ⟨k, hkn⟩)
      let e₂ := Classical.choice (Fx.triangle_obj₂ ⟨k, hkn⟩)
      have hmor1 : T.mor₁ ≫ (e₂.hom ≫ f) = 0 := by
        have h1 : e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f)) = 0 := by
          simp only [← Category.assoc]
          exact ih (by omega) _
        have h2 :
            e₁.hom ≫ (e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f))) =
              T.mor₁ ≫ (e₂.hom ≫ f) := by
          rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
        rw [← h2, h1, comp_zero]
      obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T
        (Fx.triangle_dist ⟨k, hkn⟩) (e₂.hom ≫ f) hmor1
      have hg_eq : g = 0 :=
        hom_eq_zero_of_gt_phases_deformed (C := C) (σ := σ) (W := W) (hW := hW)
          hε₀ hε₀2 hε₀8 hsin (Fx.semistable ⟨k, hkn⟩) Fy
          (fun j ↦ hgap ⟨k, hkn⟩ j) g
      have hef : e₂.hom ≫ f = 0 := by rw [hg, hg_eq, comp_zero]
      have : f = e₂.inv ≫ (e₂.hom ≫ f) := by
        rw [← Category.assoc, e₂.inv_hom_id, Category.id_comp]
      rw [this, hef, comp_zero]

variable [IsTriangulated C] in
/-- Morphisms between `Q`-HN filtered objects with a phase gap are zero. -/
private lemma hom_eq_zero_of_phase_gap_deformed
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {X Y : C}
    (Fx : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X)
    (Fy : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) Y)
    (hgap : ∀ i j, Fy.φ j < Fx.φ i) (f : X ⟶ Y) : f = 0 := by
  let eX := Classical.choice Fx.top_iso
  have h1 : eX.hom ≫ f = 0 :=
    chain_hom_eq_zero_gap_deformed (C := C) (σ := σ) (W := W) (hW := hW)
      hε₀ hε₀2 hε₀8 hsin Fx Fy hgap Fx.n (by omega) _
  have : f = eX.inv ≫ (eX.hom ≫ f) := by
    rw [← Category.assoc, eX.inv_hom_id, Category.id_comp]
  rw [this, h1, comp_zero]

variable [IsTriangulated C] in
/-- Inside a thin interval whose `W`-phase window already sits `ε₀` away from the
boundaries, the Lemma 7.6 hom-vanishing theorem applies directly to the interval-semistable
objects, because they are `deformedPred` objects witnessed by that same interval. -/
private theorem hom_eq_zero_of_enveloped_interval_semistable
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      a + ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b - ε₀)
    {E F : σ.slicing.IntervalCat C a b}
    (hE : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C E.obj
      (wPhaseOf (W (K₀.of C E.obj)) ((a + b) / 2)))
    (hF : (σ.skewedStabilityFunction_of_near C W hW hab).Semistable C F.obj
      (wPhaseOf (W (K₀.of C F.obj)) ((a + b) / 2)))
    (hlt :
      wPhaseOf (W (K₀.of C F.obj)) ((a + b) / 2) <
        wPhaseOf (W (K₀.of C E.obj)) ((a + b) / 2))
    (f : E ⟶ F) :
    f = 0 := by
  have hEQ :
      σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin
        (wPhaseOf (W (K₀.of C E.obj)) ((a + b) / 2)) E.obj := by
    refine Or.inr ⟨a, b, hab, hthin, ?_, ?_, ?_⟩
    · exact le_of_lt (hWindow E.property hE.2.1).1
    · exact le_of_lt (hWindow E.property hE.2.1).2
    · simpa using hE
  have hFQ :
      σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin
        (wPhaseOf (W (K₀.of C F.obj)) ((a + b) / 2)) F.obj := by
    refine Or.inr ⟨a, b, hab, hthin, ?_, ?_, ?_⟩
    · exact le_of_lt (hWindow F.property hF.2.1).1
    · exact le_of_lt (hWindow F.property hF.2.1).2
    · simpa using hF
  have h0 : f.hom = 0 :=
    σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin hEQ hFQ hlt f.hom
  ext
  exact h0

variable [IsTriangulated C] in
/-- Lemma 7.7 packaged directly for the deformed slicing: if a thin interval carries the
strict finite-length input and every nonzero object has `W`-phase at least `ε₀` away from
the interval boundaries, then the thin-interval HN factors are already `Q`-factors, using
the same interval as the witness in `deformedPred`. -/
private theorem exists_deformedHN_of_enveloped_interval
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      W (K₀.of C F) ≠ 0)
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      a + ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b - ε₀)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X.obj,
      ∀ j, a + ε₀ < G.φ j ∧ G.φ j < b - ε₀ := by
  let ssf : SkewedStabilityFunction C σ.slicing a b :=
    σ.skewedStabilityFunction_of_near C W hW hab
  obtain ⟨G, hGφ⟩ :=
    SkewedStabilityFunction.hn_exists_in_thin_interval
      (C := C) (σ := σ) (a := a) (b := b) (ssf := ssf) hFiniteLength
      (fun {F} hF hFne ↦ hW_interval hF hFne)
      (L := a + ε₀) (U := b - ε₀)
      (fun {F} hF hFne ↦ hWindow hF hFne)
      (by linarith [hthin])
      (fun {E F} hE hF hlt f ↦
        hom_eq_zero_of_enveloped_interval_semistable
          (C := C) (σ := σ) (W := W) (hW := hW) hab
          hε₀ hε₀2 hε₀8 hthin hsin hWindow hE hF hlt f) X hX
  let GQ : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X.obj :=
    { n := G.n
      chain := G.chain
      triangle := G.triangle
      triangle_dist := G.triangle_dist
      triangle_obj₁ := G.triangle_obj₁
      triangle_obj₂ := G.triangle_obj₂
      base_isZero := G.base_isZero
      top_iso := G.top_iso
      zero_isZero := G.zero_isZero
      φ := G.φ
      hφ := G.hφ
      semistable := fun j ↦ by
        change IsZero (G.factor j) ∨
          ∃ (a' b' : ℝ) (hab' : a' < b') (_ : b' - a' + 2 * ε₀ < 1)
            (_ : a' + ε₀ ≤ G.φ j) (_ : G.φ j ≤ b' - ε₀),
            (σ.skewedStabilityFunction_of_near C W hW hab').Semistable C (G.factor j) (G.φ j)
        refine Or.inr ⟨a, b, hab, hthin, le_of_lt (hGφ j).1, le_of_lt (hGφ j).2, ?_⟩
        simpa [ssf] using G.semistable j }
  refine ⟨GQ, hGφ⟩

/-- **Q(> t)**: the extension-closed subcategory generated by the `Q(ψ)` with `ψ > t`,
encoded concretely as existence of a `Q`-HN filtration whose phases all lie strictly above
`t`. This is the paper's Node 7.8a predicate, not just the semistable one-factor case. -/
def StabilityCondition.deformedGtPred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E,
      ∀ j : Fin G.n, t < G.φ j

/-- **Q(≤ t)**: the dual extension-closed subcategory generated by the `Q(ψ)` with `ψ ≤ t`,
again encoded by existence of a `Q`-HN filtration with all phases on the specified side. -/
def StabilityCondition.deformedLePred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E,
      ∀ j : Fin G.n, G.φ j ≤ t

/-- **Q(< t)**: the extension-closed subcategory generated by the `Q(ψ)` with `ψ < t`,
encoded as existence of a `Q`-HN filtration whose phases all lie strictly below `t`. This
is the paper's Node 7.8a / 7.9 notation needed to talk about `Q((t, t + δ))`. -/
def StabilityCondition.deformedLtPred (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (t : ℝ) : ObjectProperty C :=
  fun E ↦ IsZero E ∨
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E,
      ∀ j : Fin G.n, G.φ j < t

variable [IsTriangulated C] in
/-- Monotonicity of the provisional `Q(≤ t)` predicate. -/
private theorem StabilityCondition.deformedLePred_mono
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t₁ ≤
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t₂ := by
  intro E hE
  rcases hE with hZ | ⟨G, hG⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨G, fun j ↦ le_trans (hG j) ht⟩

variable [IsTriangulated C] in
/-- Monotonicity of the provisional `Q(< t)` predicate. -/
private theorem StabilityCondition.deformedLtPred_mono
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t₁ ≤
      σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t₂ := by
  intro E hE
  rcases hE with hZ | ⟨G, hG⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨G, fun j ↦ lt_of_lt_of_le (hG j) ht⟩

variable [IsTriangulated C] in
/-- Any `Q(< t)`-object is in `Q(≤ t)`. -/
private theorem StabilityCondition.deformedLePred_of_deformedLtPred
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t : ℝ} :
    σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t ≤
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t := by
  intro E hE
  rcases hE with hZ | ⟨G, hG⟩
  · exact Or.inl hZ
  · exact Or.inr ⟨G, fun j ↦ le_of_lt (hG j)⟩

variable [IsTriangulated C] in
/-- A length-one HN filtration presents the ambient object as isomorphic to its unique factor.
Hence, if the phase predicate is closed under isomorphisms, the ambient object is semistable
of that same phase. -/
private theorem semistable_of_hn_length_one
    {P : ℝ → ObjectProperty C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    {Y : C} (GY : HNFiltration C P Y) (h1 : GY.n = 1) :
    P (GY.φ ⟨0, by omega⟩) Y := by
  let j0 : Fin GY.n := ⟨0, by omega⟩
  let T := GY.triangle j0
  have hZ1 : IsZero T.obj₁ :=
    IsZero.of_iso GY.base_isZero (Classical.choice (GY.triangle_obj₁ j0))
  have hIso₂ : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (GY.triangle_dist j0)).mp hZ1
  have hobj₂_eq : GY.chain.obj' (0 + 1) (by omega) = GY.chain.obj (Fin.last GY.n) :=
    congrArg GY.chain.obj (Fin.ext (by simp [Fin.last, h1]))
  let e₂Y : T.obj₂ ≅ Y :=
    (Classical.choice (GY.triangle_obj₂ j0)).trans
      ((eqToIso hobj₂_eq).trans (Classical.choice GY.top_iso))
  letI : (P (GY.φ j0)).IsClosedUnderIsomorphisms := hPiso (GY.φ j0)
  exact (P (GY.φ j0)).prop_of_iso ((e₂Y.symm.trans (asIso T.mor₂)).symm) (GY.semistable j0)

variable [IsTriangulated C] in
/-- Concatenate HN filtrations across a distinguished triangle `X → E → Y → X[1]`,
provided every phase in the filtration on `Y` is strictly smaller than every phase in the
filtration on `X`. This is the generic Postnikov-splicing step needed to assemble the
faithful Section 7 HN filtration from filtrations on successive σ-semistable factors. -/
private theorem append_hn_filtration_of_triangle
    {P : ℝ → ObjectProperty C} {X E Y : C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    (GX : HNFiltration C P X)
    (GY : HNFiltration C P Y)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (t : ℝ)
    (hX_gt : ∀ j : Fin GX.n, t < GX.φ j)
    (hY_gt : ∀ i : Fin GY.n, t < GY.φ i)
    (hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) :
    ∃ G : HNFiltration C P E, ∀ j : Fin G.n, t < G.φ j := by
  suffices hmain :
      ∀ (m : ℕ) {Y : C} (GY : HNFiltration C P Y), GY.n ≤ m →
        ∀ {E : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C →
          ∀ (t : ℝ),
          (∀ j : Fin GX.n, t < GX.φ j) →
          (∀ i : Fin GY.n, t < GY.φ i) →
          (∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) →
          ∃ G : HNFiltration C P E, ∀ j : Fin G.n, t < G.φ j by
    exact hmain GY.n GY le_rfl f g h hT t hX_gt hY_gt hsep
  intro m
  induction m with
  | zero =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep
      have hYn : GY.n = 0 := by omega
      have hYz : IsZero Y := GY.zero_isZero hYn
      haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
      refine ⟨GX.ofIso C (asIso f), ?_⟩
      intro j
      simpa using hX_gt j
  | succ m ih =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep
      by_cases hYn : GY.n = 0
      · have hYz : IsZero Y := GY.zero_isZero hYn
        haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
        refine ⟨GX.ofIso C (asIso f), ?_⟩
        intro j
        simpa using hX_gt j
      · have hYpos : 0 < GY.n := Nat.pos_of_ne_zero hYn
        by_cases hYone : GY.n = 1
        · let j0 : Fin GY.n := ⟨0, by omega⟩
          have hsep0 : ∀ j : Fin GX.n, GY.φ j0 < GX.φ j := by
            intro j
            exact hsep j0 j
          have hYss : P (GY.φ j0) Y :=
            semistable_of_hn_length_one (C := C) hPiso GY hYone
          refine ⟨GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
            (GY.φ j0) hYss hsep0, ?_⟩
          intro j
          by_cases hj : j.val < GX.n
          · have hsmall :
                GY.φ j0 <
                  (GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
                    (GY.φ j0) hYss hsep0).φ j := by
              simpa [HNFiltration.appendFactor, hj] using hsep0 ⟨j.val, hj⟩
            exact lt_trans (hY_gt j0) hsmall
          · have hjLast :
                (GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
                  (GY.φ j0) hYss hsep0).φ j = GY.φ j0 := by
              simp [HNFiltration.appendFactor, hj]
            exact hjLast.symm ▸ hY_gt j0
        · have hYtwo : 2 ≤ GY.n := by omega
          let jLast : Fin GY.n := ⟨GY.n - 1, by omega⟩
          let GY' := GY.prefix C (GY.n - 1) (by omega) (by omega)
          let Tlast := GY.triangle jLast
          let e₁ := Classical.choice (GY.triangle_obj₁ jLast)
          let e₂ := Classical.choice (GY.triangle_obj₂ jLast)
          let eY := by
            have hchainN : GY.chain.obj' (GY.n - 1 + 1) (by omega) =
                GY.chain.obj (Fin.last GY.n) :=
              congrArg GY.chain.obj (Fin.ext (by simp [Fin.last]; omega))
            exact e₂.trans ((eqToIso hchainN).trans (Classical.choice GY.top_iso))
          let f23 : GY.chain.obj ⟨GY.n - 1, by omega⟩ ⟶ Y :=
            e₁.inv ≫ Tlast.mor₁ ≫ eY.hom
          let g23 : Y ⟶ Tlast.obj₃ :=
            eY.inv ≫ Tlast.mor₂
          let h23 : Tlast.obj₃ ⟶ GY.chain.obj ⟨GY.n - 1, by omega⟩⟦(1 : ℤ)⟧ :=
            Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hT23 : Triangle.mk f23 g23 h23 ∈ distTriang C := by
            refine isomorphic_distinguished _ (GY.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm eY.symm (Iso.refl _)
              (by simp [Tlast, f23, eY])
              (by simp [Tlast, g23, eY])
              (by simp [Tlast, h23])
          obtain ⟨Z, f13, h13, hT13⟩ := distinguished_cocone_triangle₁ (g ≫ g23)
          let oct := Triangulated.someOctahedron'
            (show g ≫ g23 = g ≫ g23 by rfl) hT hT23 hT13
          have hsep' :
              ∀ i : Fin GY'.n, ∀ j : Fin GX.n, GY'.φ i < GX.φ j := by
            intro i j
            have hEqn : GY'.n = GY.n - 1 := rfl
            have hi : i.val < GY.n - 1 := by
              simpa [hEqn] using i.is_lt
            exact hsep ⟨i.val, by omega⟩ j
          have hX_gt_last : ∀ j : Fin GX.n, GY.φ jLast < GX.φ j := by
            intro j
            exact hsep jLast j
          have hY'_gt_last : ∀ i : Fin GY'.n, GY.φ jLast < GY'.φ i := by
            intro i
            have hEqn : GY'.n = GY.n - 1 := rfl
            have hi : i.val < GY.n - 1 := by
              simpa [hEqn] using i.is_lt
            change GY.φ jLast < GY.φ ⟨i.val, by omega⟩
            exact GY.hφ (show (⟨i.val, by omega⟩ : Fin GY.n) < jLast by
              exact Fin.mk_lt_mk.mpr (by omega))
          obtain ⟨GZ, hGZ⟩ := ih GY' (by
            change GY.n - 1 ≤ m
            omega) oct.triangle.mor₁ oct.triangle.mor₂ oct.triangle.mor₃ oct.mem
            (GY.φ jLast) hX_gt_last hY'_gt_last hsep'
          have hlast_gt_t : t < GY.φ jLast := hY_gt jLast
          refine ⟨GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
            (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast) hGZ, ?_⟩
          intro j
          by_cases hj : j.val < GZ.n
          · have hsmall :
                GY.φ jLast <
                  (GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
                    (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast)
                    hGZ).φ j := by
              simpa [HNFiltration.appendFactor, hj] using hGZ ⟨j.val, hj⟩
            exact lt_trans hlast_gt_t hsmall
          · have hjLast :
                (GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
                  (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast) hGZ).φ j =
                    GY.φ jLast := by
              simp [HNFiltration.appendFactor, hj]
            exact hjLast.symm ▸ hlast_gt_t

variable [IsTriangulated C] in
/-- Split an HN filtration at an arbitrary cutoff `t`. The `X`-part carries a filtration whose
phases are all `> t`, and the `Y`-part carries a filtration whose phases are all `≤ t`.

The strengthened conclusion tracks that every phase of the `Y`-part is bounded below by the
last phase of the original filtration. This is the generic cutoff invariant needed to append the
last factor in the mixed case, exactly as in Bridgeland's p.24 argument. -/
private theorem split_hn_filtration_at_cutoff
    {P : ℝ → ObjectProperty C} {A : C}
    (F : HNFiltration C P A) (t : ℝ) :
    ∃ (X Y : C) (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      (∀ j : Fin GX.n, t < GX.φ j) ∧
      (∀ j : Fin GY.n, GY.φ j ≤ t) ∧
      (∀ (_ : 0 < F.n) (j : Fin GY.n),
        F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j) := by
  suffices hmain :
      ∀ (m : ℕ) (A : C) (F : HNFiltration C P A), F.n ≤ m →
        ∃ (X Y : C) (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
          (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C ∧
          (∀ j : Fin GX.n, t < GX.φ j) ∧
          (∀ j : Fin GY.n, GY.φ j ≤ t) ∧
          (∀ (_ : 0 < F.n) (j : Fin GY.n),
            F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j) by
    exact hmain F.n A F le_rfl
  intro m
  induction m with
  | zero =>
      intro A F hFn
      have hn : F.n = 0 := by omega
      refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
        𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_⟩
      · intro j
        exact False.elim (by simpa [hn] using j.is_lt)
      · intro j
        exact Fin.elim0 j
      · intro hn0 j
        exact False.elim (by omega)
  | succ m ih =>
      intro A F hFn
      by_cases hn : F.n = 0
      · refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
          𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_⟩
        · intro j
          exact False.elim (by simpa [hn] using j.is_lt)
        · intro j
          exact Fin.elim0 j
        · intro hn0 j
          exact False.elim (by omega)
      · have hn0 : 0 < F.n := Nat.pos_of_ne_zero hn
        by_cases hlast_gt : t < F.φ ⟨F.n - 1, by omega⟩
        · refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
            𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_⟩
          · intro j
            exact lt_of_lt_of_le hlast_gt
              (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
          · intro j
            exact Fin.elim0 j
          · intro _ j
            exact Fin.elim0 j
        · have hlast_le : F.φ ⟨F.n - 1, by omega⟩ ≤ t := by
            linarith
          by_cases hFone : F.n = 1
          · refine ⟨0, A, HNFiltration.zero C (P := P) 0 (isZero_zero C), F,
              0, 𝟙 A, 0, contractible_distinguished₁ A, ?_, ?_, ?_⟩
            · intro j
              exact Fin.elim0 j
            · intro j
              have hj : j = ⟨0, by omega⟩ := by
                apply Fin.ext
                omega
              subst j
              simpa [HNFiltration.phiPlus, hFone] using hlast_le
            · intro _ j
              have hj : j = ⟨0, by omega⟩ := by
                apply Fin.ext
                omega
              subst j
              simpa [hFone]
          · have hn2 : 2 ≤ F.n := by omega
            let G := F.prefix C (F.n - 1) (by omega) (by omega)
            obtain ⟨X, Y', GX, GY', f', g', h', hT', hGX_gt, hGY'_le, hGY'_bound⟩ :=
              ih (F.chain.obj' (F.n - 1) (by omega)) G
                (by
                  change F.n - 1 ≤ m
                  omega)
            let T := F.triangle ⟨F.n - 1, by omega⟩
            let e₁ := Classical.choice (F.triangle_obj₁ ⟨F.n - 1, by omega⟩)
            let e₂ := Classical.choice (F.triangle_obj₂ ⟨F.n - 1, by omega⟩)
            let eA := Classical.choice F.top_iso
            have hchainN : F.chain.obj' (F.n - 1 + 1) (by omega) =
                F.chain.obj (Fin.last F.n) :=
              congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; omega))
            let e₂A : T.obj₂ ≅ A :=
              e₂.trans ((eqToIso hchainN).trans eA)
            let u₂₃ : F.chain.obj' (F.n - 1) (by omega) ⟶ A :=
              e₁.inv ≫ T.mor₁ ≫ e₂A.hom
            let Tisoₘ := Triangle.isoMk
              (Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂) (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')) T
              e₁.symm e₂A.symm (Iso.refl _)
              (by simp [u₂₃, e₂A])
              (by simp [e₂A])
              (by simp)
            have hTu₂₃ :
                Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂) (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ∈
                  distTriang C :=
              isomorphic_distinguished _ (F.triangle_dist ⟨F.n - 1, by omega⟩) _ Tisoₘ
            have hGn : 0 < G.n := by
              change 0 < F.n - 1
              omega
            have hφlast_lt : ∀ j : Fin GY'.n, F.φ ⟨F.n - 1, by omega⟩ < GY'.φ j := by
              intro j
              calc
                F.φ ⟨F.n - 1, by omega⟩
                    < F.φ ⟨F.n - 2, by omega⟩ :=
                  F.hφ (show (⟨F.n - 2, by omega⟩ : Fin F.n) <
                    ⟨F.n - 1, by omega⟩ from
                      Fin.mk_lt_mk.mpr (by omega))
                _ = G.φ ⟨G.n - 1, by omega⟩ := by
                    change F.φ ⟨F.n - 2, _⟩ = F.φ ⟨(F.n - 1) - 1, _⟩
                    congr 1
                _ ≤ GY'.φ j := hGY'_bound hGn j
            obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f' ≫ u₂₃)
            let oct := Triangulated.someOctahedron rfl hT' hTu₂₃ h₁₃
            let GZ := GY'.appendFactor C oct.triangle oct.mem (Iso.refl _)
              (Iso.refl _) (F.φ ⟨F.n - 1, by omega⟩)
              (F.semistable ⟨F.n - 1, by omega⟩) hφlast_lt
            refine ⟨X, Z, GX, GZ, f' ≫ u₂₃, v₁₃, w₁₃, h₁₃, hGX_gt, ?_, ?_⟩
            · intro j
              change GZ.φ j ≤ t
              simp only [GZ, HNFiltration.appendFactor]
              split_ifs with hj
              · exact hGY'_le ⟨j.val, hj⟩
              · exact hlast_le
            · intro _ j
              change F.φ ⟨F.n - 1, by omega⟩ ≤ GZ.φ j
              simp only [GZ, HNFiltration.appendFactor]
              split_ifs with hj
              · exact le_of_lt (hφlast_lt ⟨j.val, hj⟩)
              · exact le_rfl


variable [IsTriangulated C] in
/-- Once a distinguished triangle is split at cutoff `t` into an object of `Q(> t)` and an
object of `Q(≤ t)`, the middle term automatically has a full `Q`-HN filtration. This is the
last generic step needed after constructing Bridgeland's p.24 truncation triangles. -/
private theorem exists_hn_of_deformedGt_deformedLe_triangle
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {t : ℝ} {X E Y : C} {f : X ⟶ E} {g : E ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hX : σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t X)
    (hY : σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t Y) :
    Nonempty (HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E) := by
  rcases hX with hXZ | ⟨GX, hGX⟩
  · haveI : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hT).mp hXZ
    rcases hY with hYZ | ⟨GY, _⟩
    · -- X zero ⟹ g iso; Y zero ⟹ E ≅ Y zero
      exact ⟨HNFiltration.zero C (P := σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin)
        E (IsZero.of_iso hYZ (asIso g))⟩
    · exact ⟨GY.ofIso C (asIso g).symm⟩
  · rcases hY with hYZ | ⟨GY, hGY⟩
    · haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYZ
      exact ⟨GX.ofIso C (asIso f)⟩
    · have hPiso :
          ∀ φ : ℝ,
            (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin φ).IsClosedUnderIsomorphisms :=
        σ.deformedPred_closedUnderIso C W hW ε₀ hε₀ hε₀2 hsin
      rcases Nat.eq_zero_or_pos GY.n with hGYn0 | hGYn
      · -- GY.n = 0: Y is zero, so f is iso and E ≅ X has HN via GX
        haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp (GY.zero_isZero hGYn0)
        exact ⟨GX.ofIso C (asIso f)⟩
      · -- GY.n > 0: concatenate GX and GY HN filtrations across the triangle
        let jLast : Fin GY.n := ⟨GY.n - 1, by omega⟩
        let t0 : ℝ := GY.φ jLast - 1
        have hGX_gt : ∀ j : Fin GX.n, t0 < GX.φ j := by
          intro j; dsimp [t0]; linarith [hGY jLast, hGX j]
        have hGY_gt : ∀ i : Fin GY.n, t0 < GY.φ i := by
          intro i; dsimp [t0]
          calc GY.φ jLast - 1 < GY.φ jLast := by linarith
            _ ≤ GY.φ i := GY.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        have hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j := by
          intro i j; exact lt_of_le_of_lt (hGY i) (hGX j)
        obtain ⟨G, _⟩ :=
          append_hn_filtration_of_triangle (C := C) hPiso GX GY f g h hT t0
            hGX_gt hGY_gt hsep
        exact ⟨G⟩

variable [IsTriangulated C] in
/-- **Orthogonality of Q(> t) and Q(≤ t)** (**Node 7.8b**). Every morphism from a
`Q(> t)`-object to a `Q(≤ t)`-object is zero, by the sharp hom-vanishing (Node 7.6). -/
theorem StabilityCondition.hom_eq_zero_of_deformedGt_deformedLe
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E F : C} {t : ℝ}
    (hE : σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t E)
    (hF : σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t F)
    (f : E ⟶ F) : f = 0 := by
  rcases hE with hEZ | ⟨GE, hGE⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨GF, hGF⟩
  · exact hFZ.eq_of_tgt f 0
  exact hom_eq_zero_of_phase_gap_deformed (C := C) (σ := σ) (W := W) (hW := hW)
    hε₀ hε₀2 hε₀8 hsin GE GF
    (fun i j ↦ lt_of_le_of_lt (hGF j) (hGE i)) f

variable [IsTriangulated C] in
/-- Orthogonality of `Q(> t)` and `Q(< t)`. This is the strict version of Node 7.8b used
later for the strip categories `Q((t, t + δ))`. -/
theorem StabilityCondition.hom_eq_zero_of_deformedGt_deformedLt
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E F : C} {t : ℝ}
    (hE : σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t E)
    (hF : σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin t F)
    (f : E ⟶ F) : f = 0 := by
  rcases hE with hEZ | ⟨GE, hGE⟩
  · exact hEZ.eq_of_src f 0
  rcases hF with hFZ | ⟨GF, hGF⟩
  · exact hFZ.eq_of_tgt f 0
  exact hom_eq_zero_of_phase_gap_deformed (C := C) (σ := σ) (W := W) (hW := hW)
    hε₀ hε₀2 hε₀8 hsin GE GF
    (fun i j ↦ lt_trans (hGF j) (hGE i)) f
variable [IsTriangulated C] in
/-- A `Q`-HN filtration split at cutoff `t` gives the paper's truncation triangle whose two
pieces lie in `Q(> t)` and `Q(≤ t)`. -/
private theorem exists_deformedGt_deformedLe_triangle_of_hn
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C}
    (G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t X ∧
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t Y := by
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, _⟩ :=
    split_hn_filtration_at_cutoff (C := C) G t
  exact ⟨X, Y, f, g, h, hT, Or.inr ⟨GX, hGX⟩, Or.inr ⟨GY, hGY⟩⟩

variable [IsTriangulated C] in
/-- A `Q`-HN filtration split at cutoff `t` also gives the strip-style truncation triangle
used in Node 7.9, with the right-hand term in `Q(< t + δ)` for any `δ > 0`. -/
private theorem exists_deformedGt_deformedLt_triangle_of_hn
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C}
    (G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E)
    (t δ : ℝ) (hδ : 0 < δ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t X ∧
      σ.deformedLtPred C W hW ε₀ hε₀ hε₀2 hsin (t + δ) Y := by
  obtain ⟨X, Y, f, g, h, hT, hX, hY⟩ :=
    exists_deformedGt_deformedLe_triangle_of_hn
      (C := C) (σ := σ) (W := W) (hW := hW) hε₀ hε₀2 hsin G t
  refine ⟨X, Y, f, g, h, hT, hX, ?_⟩
  rcases hY with hYZ | ⟨GY, hGY⟩
  · exact Or.inl hYZ
  · exact Or.inr ⟨GY, fun j ↦ lt_of_le_of_lt (hGY j) (by linarith)⟩

variable [IsTriangulated C] in
/-- Faithful Node 7.8c wrapper: once an object in a thin interval admits a `Q`-HN filtration
whose factors stay inside the same enveloping window, splitting that HN filtration at a cutoff
`t` gives the paper's `Q(> t) / Q(≤ t)` truncation triangle. -/
private theorem exists_deformedGt_deformedLe_triangle_of_enveloped_interval
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hW_interval : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      W (K₀.of C F) ≠ 0)
    (hWindow : ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
      a + ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
        wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b - ε₀)
    {E : C} (hE : σ.slicing.intervalProp C a b E) (hEne : ¬IsZero E)
    (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      σ.deformedGtPred C W hW ε₀ hε₀ hε₀2 hsin t X ∧
      σ.deformedLePred C W hW ε₀ hε₀ hε₀2 hsin t Y := by
  let EI : σ.slicing.IntervalCat C a b := ⟨E, hE⟩
  have hEIne : ¬IsZero EI := by
    intro hZ
    exact hEne (((σ.slicing.intervalProp C a b).ι).map_isZero hZ)
  obtain ⟨G, _hGφ⟩ :=
    exists_deformedHN_of_enveloped_interval
      (C := C) (σ := σ) (W := W) (hW := hW) hab
      hFiniteLength hε₀ hε₀2 hε₀8 hthin hsin hW_interval hWindow
      (X := EI) hEIne
  exact exists_deformedGt_deformedLe_triangle_of_hn
    (C := C) (σ := σ) (W := W) (hW := hW) hε₀ hε₀2 hsin G t

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
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
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
    σ.hom_eq_zero_of_deformedPred C W hW hε₀ hε₀2 hε₀8 hsin hA hB hlt f
  hn_exists := by
    -- Faithful p.24 route:
    -- 1. use the exact strip-local Lemma 7.7 wrappers, not the old `P(φ)` detour;
    -- 2. build the paper's `Q(> t) / Q(≤ t)` and `Q(> t) / Q(< t + δ)` triangles
    --    from those strip windows;
    -- 3. assemble the global `Q`-HN filtration through
    --    `exists_hn_of_deformedGt_deformedLe_triangle`.
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
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (ψ : ℝ) (E : C)
    (hQ : (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).P ψ E)
    (hE : ¬IsZero E) :
    ∃ (m : ℝ), 0 < m ∧
      W (K₀.of C E) = ↑m * Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  -- hQ : deformedPred, so either IsZero or ∃ a b hab hthin, Semistable
  rcases hQ with hEZ | ⟨a, b, hab, _, _, _, hSS⟩
  · exact absurd hEZ hE
  · exact ⟨‖W (K₀.of C E)‖, norm_pos_iff.mpr hSS.2.2.1, hSS.polar⟩



variable [IsTriangulated C] in
/-- **σ-semistable objects have Q-HN filtrations** (Bridgeland p.24).
For E ∈ P(φ), embed E in the wide interval P((φ-3ε₀, φ+5ε₀)) and apply Lemma 7.7
(`exists_deformedHN_of_enveloped_interval`). The enveloping condition is automatic
since phase confinement (Lemma 7.3) gives W-phases in (φ-ε₀, φ+ε₀) ⊂ (a+ε₀, b-ε₀). -/
private theorem sigmaSemistable_hasDeformedHN
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4)
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    Nonempty (HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) E) := by
  -- Bridgeland p.24: embed E in P((φ-3ε₀, φ+5ε₀)), apply Lemma 7.7.
  sorry

/-! #### Step A4: Main theorem -/

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
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (_hE : ¬IsZero E)
    {δ : ℝ} (hδ : 0 < δ) :
    (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).intervalProp C
      (φ - ε₀ - δ) (φ + ε₀ + δ) E := by
  -- Bridgeland p.24: embed E ∈ P(φ) in wide interval P((φ-3ε₀, φ+5ε₀)),
  -- apply Lemma 7.7 (exists_deformedHN_of_enveloped_interval), then read off
  -- the Q-interval bounds from the HN factor phases.
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
    (hε₀8 : ε₀ < 1 / 8)
    (hWide : WideSectorFiniteLength (C := C) σ ε₀ hε₀ hε₀8)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    (hε₀_lf : ∃ δ : ℝ, 0 < δ ∧ ε₀ + δ < 1 / 2 ∧ ∀ t : ℝ,
      ∀ (E :
        (σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ))).FullSubcategory),
        IsArtinianObject E ∧ IsNoetherianObject E) :
    ∃ (τ : StabilityCondition C), τ.Z = W ∧
      slicingDist C σ.slicing τ.slicing ≤ ENNReal.ofReal ε₀ := by
  let hSector : SectorFiniteLength (C := C) σ ε₀ hε₀ hε₀2 :=
    SectorFiniteLength.of_wide (C := C) σ hε₀ hε₀2 hε₀8 hWide
  refine ⟨⟨σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin, W,
    σ.deformedSlicing_compat C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin, ?_⟩, rfl, ?_⟩
  · -- Local finiteness: inherited from σ via phase confinement
    obtain ⟨δ, hδ, hδ_half, hlf_σ⟩ := hε₀_lf
    let δ' : ℝ := min (δ / 2) (1 / 4)
    constructor
    refine ⟨δ', by
      dsimp [δ']
      positivity, by
      dsimp [δ']
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun t E ↦ ?_⟩
    letI : Fact (t - δ' < t + δ') := ⟨by
      dsimp [δ']
      have : 0 < δ' := by
        dsimp [δ']
        positivity
      linarith⟩
    letI : Fact ((t + δ') - (t - δ') ≤ 1) := ⟨by
      dsimp [δ']
      have hδ' : δ' ≤ 1 / 4 := by
        dsimp [δ']
        exact min_le_right _ _
      linarith⟩
    have hIncl :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).intervalProp C
            (t - δ') (t + δ') ≤
          σ.slicing.intervalProp C (t - (ε₀ + δ)) (t + (ε₀ + δ)) := by
      intro X hX
      rcases hX with hZ | ⟨F, hF⟩
      · exact Or.inl hZ
      · apply intervalProp_of_postnikovTower C σ.slicing F.toPostnikovTower
        intro i
        have hsem := F.semistable i
        change σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin (F.φ i) _ at hsem
        rcases hsem with hZ_i | ⟨a_i, b_i, hab_i, hthin_i, _, _, hSS_i⟩
        · exact Or.inl hZ_i
        · have ⟨hlo, hhi⟩ := phase_confinement_from_stabSeminorm C σ W hW hab_i
            hε₀ hε₀2 hthin_i hsin hSS_i
          exact σ.slicing.intervalProp_of_intrinsic_phases C hSS_i.2.1
            (by
              have hleft := (hF i).1
              dsimp [δ'] at hleft
              linarith [hlo, min_le_left (δ / 2) (1 / 4 : ℝ)])
            (by
              have hright := (hF i).2
              dsimp [δ'] at hright
              linarith [hhi, min_le_left (δ / 2) (1 / 4 : ℝ)])
    let I :
        (σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin).IntervalCat C
            (t - δ') (t + δ') ⥤
          σ.slicing.IntervalCat C (t - (ε₀ + δ)) (t + (ε₀ + δ)) :=
      ObjectProperty.ιOfLE hIncl
    letI : Fact (t - (ε₀ + δ) < t + (ε₀ + δ)) := ⟨by linarith [hε₀, hδ]⟩
    letI : Fact ((t + (ε₀ + δ)) - (t - (ε₀ + δ)) ≤ 1) := ⟨by linarith [hδ_half]⟩
    have hI : IsArtinianObject (I.obj E) ∧ IsNoetherianObject (I.obj E) :=
      hlf_σ t (I.obj E)
    haveI : IsArtinianObject (I.obj E) := hI.1
    haveI : IsNoetherianObject (I.obj E) := hI.2
    have hstrictE :
        IsStrictArtinianObject E ∧ IsStrictNoetherianObject E :=
      interval_strictFiniteLength_of_inclusion (C := C)
        (s₁ := σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin) (s₂ := σ.slicing)
        (a₁ := t - δ') (b₁ := t + δ') (a₂ := t - (ε₀ + δ)) (b₂ := t + (ε₀ + δ))
        hIncl (X := E)
    haveI : IsStrictArtinianObject E := hstrictE.1
    haveI : IsStrictNoetherianObject E := hstrictE.2
    exact ⟨inferInstance, inferInstance⟩
  · -- Distance bound: d(P, Q) ≤ ε₀ by phase confinement
    set Q := σ.deformedSlicing C W hW ε₀ hε₀ hε₀2 hε₀8 hWide hsin
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
          hε₀ hε₀2 hε₀8 hWide hsin (F.semistable i) hFi hδ
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

variable [IsTriangulated C] in
/-- **Local connectedness of `Stab(D)`**: every basis neighbourhood is contained in
the topological connected component of its centre.

This is the path-connectedness content of Bridgeland's Theorem 1.2 proof (§7).
For `τ ∈ basisNhd(σ, ε)`, the linear interpolation `W_t = Z(σ) + t·(Z(τ) − Z(σ))`
and `γ(t) = bridgeland_7_1(σ, W_t, ε₀)` define a path from `σ` to `τ`.
Path-continuity at `t₀` follows from applying Theorem 7.1 centred at `γ(t₀)` with
a small `ε′`, then **Lemma 6.4** (uniqueness for same `Z` and `d < 1`) identifies
the result with `γ(t)`. The image of `[0, 1]` is therefore preconnected. -/
theorem basisNhd_subset_connectedComponent (σ : StabilityCondition C)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    basisNhd C σ ε ⊆ {τ | ConnectedComponents.mk τ = ConnectedComponents.mk σ} := by
  sorry

end CategoryTheory.Triangulated
