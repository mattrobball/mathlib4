/-
  Dead code: unfaithful thin-interval HN declarations removed from Deformation.lean.

  These apply Lemma 7.7 to all P((a,b)) objects instead of restricting to
  interior P((a+2ε, b-4ε)) as the paper does. The faithful versions are
  `exists_deformedHN_of_enveloped_interval` (line ~9910 of Deformation.lean).

  Moved here 2026-03-16 as part of the unfaithful-code purge.
-/

-- Original: Deformation.lean lines 9729-9828
/-
variable [IsTriangulated C] in
/-- A faithful local 7.7 bridge: any object in a thin finite-length interval admits a
`Q`-HN filtration by first constructing a `W`-HN filtration in that thin category and then
re-witnessing each semistable factor in its own centered target window. Unlike
`exists_deformedHN_of_enveloped_interval`, this theorem does not require a global
enveloping window for the whole ambient interval. -/
private theorem exists_deformedHN_of_thin_interval
    (σ : StabilityCondition C) (W : K₀ C →+ ℂ)
    (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ G : HNFiltration C (σ.deformedPred C W hW ε₀ hε₀ hε₀2 hsin) X.obj,
      ∀ j, a - ε₀ < G.φ j ∧ G.φ j < b + ε₀ := by
  let ssf : SkewedStabilityFunction C σ.slicing a b :=
    σ.skewedStabilityFunction_of_near C W hW hab
  have hthin' : b - a < 1 := by
    linarith
  have hsmall :
      stabSeminorm C σ (W - σ.Z) <
        ENNReal.ofReal (Real.cos (Real.pi * (b - a) / 2)) :=
    stabSeminorm_lt_cos_of_hsin_hthin
      (C := C) (σ := σ) (W := W) hab hε₀ hε₀2 hthin hsin
  have hW_interval :
      ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
        W (K₀.of C F) ≠ 0 := by
    intro F hF hFne
    exact σ.W_ne_zero_of_intervalProp C W hthin' hsmall hFne hF
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
  have hWindow :
      ∀ {F : C}, σ.slicing.intervalProp C a b F → ¬IsZero F →
        a - ε₀ < wPhaseOf (W (K₀.of C F)) ((a + b) / 2) ∧
          wPhaseOf (W (K₀.of C F)) ((a + b) / 2) < b + ε₀ := by
    intro F hF hFne
    exact ⟨wPhaseOf_gt_of_intervalProp C σ hFne W (by linarith) hF hW_ne hpert_lo,
      wPhaseOf_lt_of_intervalProp C σ hFne W (by linarith) hF hW_ne hpert_hi⟩
  obtain ⟨G, hGφ⟩ :=
    SkewedStabilityFunction.hn_exists_in_thin_interval
      (C := C) (σ := σ) (a := a) (b := b) (ssf := ssf) hFiniteLength
      (fun {F} hF hFne ↦ hW_interval hF hFne)
      (L := a - ε₀) (U := b + ε₀)
      (fun {F} hF hFne ↦ hWindow hF hFne)
      (by linarith [hthin])
      (fun {E F} hE hF hlt f ↦ by
        have hEQ :=
          deformedPred_of_semistable_of_target_window
            (C := C) (σ := σ) (W := W) (hW := hW) hab
            hε₀ hε₀2 hthin hsin (E := E.obj) (by simpa [ssf] using hE)
        have hFQ :=
          deformedPred_of_semistable_of_target_window
            (C := C) (σ := σ) (W := W) (hW := hW) hab
            hε₀ hε₀2 hthin hsin (F := F.obj) (by simpa [ssf] using hF)
        exact σ.hom_eq_zero_of_deformedPred
          (C := C) (W := W) (hW := hW) hε₀ hε₀2 hε₀8 hsin
          hEQ hFQ hlt f) X hX
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
        simpa [ssf] using
          deformedPred_of_semistable_of_target_window
            (C := C) (σ := σ) (W := W) (hW := hW) hab
            hε₀ hε₀2 hthin hsin (E := G.factor j) (G.semistable j) }
  refine ⟨GQ, ?_⟩
  intro j
  simpa using hGφ j
-/

-- Original: Deformation.lean lines 9830-9859
/-
variable [IsTriangulated C] in
/-- Faithful Node 7.8c local wrapper: an object in any thin finite-length interval admits the
paper's `Q(> t) / Q(≤ t)` truncation triangle by first taking the local `Q`-HN filtration
from Lemma 7.7 and then splitting it at the cutoff `t`. -/
private theorem exists_deformedGt_deformedLe_triangle_of_thin_interval
    (σ : StabilityCondition C)
    (W : K₀ C →+ ℂ) (hW : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal 1)
    {a b ε₀ : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFiniteLength : ThinFiniteLengthInInterval (C := C) σ a b)
    (hε₀ : 0 < ε₀) (hε₀2 : ε₀ < 1 / 4) (hε₀8 : ε₀ < 1 / 8)
    (hthin : b - a + 2 * ε₀ < 1)
    (hsin : stabSeminorm C σ (W - σ.Z) < ENNReal.ofReal (Real.sin (Real.pi * ε₀)))
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
  obtain ⟨G, _⟩ :=
    exists_deformedHN_of_thin_interval
      (C := C) (σ := σ) (W := W) (hW := hW) hab
      hFiniteLength hε₀ hε₀2 hε₀8 hthin hsin
      (X := EI) hEIne
  exact exists_deformedGt_deformedLe_triangle_of_hn
    (C := C) (σ := σ) (W := W) (hW := hW) hε₀ hε₀2 hsin G t
-/
