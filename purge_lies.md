# Deformation.lean: Declaration-by-Declaration Faithfulness Audit

## NOT Faithful to Bridgeland

| Lines | Declaration | Paper ref | Verdict | Detail |
|-------|------------|-----------|---------|--------|
| 9699-9736 | `deformedPred_of_semistable_of_target_window` | None — paper never does this | **NOT faithful** ✗ | Tries to witness Q(ψ) using interval (a,b) directly. Needs enveloping `a+ε₀ ≤ ψ ≤ b-ε₀` which is **mathematically unprovable** for narrow intervals (b-a < 2ε₀). **2 sorrys at 9725/9727.** Paper uses wider ambient with objects in interior P((a+2ε, b-4ε)) where enveloping is automatic. |
| 9744-9838 | `exists_deformedHN_of_thin_interval` | Lemma 7.7 (p.23) | **NOT faithful** ✗ | Applies Lemma 7.7 to ALL objects in P((a,b)). Paper restricts to **P((a+2ε, b-4ε))** (interior). Wraps factors via sorry'd `deformedPred_of_semistable_of_target_window`. Sorry-free twin `exists_deformedHN_of_enveloped_interval` (line 9889) exists. |
| 10787-10812 | `exists_deformedGt_deformedLe_triangle_of_thin_interval` | p.24 truncation | **NOT faithful** ✗ | Uses sorry-dependent `exists_deformedHN_of_thin_interval`. Sorry-free twin `exists_deformedGt_deformedLe_triangle_of_enveloped_interval` (line 10751) exists. |
| 10820-10858 | `exists_deformedGt_deformedLe_triangle_of_middle_strip` | p.24 middle strip | **NOT faithful** ✗ | Delegates to sorry-dependent `exists_deformedGt_deformedLe_triangle_of_thin_interval` at line 10852. Should use enveloped variant. |
| 10860-10890 | `sigmaSemistable_hasDeformedHN_local` | p.24 (σ-semistable → Q-HN) | **NOT faithful** ✗ | Embeds E ∈ P(φ) in tight interval (φ-η, φ+η), delegates to sorry-dependent `exists_deformedHN_of_thin_interval`. Paper uses wider ambient P((t-3ε, t+5ε)) with interior restriction. |
| 10903-10921 | `sigma_semistable_in_deformedGt` | p.24 ("P(s) ⊂ Q(>t) for s ≥ t+ε") | **NOT faithful** ✗ | Correct math, but calls sorry-dependent `sigmaSemistable_hasDeformedHN_local`. |
| 10926-10944 | `sigma_semistable_in_deformedLe` | p.24 ("P(s) ⊂ Q(≤t) for s ≤ t-ε") | **NOT faithful** ✗ | Same: correct math, sorry-dependent leaf call. |
| 10951-10968 | `sigma_semistable_truncation_middle` | p.24 middle strip truncation | **NOT faithful** ✗ | Calls sorry-dependent `exists_deformedGt_deformedLe_triangle_of_middle_strip`. |
| 11119-11346 | `deformed_truncation_triangle` | p.24 t-structure | **Structure faithful, leaf calls not** ⚠️ | Correct octahedral assembly following p.24. But calls sorry-dependent `exists_deformedGt_deformedLe_triangle_of_thin_interval` at line 11244. Should use enveloped variant. |
| 11348-11435 | `PhasedTower.toHNFiltration` | **Does not exist in paper** | **NOT faithful** ✗✗ | Octahedral insertion sort for unsorted phased towers. Paper never creates unsorted towers. Lemma 7.7 produces sorted filtrations via mdq. p.24 uses iterated truncation. **1 sorry at 11435.** |
| 11438-11673 | `hn_exists_of_sigma_hn` | p.24 final step | **NOT faithful** ✗✗ | Refines σ-HN factor-by-factor, concatenates into PhasedTower, sorts. Paper decomposes via Q-truncation into Q-interval pieces, applies Lemma 7.7 to each in wider ambient. Never concatenates+sorts. |
| 11684-11857 | `deformedSlicing` | p.22-24 Q construction | **Structure faithful, delegation not** ⚠️ | Correct slicing fields. `hn_exists` delegates to sorry-dependent `hn_exists_of_sigma_hn`. |

## Faithful to Bridgeland

| Lines | Declaration | Paper ref | Verdict |
|-------|------------|-----------|---------|
| 52-100 | `StabilityCondition.exists_epsilon0` | §7 p.20 (ε₀ extraction) | ✓ |
| 101-170 | `StabilityCondition.exists_epsilon0_sector` | §7 p.20 | ✓ |
| 143-170 | `SectorFiniteLength`, `WideSectorFiniteLength` | §7 p.20 (local finiteness) | ✓ |
| 179-200 | `intervalProp_of_semistable_near` | Lemma 7.3 setup | ✓ |
| 201-205 | `intervalProp_widen` | Lemma 3.4 interval monotonicity | ✓ |
| 211-226 | `phiPlus_phiMinus_in_interval`, `phiPlus_phiMinus_near` | Lemma 7.3 setup | ✓ |
| 231-238 | `StabilityCondition.slicingDist_le_of_near` | §6 Lemma 6.1 | ✓ |
| 245-282 | `StabilityCondition.W_ne_zero_of_seminorm_lt_one` | §7 p.20 (W nonvanishing) | ✓ |
| 274-283 | `StabilityCondition.skewedStabilityFunction_of_near` | §7 Def 7.2, §4 Def 4.4 | ✓ |
| 290-376 | `StabilityCondition.norm_Z_pos_of_intervalProp` | §7 (sector argument for Z nonvanishing) | ✓ |
| 378-425 | `StabilityCondition.W_ne_zero_of_intervalProp` | §7 (W nonvanishing for interval objects) | ✓ |
| 437-556 | `wPhaseOf_mem_Ioc`, `wPhaseOf_compat`, `wPhaseOf_of_exp`, `wPhaseOf_zero`, `wPhaseOf_neg`, `wPhaseOf_add_two` | §7 p.20 (W-phase definition) | ✓ |
| 570-611 | `SkewedStabilityFunction.Semistable`, `wPhaseOf_indep`, `Semistable.phase_mem_Ioc`, `Semistable.polar` | §7 Def 7.2 (W-semistability) | ✓ |
| 620-755 | `im_sq_le_norm_sq_mul`, `abs_sin_arg_le_norm_sub_one`, `sin_abs_eq_abs_sin`, `abs_arg_one_add_lt`, `wPhaseOf_perturbation_generic` | §7 (phase perturbation estimates) | ✓ |
| 763-818 | `sum_mem_upperHalfPlane`, `arg_sum_le_sup'_of_upperHalfPlane`, `inf'_le_arg_sum_of_upperHalfPlane` | §7 (arg convexity for sums) | ✓ |
| 823-916 | `wPhaseOf_Z_eq`, `wPhaseOf_perturbation`, `hperturb_of_stabSeminorm` | §7 p.20 (perturbation bound) | ✓ |
| 920-932 | `mem_upperHalfPlaneUnion_of_arg_pos` | §7 supporting | ✓ |
| 938-1015 | `wPhaseOf_gt_of_mem_upperHalfPlaneUnion`, `mem_upperHalfPlaneUnion_of_wPhaseOf_gt`, `wPhaseOf_sum_gt`, `im_pos_of_phase_above`, `im_sum_pos_of_all_pos`, `wPhaseOf_gt_of_im_pos` | Lemma 7.3 infrastructure | ✓ |
| 1046-1135 | `im_neg_of_phase_below`, `im_sum_neg_of_all_neg`, `wPhaseOf_lt_of_im_neg`, `im_eq_zero_of_wPhaseOf_eq`, `im_pos_of_sum_zero_and_neg` | Lemma 7.3 dual infrastructure | ✓ |
| 1144-1366 | `wPhaseOf_seesaw`, `wPhaseOf_seesaw_strict`, `wPhaseOf_seesaw_dual`, `wPhaseOf_lt_of_add_le_lt`, `wPhaseOf_lt_of_add_le_gt` | §7 (phase see-saw lemma) | ✓ |
| 1374-1593 | `im_W_pos_of_intervalProp`, `im_W_neg_of_intervalProp`, `wPhaseOf_gt_of_intervalProp`, `wPhaseOf_lt_of_intervalProp` | **Lemma 7.3(b)** (W-phase range for interval objects) | ✓ |
| 1604-1892 | `phiPlus_le_of_wSemistable`, `phiMinus_ge_of_wSemistable`, `phase_confinement_of_wSemistable`, `hom_eq_zero_of_wSemistable_gap` | **Lemma 7.3** (phase confinement) | ✓ |
| 1928-2152 | `SkewedStabilityFunction.phase_le_of_strictQuotient`, `phase_le_of_triangle_quotient`, `phase_confinement_from_stabSeminorm` | **Lemma 7.3** continued | ✓ |
| 2154-2170 | `gtProp_of_wSemistable_phase_gt` | Lemma 7.3 corollary | ✓ |
| 2171-2187 | `ltProp_of_wSemistable_phase_lt` | Lemma 7.3 corollary | ✓ |
| 2188-2329 | `wPhaseOf_eq_of_semistable_of_target_envelope`, `semistable_of_target_envelope_triangleTest`, `stabSeminorm_lt_cos_of_hsin_hthin`, `wPhaseOf_eq_of_intervalProp_upper_inclusion`, `wPhaseOf_eq_of_intervalProp_lower_inclusion` | **Lemma 7.5** infrastructure | ✓ |
| 2329-2609 | `wPhaseOf_mem_Ioo_of_intervalProp_target_envelope`, `exists_upper_boundary_triangle`, `gtProp_of_geProp_of_lt`, `wPhaseOf_gt_of_geProp_target` | Lemma 7.5 boundary arguments | ✓ |
| 2609-3036 | `intervalProp_of_upper_boundary_triangle`, `wPhaseOf_gt_of_upper_boundary_triangle`, `wPhaseOf_gt_of_upper_source_boundary_target`, `wPhaseOf_gt_of_upper_source_boundary_P_phi`, `wPhaseOf_lt_of_leProp_source`, `exists_lower_boundary_triangle`, `intervalProp_of_lower_boundary_triangle`, `wPhaseOf_lt_of_lower_boundary_triangle`, `wPhaseOf_lt_of_lower_source_boundary_target`, `wPhaseOf_lt_of_lower_source_boundary_P_phi`, `exists_upper_boundary_strictShortExact`, `exists_lower_boundary_strictShortExact` | Lemma 7.5 boundary infrastructure | ✓ |
| 3037-3194 | `intervalProp_of_wSemistable_upper_target`, `intervalProp_of_wSemistable_lower_target` | Lemma 7.5 interval transport | ✓ |
| 3194-3560 | Thin-interval Phase 3 selection: `intervalSubobject_*`, `intervalInclusion_map_strictMono`, `interval_strict*Object_of_inclusion*`, `SectorFiniteLength.of_wide`, `interval_K0_of_strictMono` | §7 (thin interval finite-length infrastructure) | ✓ |
| 3560-3992 | `intervalLiftSub*`, `SkewedStabilityFunction.exists_phase_gt_strictSubobject_of_not_semistable`, `intervalLiftSubCokernelIso`, `SkewedStabilityFunction.exists_minPhase_maximal_strictKernel`, `exists_minPhase_minimal_strictKernel` | §7 / Prop 2.4 adapted (mdq infrastructure in thin intervals) | ✓ |
| 3993-4141 | `SkewedStabilityFunction.exists_maxPhase_maximal_strictSubobject*`, `semistable_of_maxPhase_strictSubobject` | Prop 2.4 adapted (max-phase subobject) | ✓ |
| 4141-4546 | `interval_pullbackπ_strictEpi_of_strictEpi`, `interval_pullback_arrow_strictMono_of_strictMono`, `interval_le_pullback_cokernel`, `interval_ofLE_pullbackπ_eq_zero`, `interval_strictShortExact_of_kernel_strictEpi`, `interval_strictShortExact_pullback_left`, `interval_strictShortExact_pullback_right`, `interval_strictShortExact_ofLE_pullbackπ_cokernel` | §7 (thin-interval pullback infrastructure for Lemma 7.5) | ✓ |
| 4546-4966 | `semistable_of_upper_inclusion`, `SkewedStabilityFunction.semistable_of_iso`, `maxPhase_strictSubobject_ne_top_of_not_semistable`, `phase_gt_of_maxPhase_strictSubobject_of_not_semistable` | **Lemma 7.5** (interval independence of semistability) | ✓ |
| 4966-5177 | `SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable*` | Lemma 7.5 (first destabilizing SES) | ✓ |
| 5177-5591 | `interval_pullback_cokernel_bot_eq`, `interval_cokernel_nonzero_of_ne_top`, `interval_pullback_ofLE_comm`, `Wobj_pullback_eq_add`, `interval_lt_pullback_cokernel_of_ne_bot`, `interval_pullback_cokernel_ne_top_of_ne_top`, `Wobj_cokernel_pullback_eq`, `Wobj_liftSub_cokernel_eq_add`, `semistable_cokernel_of_minPhase_strictKernel` | Lemma 7.5 (cokernel phase analysis) | ✓ |
| 5591-5929 | `semistable_of_lower_inclusion`, `semistable_of_interval_inclusion`, `semistable_of_target_subinterval`, `semistable_of_target_envelope` | **Lemma 7.5** (complete interval transport) | ✓ |
| 5929-6073 | `SkewedStabilityFunction.phase_le_of_strictQuotient_of_window`, `phase_cokernel_lt_of_phase_gt_strictSubobject`, `ThinFiniteLengthInInterval` | §7 (thin interval setup) | ✓ |
| 6074-6134 | `ThinFiniteLengthInInterval.of_wide`, `ThinFiniteLengthInInterval.of_ambient`, `thinFiniteLength_of_node78_window` | §7 p.20 (finite length derivation) | ✓ |
| 6135-6730 | `SkewedStabilityFunction.exists_semistable_strictQuotient_le_phase_of_finiteLength`, `IsStrictMDQ.*`, `SkewedStabilityFunction.exists_strictMDQ_of_finiteLength` | **Prop 2.4** adapted to quasi-abelian (mdq construction) | ✓ |
| 6731-7740 | `wPhaseOf_gt_of_strictQuotient_of_inner_strip`, `IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable`, `phase_lt_of_strictQuotient_of_kernel`, `isStrictMDQKernel_of_minPhase_strictKernel*`, `semistable_cokernel_of_minPhase_strictKernel_of_minimal*`, `phase_lt_of_strictQuotient_of_minPhase_strictKernel`, `thinFiniteLength_cokernel`, `isStrictMDQKernel_of_minPhase_strictKernel_of_finiteLength` | Prop 2.4 adapted (kernel/cokernel phase analysis for HN) | ✓ |
| 7740-8093 | `SkewedStabilityFunction.hn_exists_in_thin_interval*` | **Lemma 7.7 core** (HN in thin quasi-abelian, sorry-free) | ✓ |
| 8094-8196 | `intervalProp_of_postnikovTower`, `gtProp_of_postnikovTower`, `ltProp_of_postnikovTower` | **Lemma 3.4** (extension closure of interval membership) | ✓ |
| 8196-8556 | `im_Z_nonpos_of_heart_phases`, `P_phi_of_im_zero_heart`, `P_phi_of_heart_triangle`, `im_Z_nonneg_of_phases_above`, `P_phi_of_im_zero_above` | §5 (P(φ) closure under K₀ decomposition) | ✓ |
| 8557-9000 | `StabilityCondition.P_phi_biprod`, `P_phi_hom_vanishing`, `P_phi_of_truncation_of_P_phi_cone`, `StabilityCondition.P_phi_admissible` | **Lemma 5.2** (P(φ) is abelian) | ✓ |
| 9001-9018 | `StabilityCondition.deformedPred` | §7 p.22 (Q(ψ) definition) | ✓ |
| 9021-9055 | `deformedPred_zero`, `deformedPred_closedUnderIso` | §7 (Q(ψ) closure properties) | ✓ |
| 9056-9198 | `gtProp_of_lt_phiMinus_smallGap`, `leProp_of_phiPlus_le_smallGap`, `geProp_of_phiMinus_ge_smallGap`, `mem_phaseShiftHeart_of_phaseBounds_smallGap`, `gtProp_leProp_of_phaseShiftHeart`, `geProp_leProp_of_phaseShiftHeart`, `midpoint_*_target_thin`, `mem_phaseShiftHeart_of_midpoint_*` | §7 (heart membership for hom-vanishing) | ✓ |
| 9220-9567 | `StabilityCondition.hom_eq_zero_of_deformedPred` | **Lemma 7.6** (hom-vanishing for Q) | ✓ |
| 9567-9698 | `chain_hom_eq_zero_of_gt_deformed`, `hom_eq_zero_of_gt_phases_deformed`, `chain_hom_eq_zero_gap_deformed`, `hom_eq_zero_of_phase_gap_deformed` | §7 (extension-closed Q(>t), Q(≤t) hom-vanishing) | ✓ |
| 9844-9883 | `hom_eq_zero_of_enveloped_interval_semistable` | Lemma 7.6 for enveloped objects (**sorry-free**) | ✓ |
| 9889-9938 | `exists_deformedHN_of_enveloped_interval` | **Lemma 7.7** with enveloping (**sorry-free**) | ✓ |
| 9943-9992 | `deformedGtPred`, `deformedLePred`, `deformedLtPred`, `deformedLePred_mono`, `deformedLtPred_mono`, `deformedLePred_of_deformedLtPred` | §7 p.24 (Q(>t), Q(≤t), Q(<t) definitions) | ✓ |
| 10023-10089 | `hom_eq_zero_of_deformedGt_deformedLe`, `hom_eq_zero_of_deformedGt_deformedLt`, `semistable_of_hn_length_one` | §7 p.24 (Q-hom-vanishing) | ✓ |
| 10090-10224 | `append_hn_filtration_of_triangle` | Standard (HN appending via triangle) | ✓ |
| 10225-10341 | `PhasedTower.appendFactor`, `PhasedTower.ofIso`, `PhasedTower.prefix` | Standard (PhasedTower infrastructure) | ✓ |
| 10342-10476 | `split_hn_filtration_at_cutoff` | Standard (HN splitting at cutoff) | ✓ |
| 10483-10706 | `PhasedTower.appendOfTriangle`, `PhasedTower.appendOfTriangle_bound` | Standard (PhasedTower concatenation) | ✓ |
| 10707-10750 | `exists_deformedGt_deformedLe_triangle_of_hn` | §7 (truncation from HN) | ✓ |
| 10751-10781 | `exists_deformedGt_deformedLe_triangle_of_enveloped_interval` | §7 p.24 truncation (**sorry-free**) | ✓ |
| 10976-11005 | `deformedGtPred_of_triangle` | §7 p.24 (Q(>t) extension closure) | ✓ |
| 11005-11032 | `deformedLePred_of_triangle` | §7 p.24 (Q(≤t) extension closure) | ✓ |
| 11032-11074 | `deformedGtPred_of_postnikovTower` | §7 p.24 (Q(>t) tower closure) | ✓ |
| 11074-11112 | `deformedLePred_of_postnikovTower` | §7 p.24 (Q(≤t) tower closure) | ✓ |
| 11859-11880 | `deformedSlicing_compat` | §5 Def 5.1 (W-compatibility) | ✓ |
| 11894-11955 | Z-ray lemma note, `K0_of_shortExact_P_phi` | §5 (K₀ additivity) | ✓ |
| 11957-12088 | `stabilityFunctionOnP_phase_eq_wPhaseOf`, `wPhaseOf_eq_at_phi_*`, `intervalProp_P_phi_*`, `strictFiniteLength_of_mem_P_phi_sector`, `strictFiniteLength_of_target_interval` | §7 (reverse phase confinement step A1) | ✓ |
| 12088-12665 | `strictFiniteLength_of_upper_source`, `exists_upper_source_first_strictShortExact_*`, `strictFiniteLength_of_lower_source`, `exists_lower_source_first_strictShortExact_*`, `exists_target_first_strictShortExact_*`, `wPhaseOf_eq_*_midpoint_of_mem_P_phi` | §7 (source envelope infrastructure) | ✓ |
| 12666-13965 | `leProp_of_phiPlus_le`, `gtProp_of_lt_phiMinus`, `mem_phaseShiftHeart_of_phaseBounds`, `upper_source_strictSubobject_mem_phiHeart`, `target_strictSubobject_mem_phiHeart`, `upper_source_leftHeartMono_mem_target`, `upper_source_strictSubobject_mem_target`, `exists_upper_source_image_factorisation_*`, `exists_target_image_factorisation_*`, `lower_source_strictSubobject_mem_phiHeart`, `mono_of_mono_of_le`, `mem_phiHeart_of_mem_P_phi`, `P_phi_of_heart_triangle'`, `exists_P_phi_image_factorisation_*`, `wPhaseOf_le_of_mono_P_phi_semistable`, `exists_P_phi_image_factorisation_phase_le`, `compare_strongEpi_monoFactorisations`, `exists_target_P_phi_image_factorisation_phase_le`, `exists_upper_source_P_phi_image_factorisation_phase_le`, `exists_lower_source_P_phi_image_factorisation_phase_le` | §7 (P(φ) image factorisation for reverse confinement) | ✓ |
| 14025-14146 | `wPhaseOf_gt_of_upper_source_P_phi_image_triangle`, `cross_eq_norm_mul_sin'`, `cross_pos_of_arg_lt'`, `arg_lt_of_cross_pos'`, `arg_add_lt_max'` | §7 (cross-product phase arguments) | ✓ |
| 14147-14329 | `wPhaseOf_ge_of_epi_P_phi_semistable`, `exists_P_phi_quotient_factorisation_phase_ge` | §7 (epi factorisation) | ✓ |
| 14329-14631 | `P_phi_subobject_strict_in_interval`, `P_phi_finiteLength`, `stabilityFunctionOnP_hasHN`, `abelianHNFactorObj_*`, `abelianHNFactorPhase_*` | §7 step A2 (P(φ) finite length + abelian HN) | ✓ |
| 14662-14721 | `upper_source_semistable_of_P_phi_wSemistable` (partial) | §7 step A3 | ⚠️ sorry at 14721 (off critical path) |
| 14736-14750 | `lower_source_semistable_of_P_phi_wSemistable` | §7 step A3 | ⚠️ sorry at 14750 (off critical path) |
| 14762-14817 | `target_semistable_of_P_phi_wSemistable` | §7 step A3 | ✓ (delegates to above) |
| 14835-14940 | `P_phi_wSemistable_is_deformedPred`, `stabilityFunctionOnP_semistable_deformedPred_canonical` | §7 (P(φ) bridge) | ✓ |
| 14941-15081 | `stabilityFunctionOnP_semistable_deformedPred`, `abelianHN_stepTriangle`, `abelianHNFactorObj_deformedPred`, `abelianHNFactorPhase_deformedPred` | §7 (abelian HN → deformed pred) | ✓ |
| 15081-15341 | `pphiHNBridge_*`, `stabilityFunctionOnP_hasDeformedHN`, `stabilityFunctionOnP_semistable_intervalProp`, `abelianHN_to_intervalProp` | §7 (P(φ) HN bridge infrastructure) | ✓ |
| 15346-15363 | `sigmaSemistable_hasDeformedHN` (commented out) | §7 (old P(φ) bridge route) | N/A (dead code) |
| 15373-15474 | `sigmaSemistable_hasDeformedHN`, `sigmaSemistable_hasDeformedHN_in_window` | §7 (thin-interval route for σ-semistable) | ✓ |
| 15477-15566 | `sigma_semistable_intervalProp` | §7 (reverse phase confinement, main) | ✓ |
| 15567-15670 | `bridgeland_7_1` | **Theorem 7.1** (p.20) | ✓ |
