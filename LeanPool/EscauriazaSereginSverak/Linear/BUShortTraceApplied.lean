/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTraceData
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Initial-time trace estimate for the rescaled field

The unshifted rescaling of the original field satisfies the sectionwise
trace bound. Its normalized quadratic mass in an initial-time strip
therefore tends to zero.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- The rescaled field has vanishing normalized quadratic mass in
shrinking initial-time strips on the bounded trace ball. -/
theorem bu_short_rescaled_trace_strip_tendsto_zero
    (scale R : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Tendsto (fun ε : ℝ =>
      (∫⁻ t in Ioc ε (2 * ε),
        ∫⁻ x,
          ENNReal.ofReal
            (vec3EuclideanNorm ((buAffineField 0 scale w) (x, t)) ^ 2)
          ∂(volume.restrict (buShortTraceBall R))) /
        ENNReal.ofReal ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let B := buShortTraceBall R
  let v := buAffineField 0 scale w
  let Dv := buAffineDw 0 scale Dw
  let D2v := buAffineD2w 0 scale D2w
  let Dtv := buAffineDtw 0 scale Dtw
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict B).prod (volume.restrict (Ioo 0 1))
  let K := spaceTimeSet B (Ioo (0 : ℝ) 1)
  obtain ⟨hBopen, hBfinite, _⟩ := buShortTraceBall_geometry hR
  obtain ⟨hcontv, hzero, hweakv, hDtLp⟩ :=
    bu_short_trace_rescaled_data scale R hscale hscale1 hR
      w Dw D2w Dtw hcont hinit hweak hL2
  have hpres : MeasurePreserving parabolicHomeomorph.symm μ
      ((volume : Measure ParabolicPoint).restrict K) := by
    have h := parabolicHomeomorphSymm_measurePreserving.restrict_preimage_emb
      parabolicHomeomorph.symm.measurableEmbedding K
    convert h using 1
    change ((volume.restrict B).prod (volume.restrict (Ioo 0 1))) =
      (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ Ioo (0 : ℝ) 1)
    exact Measure.prod_restrict B (Ioo (0 : ℝ) 1)
  have htarget : (volume : Measure ParabolicPoint).restrict K =
      ((volume.restrict B).prod (volume.restrict (Ioo 0 1))) := by
    dsimp [K, spaceTimeSet]
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact (Measure.prod_restrict B (Ioo (0 : ℝ) 1)).symm
  have hDtLpK : MemLp Dtv 2 ((volume : Measure ParabolicPoint).restrict K) := by
    rw [htarget]
    exact hDtLp
  have hDtLpProd : MemLp
      (fun q : Vec3 × ℝ => Dtv (parabolicHomeomorph.symm q)) 2 μ :=
    hDtLpK.comp_measurePreserving hpres
  let f : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (vec3EuclideanNorm (v (parabolicHomeomorph.symm q)) ^ 2)
  let g : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (vec3EuclideanNorm (Dtv (parabolicHomeomorph.symm q)) ^ 2)
  have hnormInt : Integrable
      (fun q : Vec3 × ℝ => ‖Dtv (parabolicHomeomorph.symm q)‖ ^ 2) μ := by
    simpa only [μ] using hDtLpProd.integrable_norm_pow (p := 2) (by norm_num)
  have hEuMeas : AEStronglyMeasurable
      (fun q : Vec3 × ℝ =>
        vec3EuclideanNorm (Dtv (parabolicHomeomorph.symm q)) ^ 2) μ :=
    (continuous_vec3EuclideanNorm.pow 2).comp_aestronglyMeasurable
      hDtLpProd.aestronglyMeasurable
  have hbound (q : Vec3 × ℝ) :
      vec3EuclideanNorm (Dtv (parabolicHomeomorph.symm q)) ^ 2 ≤
        3 * ‖Dtv (parabolicHomeomorph.symm q)‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm
      (Dtv (parabolicHomeomorph.symm q))
    have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := by norm_num
    have hnn : 0 ≤ vec3EuclideanNorm (Dtv (parabolicHomeomorph.symm q)) :=
      vec3EuclideanNorm_nonneg _
    have hn : 0 ≤ Real.sqrt 3 * ‖Dtv (parabolicHomeomorph.symm q)‖ := by
      positivity
    nlinarith only [h, hs, hnn, hn,
      sq_nonneg (‖Dtv (parabolicHomeomorph.symm q)‖)]
  have hEuInt : Integrable
      (fun q : Vec3 × ℝ =>
        vec3EuclideanNorm (Dtv (parabolicHomeomorph.symm q)) ^ 2) μ := by
    apply Integrable.mono' (hnormInt.const_mul 3) hEuMeas
    filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound q
  have hgmeas : AEMeasurable g μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      hEuMeas.aemeasurable
  have hgfin : (∫⁻ q, g q ∂μ) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact (lintegral_ofReal_ne_top_iff_integrable hEuMeas
      (Filter.Eventually.of_forall (fun q => sq_nonneg _))).2 hEuInt
  have htrace : ∀ t, 0 < t → t < (1 : ℝ) →
      (∫⁻ x, f (x, t) ∂(volume.restrict B)) ≤
        ENNReal.ofReal t *
          ∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 t))
            ∂(volume.restrict B) := by
    intro t ht ht1
    exact ftc_small_time hBopen (by norm_num) hcontv hzero hDtLp
      Dv D2v hweakv t ht ht1
  exact bu_short_trace_strip_tendsto_zero B 1 (by norm_num)
    hBfinite f g hgmeas hgfin htrace

end ESS
