/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRealTraceStrip
public import LeanPool.EscauriazaSereginSverak.Linear.SmallTimeTrace
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Vanishing initial-time mass on a bounded ball

The zero trace and the weak time derivative bound imply that the normalized
quadratic mass vanishes in shrinking initial-time strips.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology ENNReal

noncomputable section

namespace ESS

/-- The normalized quadratic mass of a zero-trace field vanishes on shrinking
initial-time strips (`lem:ftc-small-time`). -/
theorem buGaussian_initial_trace_strip_tendsto_zero
    {B : Set Vec3} {τ : ℝ}
    (hBopen : IsOpen B) (hBfinite : volume B < ⊤) (hτ : 0 < τ)
    {v : ParabolicPoint → Vec3} {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hcont : ContinuousOn v (spaceTimeSet B (Ico 0 τ)))
    (hzero : ∀ x ∈ B, v ((show ParabolicPoint from (x, 0))) = 0)
    (hweak : HasSpaceTimeWeakDerivs B (Ioo 0 τ) v Dv D2v Dtv)
    (hL2 : (∫⁻ z in spaceTimeSet B (Ioo 0 τ),
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Tendsto (fun ε : ℝ =>
      (∫ q in B ×ˢ Ioc ε (2 * ε),
        vec3EuclideanNorm (v (parabolicHomeomorph.symm q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let K : Set ParabolicPoint := spaceTimeSet B (Ioo 0 τ)
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict B).prod (volume.restrict (Ioo 0 τ))
  let f : Vec3 × ℝ → ℝ := fun q =>
    vec3EuclideanNorm (v (parabolicHomeomorph.symm q)) ^ 2
  let g : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (vec3EuclideanNorm (Dtv (parabolicHomeomorph.symm q)) ^ 2)
  have hDtfin : (∫⁻ z in K, ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hL2
    intro z
    calc
      ‖Dtv z‖ₑ ^ (2 : ℝ) ≤
          ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ) :=
        le_add_of_nonneg_left (by positivity)
      _ ≤ ‖Dv z‖ₑ ^ (2 : ℝ) +
          (‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) :=
        le_add_of_nonneg_left (by positivity)
      _ ≤ ‖v z‖ₑ ^ (2 : ℝ) +
          (‖Dv z‖ₑ ^ (2 : ℝ) +
            (‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ))) :=
        le_add_of_nonneg_left (by positivity)
      _ = ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
          ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ) := by
        simp only [add_assoc]
  have hDtmeas : AEStronglyMeasurable Dtv (volume.restrict K) :=
    hweak.2.2.2.1.aestronglyMeasurable
  have hDtLpK : MemLp Dtv 2 (volume.restrict K) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict K)
      (by norm_num) (by norm_num) hDtmeas).2
    simpa [K] using hDtfin
  have htarget : (volume : Measure ParabolicPoint).restrict K = μ := by
    dsimp [K, μ, spaceTimeSet]
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact (Measure.prod_restrict B (Ioo (0 : ℝ) τ)).symm
  have hDtLp : MemLp Dtv 2 μ := by
    rw [← htarget]
    exact hDtLpK
  have hpres : MeasurePreserving parabolicHomeomorph.symm μ
      ((volume : Measure ParabolicPoint).restrict K) := by
    have h := parabolicHomeomorphSymm_measurePreserving.restrict_preimage_emb
      parabolicHomeomorph.symm.measurableEmbedding K
    convert h using 1
    change ((volume.restrict B).prod (volume.restrict (Ioo 0 τ))) =
      (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ Ioo 0 τ)
    exact Measure.prod_restrict B (Ioo (0 : ℝ) τ)
  have hDtLpProd : MemLp
      (fun q : Vec3 × ℝ => Dtv (parabolicHomeomorph.symm q)) 2 μ :=
    hDtLpK.comp_measurePreserving hpres
  have hnormInt' : Integrable
      (fun q : Vec3 × ℝ => ‖Dtv (parabolicHomeomorph.symm q)‖ ^ 2) μ := by
    exact hDtLpProd.integrable_norm_pow (p := 2) (by norm_num)
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
    apply Integrable.mono' (hnormInt'.const_mul 3) hEuMeas
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
  have hcontProd : ContinuousOn
      (fun q : Vec3 × ℝ => v (parabolicHomeomorph.symm q))
      (B ×ˢ Ioo 0 τ) := by
    apply hcont.comp parabolicHomeomorph.symm.continuous.continuousOn
    intro q hq
    exact ⟨hq.1, ⟨hq.2.1.le, hq.2.2⟩⟩
  have hfcont : ContinuousOn f (B ×ˢ Ioo 0 τ) := by
    exact (continuous_vec3EuclideanNorm.pow 2).comp_continuousOn hcontProd
  have hfmeas : AEStronglyMeasurable f μ := by
    rw [show μ = (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ Ioo 0 τ) by
      dsimp [μ]
      exact Measure.prod_restrict B (Ioo (0 : ℝ) τ)]
    exact hfcont.aestronglyMeasurable
      ((hBopen.measurableSet).prod measurableSet_Ioo)
  have hf0 (q : Vec3 × ℝ) : 0 ≤ f q := sq_nonneg _
  have htrace : ∀ t, 0 < t → t < τ →
      (∫⁻ x, ENNReal.ofReal (f (x, t)) ∂(volume.restrict B)) ≤
        ENNReal.ofReal t *
          ∫⁻ x, ∫⁻ s, g (x, s) ∂(volume.restrict (Ioc 0 t))
            ∂(volume.restrict B) := by
    intro t ht htτ
    have hftc := ftc_small_time hBopen hτ hcont hzero hDtLp
      Dv D2v hweak t ht htτ
    simpa [f, g] using hftc
  exact bu_short_real_trace_strip_tendsto_zero B τ hτ hBfinite
    f hfmeas hf0 g hgmeas hgfin htrace

end ESS
