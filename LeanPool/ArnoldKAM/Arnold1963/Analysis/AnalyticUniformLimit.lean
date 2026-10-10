/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.PolydiscCauchy
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Analyticity of uniform limits on complex polydiscs, using the Cauchy integral formula and
convergence of weighted integrals over compact sets.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Complex Filter
open scoped Topology ENNReal
namespace KamProject.Arnold1963

theorem analyticAt_cauchyIntegral {n : ℕ} {f : ComplexSpace n → ℂ}
    {c w : ComplexSpace n} {r : RealSpace n} (hr : ∀ i, 0 ≤ r i)
    (hf : ContinuousOn f (pi univ (fun i => closedBall (c i) (r i))))
    (hw : ∀ i, w i ∈ ball (c i) (r i)) :
    AnalyticAt ℂ (fun a => torusIntegral (fun z => cauchyKernel a z * f z) c r) w := by
  let K : Set (RealSpace n) := Icc 0 (fun _ => 2 * Real.pi)
  let μ : Measure (RealSpace n) := volume.restrict K
  have : IsFiniteMeasure μ := ⟨by
    change (volume.restrict K) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  let g : RealSpace n → ComplexSpace n × ℂ := fun t =>
    (torusMap c r t, (∏ i, (r i : ℂ) * exp (t i * I) * I) * f (torusMap c r t))
  let F : ComplexSpace n × (ComplexSpace n × ℂ) → ℂ :=
    fun x => cauchyKernel x.1 x.2.1 * x.2.2
  have hg : Continuous g := by
    apply Continuous.prodMk (continuous_torusMap c r)
    apply Continuous.mul
    · fun_prop
    · exact hf.comp_continuous (continuous_torusMap c r) (torusMap_mem_pi_closedBall c hr)
  have hF : ∀ t ∈ K, AnalyticAt ℂ F (w, g t) := by
    intro t _
    apply AnalyticAt.mul
    · apply Finset.analyticAt_fun_prod
      intro i _
      apply AnalyticAt.inv
      · exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt _).comp
          (analyticAt_fst.comp analyticAt_snd)).sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt _).comp
            analyticAt_fst)
      · exact torusMap_sub_ne_zero hw t i
    · exact analyticAt_snd.comp analyticAt_snd
  have hA := analyticAt_integral_compact (μ := μ) hg (K := K) isCompact_Icc measurableSet_Icc hF
  convert! hA using 1
  funext a
  simp only [F, g, cauchyKernel, torusIntegral, smul_eq_mul, μ,
    Measure.restrict_restrict measurableSet_Icc, inter_self, K]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  ring

theorem tendsto_weightedIntegral_of_uniform_compact
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X}
    (hK : IsCompact K) (hKm : MeasurableSet K)
    {F : ℕ → X → ℂ} {f a : X → ℂ} (hF : ∀ s, ContinuousOn (F s) K)
    (ha : ContinuousOn a K) (hu : TendstoUniformlyOn F f atTop K) :
    Tendsto (fun s => ∫ x in K, a x * F s x ∂μ) atTop
      (𝓝 (∫ x in K, a x * f x ∂μ)) := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.bddAbove_image
    (hu.continuousOn (Eventually.of_forall hF).frequently).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image ha.norm
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun s => (ha.mul (hF s)).aestronglyMeasurable hKm
  · refine ⟨max B 0 * (C + 1), ?_⟩
    have hb := (uniformContinuous_norm.comp_tendstoUniformlyOn hu).eventually_forall_le
      (show C < C + 1 by linarith) (fun x hx => hC (mem_image_of_mem _ hx))
    filter_upwards [hb] with s hs
    filter_upwards [ae_restrict_mem hKm] with x hx
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      ((hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hs x hx) (le_max_right _ _))
  · filter_upwards [ae_restrict_mem hKm] with x hx
    exact tendsto_const_nhds.mul (hu.tendsto_at hx)

theorem analyticAt_uniform_limit_polydisc {n : ℕ} {F : ℕ → ComplexSpace n → ℂ}
    {f : ComplexSpace n → ℂ} {c : ComplexSpace n} {R : ℝ} (hR : 0 < R)
    (hF : ∀ s, AnalyticOnNhd ℂ (F s) (closedBall c R))
    (hu : TendstoUniformlyOn F f atTop (closedBall c R)) : AnalyticAt ℂ f c := by
  let r : RealSpace n := fun _ => R
  have hp : closedBall c R = pi univ (fun i => closedBall (c i) (r i)) :=
    closedBall_pi c hR.le
  have hfc : ContinuousOn f (closedBall c R) :=
    hu.continuousOn (Eventually.of_forall fun s => (hF s).continuousOn).frequently
  have hm (t : RealSpace n) : torusMap c r t ∈ closedBall c R := by
    rw [hp]
    exact torusMap_mem_pi_closedBall c (fun _ => hR.le) t
  have hc (w : ComplexSpace n) (hw : w ∈ ball c R) :
      torusIntegral (fun z => cauchyKernel w z * f z) c r =
        (2 * Real.pi * I : ℂ) ^ n * f w := by
    have hw' : ∀ i, w i ∈ ball (c i) (r i) := by
      simpa only [ball_pi c hR, mem_univ_pi] using hw
    let a : RealSpace n → ℂ := fun t =>
      (∏ i, (r i : ℂ) * exp (t i * I) * I) * cauchyKernel w (torusMap c r t)
    have ha : Continuous a := by
      apply Continuous.mul
      · fun_prop
      · apply continuous_finsetProd
        intro i _
        exact (((continuous_apply i).comp (continuous_torusMap c r)).sub
          continuous_const).inv₀ (fun t => torusMap_sub_ne_zero hw' t i)
    have ht := tendsto_weightedIntegral_of_uniform_compact
      (μ := (volume : Measure (RealSpace n)))
      (K := Icc (0 : RealSpace n) (fun _ => 2 * Real.pi)) isCompact_Icc measurableSet_Icc
      (fun s => ((hF s).continuousOn.comp_continuous
        (continuous_torusMap c r) hm).continuousOn) ha.continuousOn
      ((hu.comp (torusMap c r)).mono (fun t _ => hm t))
    have ht' : Tendsto (fun s => torusIntegral (fun z => cauchyKernel w z * F s z) c r)
        atTop (𝓝 (torusIntegral (fun z => cauchyKernel w z * f z) c r)) := by
      simpa only [torusIntegral, smul_eq_mul, a, mul_assoc, Function.comp_def] using! ht
    have he (s : ℕ) := polydisc_cauchy (f := F s) (fun _ => hR) (hp ▸ hF s) hw'
    have hs : Tendsto (fun s => torusIntegral (fun z => cauchyKernel w z * F s z) c r)
        atTop (𝓝 ((2 * Real.pi * I : ℂ) ^ n * f w)) := by
      exact (tendsto_const_nhds.mul (hu.tendsto_at (ball_subset_closedBall hw))).congr'
        (Eventually.of_forall fun s => (he s).symm)
    exact tendsto_nhds_unique ht' hs
  have hA := analyticAt_cauchyIntegral (c := c) (w := c) (fun _ => hR.le)
    (hp ▸ hfc) (fun i => mem_ball_self hR)
  have hne : (2 * Real.pi * I : ℂ) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  apply (analyticAt_const.mul hA).congr
    (g := f) (f := fun w => ((2 * Real.pi * I : ℂ) ^ n)⁻¹ *
      torusIntegral (fun z => cauchyKernel w z * f z) c r)
  filter_upwards [ball_mem_nhds c hR] with w hw
  rw [hc w hw, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem analyticOnNhd_uniform_limit {n : ℕ} {U : Set (ComplexSpace n)}
    (hU : IsOpen U) {F : ℕ → ComplexSpace n → ℂ} {f : ComplexSpace n → ℂ}
    (hF : ∀ s, AnalyticOnNhd ℂ (F s) U) (hu : TendstoUniformlyOn F f atTop U) :
    AnalyticOnNhd ℂ f U := by
  intro c hc
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  have hs : closedBall c (ε / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hε)).trans hsub
  exact analyticAt_uniform_limit_polydisc (half_pos hε)
    (fun s => (hF s).mono hs) (hu.mono hs)

end KamProject.Arnold1963
