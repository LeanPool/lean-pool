/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
Compact-image measure bounds under uniform convergence. Compactness controls image
neighborhoods; injectivity of the limiting map is not assumed.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace KamProject.Arnold1963

variable {α E : Type*} [TopologicalSpace α] [MetricSpace E] [ProperSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem limsup_measure_image_le {K : Set α} (hK : IsCompact K)
    {F : ℕ → α → E} {f : α → E} (hf : ContinuousOn f K)
    (hF : TendstoUniformlyOn F f atTop K) :
    limsup (fun s => μ (F s '' K)) atTop ≤ μ (f '' K) := by
  have hb (r : ℝ) (hr : 0 < r) :
      limsup (fun s => μ (F s '' K)) atTop ≤ μ (cthickening r (f '' K)) := by
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF r hr] with s hs
    apply measure_mono
    rintro _ ⟨x, hx, rfl⟩
    apply mem_cthickening_of_dist_le (F s x) (f x) r (f '' K) (mem_image_of_mem f hx)
    simpa only [dist_comm] using (hs x hx).le
  have ht : Tendsto (fun r => μ (cthickening r (f '' K))) (𝓝[>] (0 : ℝ))
      (𝓝 (μ (f '' K))) :=
    (tendsto_measure_cthickening_of_isCompact (μ := μ) (hK.image_of_continuousOn hf)).mono_left
      inf_le_left
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hb r hr

theorem measure_image_ge_of_uniform_limit {K : Set α} (hK : IsCompact K)
    {F : ℕ → α → E} {f : α → E} (hf : ContinuousOn f K)
    (hF : TendstoUniformlyOn F f atTop K) {a : ℝ≥0∞}
    (ha : ∀ᶠ s in atTop, a ≤ μ (F s '' K)) : a ≤ μ (f '' K) := by
  have hh : a ≤ limsup (fun s => μ (F s '' K)) atTop := by
    apply le_limsup_of_le (by isBoundedDefault)
    intro c hc
    obtain ⟨s, hs, ht⟩ := (ha.and hc).exists
    exact hs.trans ht
  exact hh.trans (limsup_measure_image_le hK hf hF)

theorem measure_image_gt_of_uniform_limit {K : Set α} (hK : IsCompact K)
    {F : ℕ → α → E} {f : α → E} (hf : ContinuousOn f K)
    (hF : TendstoUniformlyOn F f atTop K) {a c : ℝ≥0∞}
    (hca : c < a) (ha : ∀ᶠ s in atTop, a ≤ μ (F s '' K)) : c < μ (f '' K) :=
  hca.trans_le (measure_image_ge_of_uniform_limit hK hf hF ha)

end KamProject.Arnold1963
