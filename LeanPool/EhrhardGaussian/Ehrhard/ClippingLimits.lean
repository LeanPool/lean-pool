/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.QuantileClipping

/-! # Removing the compatible clipping by dominated convergence -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- The mean of the Gaussian distribution function of a measurable real variable lies strictly
between zero and one. -/
theorem integral_gaussianCDF_mem_Ioo {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {u : Ω → ℝ} (hu : Measurable u) :
    (∫ x, gaussianCDF (u x) ∂μ) ∈ Ioo (0 : ℝ) 1 := by
  have hmeas := continuous_gaussianCDF.measurable.comp hu
  have hint : Integrable (fun x => gaussianCDF (u x)) μ := Integrable.of_bound
    hmeas.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_pos (gaussianCDF_pos _)] using
      (gaussianCDF_lt_one (u x)).le)
  have hsupp : Function.support (fun x => gaussianCDF (u x)) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (gaussianCDF_pos _).ne'
  have hpos : 0 < ∫ x, gaussianCDF (u x) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (gaussianCDF_pos _).le) hint).mpr
    rw [hsupp, measure_univ]
    exact zero_lt_one
  have hsubint := (integrable_const (1 : ℝ)).sub hint
  have hsubsupp : Function.support (fun x => 1 - gaussianCDF (u x)) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sub_pos.mpr (gaussianCDF_lt_one _)).ne'
  have hsubpos : 0 < ∫ x, 1 - gaussianCDF (u x) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => sub_nonneg.mpr (gaussianCDF_lt_one _).le)
      hsubint).mpr
    rw [hsubsupp, measure_univ]
    exact zero_lt_one
  rw [integral_sub (integrable_const (1 : ℝ)) hint] at hsubpos
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hsubpos
  exact ⟨hpos, sub_pos.mp hsubpos⟩

/-- Removing the clipping threshold recovers the original input quantile pointwise. -/
theorem tendsto_clippedInputQuantile {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (u : ℝ → ℝ) (x : ℝ) : Tendsto (fun n => clippedInputQuantile u (L n) x) atTop (𝓝 (u x)) := by
  have heq : (fun n => clippedInputQuantile u (L n) x) =ᶠ[atTop] (fun _ => u x) := by
    filter_upwards [hL.eventually (eventually_ge_atTop (-u x))] with n hn
    exact max_eq_left (by linarith only [hn])
  exact tendsto_const_nhds.congr' heq.symm

/-- Removing the output clipping and quantile shift recovers the original output quantile pointwise.
-/
theorem tendsto_clippedOutputQuantile {L H η : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (hH : Tendsto H atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hηpos : ∀ n, 0 ≤ η n) {σ : ℝ} (hσ : 0 < σ)
    (w : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n => clippedOutputQuantile w σ (η n) (L n) (H n) x) atTop (𝓝 (w x)) := by
  have heq : (fun n => clippedOutputQuantile w σ (η n) (L n) (H n) x) =ᶠ[atTop]
      (fun n => w x + η n / σ) := by
    filter_upwards [hL.eventually (eventually_ge_atTop (-w x)),
      hH.eventually (eventually_ge_atTop (w x + 1)), hη.eventually (gt_mem_nhds hσ)] with n hnL hnH
        hnη
    have hnonneg : 0 ≤ η n / σ := div_nonneg (hηpos n) hσ.le
    have hsmall : η n / σ ≤ 1 := (div_le_iff₀ hσ).mpr (by linarith only [hnη])
    rw [clippedOutputQuantile, max_eq_left (by linarith only [hnL, hnonneg]),
      min_eq_left (by linarith only [hnH, hsmall])]
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => w x) atTop (𝓝 (w x))).add (hη.div_const σ)
  simpa only [zero_div, add_zero] using h.congr' heq.symm

end EhrhardGaussian.Ehrhard

end
