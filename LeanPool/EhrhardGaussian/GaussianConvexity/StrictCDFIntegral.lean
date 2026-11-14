/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.WeightedCDFIntegral
public import LeanPool.EhrhardGaussian.EhrhardType.Quantile

/-!
# Weighted differences in the strict-CDF convention

The strict and closed CDF differ at most at countably many thresholds. Their
Lebesgue-weighted difference integrals therefore agree, including for atomic laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace EhrhardGaussian.GaussianConvexity

/-- Strict and closed distribution functions agree at Lebesgue-almost every threshold. -/
theorem strictCDF_ae_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (fun t => μ.real (Iio t)) =ᵐ[volume] (cdf μ) := by
  have hcount := (monotone_cdf μ).countable_not_continuousAt
  filter_upwards [hcount.ae_notMem volume] with t ht
  have hc : ContinuousAt (cdf μ) t := not_not.mp ht
  rw [EhrhardType.strictCDF_eq_leftLim_cdf]
  exact hc.continuousWithinAt.leftLim_eq

/-- The signed strict-CDF difference is integrable under the two exponential moments. -/
theorem integrable_strictCDF_sub_mul_exp {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : ℝ} (hp : p ≠ 0)
    (hμ : Integrable (fun x => Real.exp (p * x)) μ)
    (hν : Integrable (fun x => Real.exp (p * x)) ν) :
    Integrable (fun t => (μ.real (Iio t) - ν.real (Iio t)) * Real.exp (p * t)) := by
  apply (integrable_cdf_sub_mul_exp hp hμ hν).congr
  filter_upwards [strictCDF_ae_eq_cdf μ, strictCDF_ae_eq_cdf ν] with t hμt hνt
  rw [hμt, hνt]

/-- The exact signed strict-CDF formula, valid for positive and negative nonzero parameters. -/
theorem integral_strictCDF_sub_mul_exp {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : ℝ} (hp : p ≠ 0)
    (hμ : Integrable (fun x => Real.exp (p * x)) μ)
    (hν : Integrable (fun x => Real.exp (p * x)) ν) :
    ∫ t, (μ.real (Iio t) - ν.real (Iio t)) * Real.exp (p * t) =
      (mgf id ν p - mgf id μ p) / p := by
  calc
    _ = ∫ t, (cdf μ t - cdf ν t) * Real.exp (p * t) := by
      apply integral_congr_ae
      filter_upwards [strictCDF_ae_eq_cdf μ, strictCDF_ae_eq_cdf ν] with t hμt hνt
      rw [hμt, hνt]
    _ = _ := integral_cdf_sub_mul_exp hp hμ hν

end EhrhardGaussian.GaussianConvexity
