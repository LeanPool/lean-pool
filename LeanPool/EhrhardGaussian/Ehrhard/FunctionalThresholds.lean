/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalEhrhard

/-! # A threshold formulation avoiding inverse-CDF endpoint limits -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- Gaussian probability thresholds obey the weighted Ehrhard comparison under its pointwise
hypothesis. -/
theorem functional_ehrhard_thresholds {n : ℕ} {u v w : (Fin n → ℝ) → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hutail : Tendsto u (cocompact (Fin n → ℝ)) atBot)
    (hvtail : Tendsto v (cocompact (Fin n → ℝ)) atBot)
    (hwtail : Tendsto w (cocompact (Fin n → ℝ)) atBot)
    {p q U V : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (huU : ∀ x, u x ≤ U) (hvV : ∀ y, v y ≤ V)
    (horiginal : ∀ x y, p * u x + q * v y ≤ w (p • x + q • y))
    {a b : ℝ} (ha : gaussianCDF a ≤ ∫ x, gaussianCDF (u x) ∂standardGaussianMeasure n)
    (hb : gaussianCDF b ≤ ∫ x, gaussianCDF (v x) ∂standardGaussianMeasure n) :
    gaussianCDF (p * a + q * b) ≤ ∫ x, gaussianCDF (w x) ∂standardGaussianMeasure n := by
  have hmu := integral_gaussianCDF_mem_Ioo (standardGaussianMeasure n) hu.measurable
  have hmv := integral_gaussianCDF_mem_Ioo (standardGaussianMeasure n) hv.measurable
  have hmw := integral_gaussianCDF_mem_Ioo (standardGaussianMeasure n) hw.measurable
  have hqa : a ≤ gaussianCDFChart.symm (∫ x, gaussianCDF (u x) ∂standardGaussianMeasure n) := by
    apply strictMono_gaussianCDF.le_iff_le.mp
    rw [gaussianCDF_chart_symm hmu]
    exact ha
  have hqb : b ≤ gaussianCDFChart.symm (∫ x, gaussianCDF (v x) ∂standardGaussianMeasure n) := by
    apply strictMono_gaussianCDF.le_iff_le.mp
    rw [gaussianCDF_chart_symm hmv]
    exact hb
  have h := (add_le_add (mul_le_mul_of_nonneg_left hqa hp.le) (mul_le_mul_of_nonneg_left hqb
    hq.le)).trans
    (functional_ehrhard hu hv hw hutail hvtail hwtail hp hq hsum huU hvV horiginal)
  have hout := strictMono_gaussianCDF.monotone h
  rw [gaussianCDF_chart_symm hmw] at hout
  exact hout

end EhrhardGaussian.Ehrhard

end
