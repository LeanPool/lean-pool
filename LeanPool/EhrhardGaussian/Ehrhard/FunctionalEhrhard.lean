/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianSlices

/-! # Functional Ehrhard inequality in every finite dimension -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure finCons)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- A pointwise Ehrhard comparison implies the corresponding comparison of Gaussian-integrated
quantiles. -/
theorem functional_ehrhard {n : ℕ} {u v w : (Fin n → ℝ) → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hutail : Tendsto u (cocompact (Fin n → ℝ)) atBot)
    (hvtail : Tendsto v (cocompact (Fin n → ℝ)) atBot)
    (hwtail : Tendsto w (cocompact (Fin n → ℝ)) atBot)
    {p q U V : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (huU : ∀ x, u x ≤ U) (hvV : ∀ y, v y ≤ V)
    (horiginal : ∀ x y, p * u x + q * v y ≤ w (p • x + q • y)) :
    p * gaussianCDFChart.symm (∫ x, gaussianCDF (u x) ∂standardGaussianMeasure n) +
      q * gaussianCDFChart.symm (∫ x, gaussianCDF (v x) ∂standardGaussianMeasure n) ≤
        gaussianCDFChart.symm (∫ x, gaussianCDF (w x) ∂standardGaussianMeasure n) := by
  induction n with
  | zero =>
    rw [integral_standardGaussian_zero, integral_standardGaussian_zero,
      integral_standardGaussian_zero,
      gaussianCDFChart_symm_gaussianCDF, gaussianCDFChart_symm_gaussianCDF,
        gaussianCDFChart_symm_gaussianCDF]
    simpa only [smul_zero, zero_add] using horiginal 0 0
  | succ n ih =>
    have hslice (x y : Fin n → ℝ) :
        p * gaussianQuantileMarginal u x + q * gaussianQuantileMarginal v y ≤
          gaussianQuantileMarginal w (p • x + q • y) := by
      have hu₁ : Continuous (fun r : ℝ => u (finCons r x)) :=
        hu.comp (continuous_finCons.comp (continuous_id.prodMk continuous_const))
      have hv₁ : Continuous (fun s : ℝ => v (finCons s y)) :=
        hv.comp (continuous_finCons.comp (continuous_id.prodMk continuous_const))
      have hw₁ : Continuous (fun r : ℝ => w (finCons r (p • x + q • y))) :=
        hw.comp (continuous_finCons.comp (continuous_id.prodMk continuous_const))
      have h := scalar_functional_ehrhard hu₁ hv₁ hw₁
        (hutail.comp (finCons_scalar_cocompact x)) (hvtail.comp (finCons_scalar_cocompact y))
        (hwtail.comp (finCons_scalar_cocompact (p • x + q • y))) hp hq hsum
        (fun r => huU _) (fun s => hvV _)
        (fun r s => by
          simpa only [finCons_linear_combination] using horiginal (finCons r x) (finCons s y))
      simpa only [scaledGaussianMean, one_mul, gaussianQuantileMarginal, gaussianMarginal,
        Function.comp_def] using h
    have h := ih (u := gaussianQuantileMarginal u) (v := gaussianQuantileMarginal v) (w :=
      gaussianQuantileMarginal w)
      (continuous_gaussianQuantileMarginal hu) (continuous_gaussianQuantileMarginal hv)
      (continuous_gaussianQuantileMarginal hw) (tendsto_gaussianQuantileMarginal_atBot hu hutail)
      (tendsto_gaussianQuantileMarginal_atBot hv hvtail) (tendsto_gaussianQuantileMarginal_atBot hw
        hwtail)
      (fun x => gaussianQuantileMarginal_le hu huU x) (fun y => gaussianQuantileMarginal_le hv hvV
        y) hslice
    simp_rw [gaussianCDF_gaussianQuantileMarginal hu, gaussianCDF_gaussianQuantileMarginal hv,
      gaussianCDF_gaussianQuantileMarginal hw] at h
    rw [integral_gaussianMarginal (continuous_gaussianCDF.comp hu)
        (fun z => by
          simpa only [Function.comp_apply, abs_of_pos (gaussianCDF_pos _)] using
            (gaussianCDF_lt_one (u z)).le),
      integral_gaussianMarginal (continuous_gaussianCDF.comp hv)
        (fun z => by
          simpa only [Function.comp_apply, abs_of_pos (gaussianCDF_pos _)] using
            (gaussianCDF_lt_one (v z)).le),
      integral_gaussianMarginal (continuous_gaussianCDF.comp hw)
        (fun z => by
          simpa only [Function.comp_apply, abs_of_pos (gaussianCDF_pos _)] using
            (gaussianCDF_lt_one (w z)).le)] at h
    exact h

end EhrhardGaussian.Ehrhard

end
