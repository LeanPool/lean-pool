/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ContinuousTripleComparison

/-! # Scalar marginal formulation of the strict correlated functional comparison -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- The scaled Gaussian mean integrates a scalar function at a scaled standard Gaussian variable. -/
def scaledGaussianMean (f : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ z, f (σ * z) ∂gaussianReal 0 1

/-- The Gaussian quantile inverts the Gaussian distribution function on the real line. -/
theorem gaussianCDFChart_symm_gaussianCDF (x : ℝ) : gaussianCDFChart.symm (gaussianCDF x) = x := by
  apply strictMono_gaussianCDF.injective
  exact gaussianCDF_chart_symm ⟨gaussianCDF_pos x, gaussianCDF_lt_one x⟩

/-- The Gaussian mean of each lifted coordinate equals its scalar Gaussian mean at the corresponding
scale. -/
theorem integral_tripleLift {f : Fin 3 → ℝ → ℝ} (hf : ∀ i, Measurable (f i))
    {p q ρ σ : ℝ} (hρ : ρ ^ 2 ≤ 1) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ) (i : Fin 3) :
    (∫ y, tripleLift f p q ρ i y ∂standardGaussianMeasure 2) = scaledGaussianMean (f i)
      (tripleScales σ i) := by
  have hform := (hasLaw_coordinateForm (tripleGaussianFactor p q ρ i)).integral_comp (hf
    i).aestronglyMeasurable
  rw [tripleFactor_row_variance hρ hvar i] at hform
  have hscale := (hasLaw_gaussian_scale (tripleScales σ i)).integral_comp (hf
    i).aestronglyMeasurable
  exact hform.trans hscale.symm

/-- A uniform strict pointwise quantile gap yields the correlated comparison of scalar Gaussian
means. -/
theorem scalar_strict_triple_comparison {f : Fin 3 → ℝ → ℝ}
    (hf : ∀ i, Continuous (f i)) (c : Fin 3 → ℝ)
    (hcompact : ∀ i, HasCompactSupport (fun y => f i y - c i))
    {lo hi p q ρ σ η : ℝ} (hlo : 0 < lo) (hhi : hi < 1)
    (hbound : ∀ i z, f i z ∈ Icc lo hi) (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (hρ : |ρ| < 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (hη : 0 < η) (hgap : ∀ x y : ℝ,
      p * gaussianCDFChart.symm (f 0 x) + q * gaussianCDFChart.symm (f 1 y) -
        σ * gaussianCDFChart.symm (f 2 (p * x + q * y)) ≤ -η) :
    quantileLinear (tripleTheta p q σ) (fun i => scaledGaussianMean (f i) (tripleScales σ i)) ≤ 0 :=
      by
  have hgap' (y : Fin 2 → ℝ) :
      quantileLinear (tripleTheta p q σ) (fun i => tripleLift f p q ρ i y) ≤ -η := by
    rw [quantileLinear_tripleTheta]
    change p * gaussianCDFChart.symm (f 0 (coordinateForm (tripleGaussianFactor p q ρ 0) y)) +
      q * gaussianCDFChart.symm (f 1 (coordinateForm (tripleGaussianFactor p q ρ 1) y)) -
      σ * gaussianCDFChart.symm (f 2 (coordinateForm (tripleGaussianFactor p q ρ 2) y)) ≤ -η
    rw [tripleFactor_relation]
    exact hgap _ _
  have h := continuous_triple_quantile_comparison hf c hcompact hlo hhi hbound hp hq hsum hρ hσ hvar
    hη hgap'
  have hρsq := (sq_le_one_iff_abs_le_one ρ).mpr hρ.le
  simp_rw [integral_tripleLift (fun i => (hf i).measurable) hρsq hvar] at h
  exact h

end EhrhardGaussian.Ehrhard

end
