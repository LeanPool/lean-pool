/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ShiftedTripleInterpolation
public import LeanPool.EhrhardGaussian.Ehrhard.ShiftedFunctionalLimit
public import LeanPool.EhrhardGaussian.Ehrhard.LiftedFamilyBounds
public import LeanPool.EhrhardGaussian.Ehrhard.OUQuantileGap

/-! # The strict functional comparison for regular scalar triples -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- A regular scalar triple satisfying a strict quantile gap obeys the correlated Gaussian
functional comparison. -/
theorem smooth_triple_quantile_comparison {f : Fin 3 → ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hcompact : ∀ i, HasCompactSupport (deriv (f i)))
    {lo hi p q ρ σ η : ℝ} (hlo : 0 < lo) (hhi : hi < 1)
    (hbound : ∀ i z, f i z ∈ Icc lo hi) (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (hρ : |ρ| < 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (hη : 0 < η) (hgap : ∀ y : Fin 2 → ℝ,
      quantileLinear (tripleTheta p q σ) (fun i => tripleLift f p q ρ i y) ≤ -η) :
    quantileLinear (tripleTheta p q σ)
      (fun i => ∫ y, tripleLift f p q ρ i y ∂standardGaussianMeasure 2) < 0 := by
  obtain ⟨M, hM, hderiv⟩ := exists_common_compact_scalar_bounds hf hcompact
  have hB : 0 ≤ max |lo| |hi| := (abs_nonneg lo).trans (le_max_left _ _)
  obtain ⟨hregular, A, hA, hgrad, hsecond, hgen⟩ := lifted_family_bounds hf hB hM
    (fun i y => abs_le_max_abs_abs (hbound i y).1 (hbound i y).2) hderiv (tripleGaussianFactor p q
      ρ)
  have hinput (i) (y) : tripleLift f p q ρ i y ∈ Icc lo hi := hbound i _
  have hf₂ := fun i => hasPolynomiallyBoundedSecond_of_third (hregular i)
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf₂ i)
  obtain ⟨ε, hε, hgapε⟩ := exists_ou_quantile_gap hf₂ hlo hhi hA hη hinput hgen
    (tripleTheta p q σ) hgap
  have hgapε' : ∀ y, quantileLinear (tripleTheta p q σ) (ouFamily (tripleLift f p q ρ) (ε, y)) ≤ -(η
    / 2) := by
    change ∀ y, quantileLinear (tripleTheta p q σ)
      (ouFamily (fun i => f i ∘ coordinateForm (tripleGaussianFactor p q ρ i)) (ε, y)) ≤ -(η / 2)
    simpa only [neg_div] using hgapε
  obtain ⟨R, hR, hstay⟩ := shifted_triple_interpolation (fun i => (hf i).continuous.measurable)
    hlo hhi hbound hp hq hsum hρ hσ hvar hε (half_pos hη) hregular hA hA hA hgrad hsecond hgen
      hgapε'
  have hlimit := tendsto_interpolationFunctional_ouFamily_atTop (tripleTheta p q σ) R ε hf₁ hlo hhi
    hinput 0
  have hle := le_of_tendsto hlimit (eventually_atTop.mpr ⟨ε, fun t ht => hstay t ht 0⟩)
  have hd : 0 < Real.sqrt (1 - Real.exp (-ε)) :=
    Real.sqrt_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hε])))
  have hb : gaussianCDF (-(R * Real.sqrt (1 - Real.exp (-ε))) * (η / 2)) < gaussianCDF 0 :=
    strictMono_gaussianCDF (by nlinarith only [mul_pos (mul_pos hR hd) (half_pos hη)])
  have hlt := hle.trans_lt hb
  change gaussianCDF (R * quantileLinear (tripleTheta p q σ)
    (fun i => ∫ y, tripleLift f p q ρ i y ∂standardGaussianMeasure 2)) < gaussianCDF 0 at hlt
  have hprod := strictMono_gaussianCDF.lt_iff_lt.mp hlt
  by_contra hnot
  have hnonneg := mul_nonneg hR.le (le_of_not_gt hnot)
  linarith only [hprod, hnonneg]

end EhrhardGaussian.Ehrhard

end
