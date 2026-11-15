/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ShiftedFunctional
public import LeanPool.EhrhardGaussian.Ehrhard.OULimits

/-! # The infinite-time endpoint of the shifted quantile functional -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- The shifted functional of an Ornstein–Uhlenbeck family tends to its limiting value at the
Gaussian means. -/
theorem tendsto_interpolationFunctional_ouFamily_atTop {n k : ℕ}
    (θ : Fin k → ℝ) (R ε : ℝ) {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedCoordinateDerivatives (f i))
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hbound : ∀ i y, f i y ∈ Icc a b) (x : Fin n → ℝ) :
    Tendsto (fun t => interpolationFunctional θ R ε (t, ouFamily f (t, x))) atTop
      (𝓝 (gaussianFunctional θ R (fun i => ∫ z, f i z ∂standardGaussianMeasure n))) := by
  have hshift : Tendsto (fun t : ℝ => t - ε) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-ε) tendsto_id
  have hscale := (tendsto_interpolationScale_atTop R ε).comp hshift
  have hfamily := tendsto_ouFamily_atTop (fun i => (hf i).1.continuous)
    (fun i y => abs_le_max_abs_abs (hbound i y).1 (hbound i y).2) x
  have hmean : (fun i => ∫ z, f i z ∂standardGaussianMeasure n) ∈ probabilityBox := by
    intro i
    have hi := integral_mem_Icc_of_bounded (hf i) (hbound i)
    exact ⟨ha.trans_le hi.1, hi.2.trans_lt hb⟩
  have hquantile := (contDiffAt_quantileLinear θ hmean).continuousAt.tendsto.comp hfamily
  exact continuous_gaussianCDF.continuousAt.tendsto.comp (hscale.mul hquantile)

end EhrhardGaussian.Ehrhard

end
