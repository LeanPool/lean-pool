/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianBridgeDerivative

/-!
# Ornstein–Uhlenbeck Gaussian averages

The operator is defined by its Gaussian integral. Time differentiation follows
from the proved Gaussian bridge derivative after the change of parameter
`r = exp(-2*t)`. Only positive times are used in the differential identities.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- The standard finite-dimensional OU operator, in its Gaussian integral form. -/
def ouAverage {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ z, F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z)
    ∂standardGaussianMeasure n

/-- The square root of the exponential of minus twice a number equals its negative exponential. -/
theorem sqrt_exp_neg_two (t : ℝ) : Real.sqrt (Real.exp (-2 * t)) = Real.exp (-t) := by
  rw [← Real.exp_half]
  congr 1
  ring

/-- The exponential of minus twice a number is the square of its negative exponential. -/
theorem exp_neg_two_eq_sq (t : ℝ) : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The differentiated OU integral for a polynomially smooth test function. -/
theorem hasDerivAt_ouAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (x : Fin n → ℝ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (ouAverage F x)
      (∫ z, fderiv ℝ F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z)
        (-Real.exp (-t) • x +
          (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) • z)
        ∂standardGaussianMeasure n) t := by
  have hr : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [ht])
  have hbridge := (hasDerivAt_gaussian_bridge_integral hF x (Real.exp_pos _) hr).2
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
      (Real.exp (-2 * t) * (-2)) t := by
    convert ((hasDerivAt_id' t).const_mul (-2)).exp using 1
    ring
  have h := hbridge.comp (h := fun s : ℝ => Real.exp (-2 * s)) t hexp
  simp only [Function.comp_def, sqrt_exp_neg_two] at h
  convert h using 1
  · rfl
  · rw [← integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp only
      have hcoef : (Real.exp (-2 * t) * (-2)) * (1 / (2 * Real.exp (-t))) =
          -Real.exp (-t) := by
        rw [exp_neg_two_eq_sq]
        field_simp
      have hcoef' : -((Real.exp (-2 * t) * (-2)) *
          (1 / (2 * Real.sqrt (1 - Real.exp (-2 * t))))) =
          Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t)) := by ring
      have hv : (Real.exp (-2 * t) * (-2)) •
          ((1 / (2 * Real.exp (-t))) • x -
            (1 / (2 * Real.sqrt (1 - Real.exp (-2 * t)))) • z) =
          -Real.exp (-t) • x +
            (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) • z := by
        rw [smul_sub, smul_smul, smul_smul, hcoef, sub_eq_add_neg, ← neg_smul, hcoef']
      rw [← hv, map_smul, smul_eq_mul, mul_comm]

end EhrhardGaussian.Ehrhard

end
