/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalChainMeanJumpScale

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalChainTonelli

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Tonelli aggregation for the infinite fractional chain
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The negative dyadic scale power is the growing geometric weight used in
the physical chain-head estimate. -/
theorem ofReal_convexFractionalChainScale_rpow_sub_eq
    (d n : ℕ) (s : ℝ) :
    ENNReal.ofReal (convexFractionalChainScale n ^ (s - (d : ℝ))) =
      ENNReal.ofReal (((2 : ℝ) ^ ((d : ℝ) - s)) ^ n) := by
  apply congrArg ENNReal.ofReal
  unfold convexFractionalChainScale
  calc
    ((1 / 2 : ℝ) ^ n) ^ (s - (d : ℝ)) =
        ((1 / 2 : ℝ) ^ (s - (d : ℝ))) ^ n :=
      (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2) _ _).symm
    _ = ((2 : ℝ) ^ ((d : ℝ) - s)) ^ n := by
      congr 1
      calc
        (1 / 2 : ℝ) ^ (s - (d : ℝ)) =
            ((2 : ℝ)⁻¹) ^ (s - (d : ℝ)) := by rw [one_div]
        _ = ((2 : ℝ) ^ (s - (d : ℝ)))⁻¹ :=
          Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2) _
        _ = (2 : ℝ) ^ (-(s - (d : ℝ))) :=
          (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm
        _ = (2 : ℝ) ^ ((d : ℝ) - s) := by ring_nf

/-- Tonelli exchanges the sum of weighted amplitude masses on the chain balls
with the spatial integral of the pointwise chain-membership weight. -/
theorem tsum_scaleWeight_mul_setLIntegral_chainBall_eq
    {c x : Vec d} {rho s : ℝ} {A : Vec d → ℝ≥0∞}
    (hA : Measurable A) :
    (∑' n : ℕ, ENNReal.ofReal
        (convexFractionalChainScale n ^ (s - (d : ℝ))) *
          ∫⁻ y in convexFractionalChainBall c x rho n, A y ∂volume) =
      ∫⁻ y, ∑' n : ℕ,
        (convexFractionalChainBall c x rho n).indicator
          (fun y => ENNReal.ofReal
            (convexFractionalChainScale n ^ (s - (d : ℝ))) * A y) y ∂volume := by
  let f : ℕ → Vec d → ℝ≥0∞ := fun n y =>
    (convexFractionalChainBall c x rho n).indicator
      (fun y => ENNReal.ofReal
        (convexFractionalChainScale n ^ (s - (d : ℝ))) * A y) y
  have hf : ∀ n, Measurable (f n) := by
    intro n
    exact ((measurable_const.mul hA).indicator
      (isOpen_euclideanBallAt _ _).measurableSet)
  calc
    (∑' n : ℕ, ENNReal.ofReal
        (convexFractionalChainScale n ^ (s - (d : ℝ))) *
          ∫⁻ y in convexFractionalChainBall c x rho n, A y ∂volume) =
        ∑' n : ℕ, ∫⁻ y, f n y ∂volume := by
      apply tsum_congr
      intro n
      dsimp only [f]
      have hball : MeasurableSet (convexFractionalChainBall c x rho n) :=
        (isOpen_euclideanBallAt _ _).measurableSet
      rw [lintegral_indicator hball]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ y, ∑' n : ℕ, f n y ∂volume :=
      (lintegral_tsum fun n => (hf n).aemeasurable).symm
    _ = _ := rfl

end

end HighContrast
end HCPolySupport
