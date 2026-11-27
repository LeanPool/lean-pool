/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointWeightedIncrement
public import LeanPool.VacuumBellSeparation.Constants.Parameters

/-! # The manuscript's fixed reverse exponent gives uniform mass decay -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian

/-- Joint reverse unweighted constant defined as `4000 * jointPolynomialErrorConstant`. -/
def jointReverseUnweightedConstant : ℝ := 4000 * jointPolynomialErrorConstant
/-- Joint reverse weighted constant defined as `67072 * C ^ 2 * (jointWeightedPolynomialBase (1 /
2) + 1)`. -/
def jointReverseWeightedConstant (C : ℝ) : ℝ :=
  67072 * C ^ 2 * (jointWeightedPolynomialBase (1 / 2) + 1)
/-- Joint reverse bound constant defined as `52 * 256 * jointReverseUnweightedConstant ^ (1 -
theta) * jointReverseWeightedConstant C ^ theta`. -/
def jointReverseBoundConstant (C : ℝ) : ℝ :=
  52 * 256 * jointReverseUnweightedConstant ^ (1 - theta) * jointReverseWeightedConstant C ^ theta

theorem sourceMomentLambda_half : sourceMomentLambda (1 / 2) = Lambda0 := by
  unfold sourceMomentLambda Lambda0
  rw [mul_one_div, Real.sin_pi_div_two, div_one]

theorem jointReverseBoundConstant_pos {C : ℝ} (hC : 0 < C) :
    0 < jointReverseBoundConstant C := by
  have hA : 0 < jointReverseUnweightedConstant := mul_pos
    (by norm_num) jointPolynomialErrorConstant_pos
  have ht := jointWeightedPolynomialBase_pos (1 / 2)
  have hB : 0 < jointReverseWeightedConstant C := by unfold jointReverseWeightedConstant; positivity
  unfold jointReverseBoundConstant
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hA _)) (Real.rpow_pos_of_pos hB _)

theorem jointReverse_exponential_le {μ s : ℝ} (hμ : 0 < μ) (hs : 4 ≤ s) :
    Real.exp (-μ * s / 2) ^ (1 - theta) *
      (Real.exp (-μ * s / 2) *
        Real.exp (2 * sourceMomentLambda (1 / 2) * μ * jointMidpointMomentRadius s)) ^ theta ≤
      Real.exp (-(μ * s / 8)) := by
  have hms := mul_le_mul_of_nonneg_left hs hμ.le
  rw [Real.mul_rpow (Real.exp_pos _).le (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [sourceMomentLambda_half]
  unfold jointMidpointMomentRadius theta Lambda0
  norm_num
  nlinarith

theorem jointReverse_envelope_le {C μ s : ℝ} (hμ : 0 < μ) (hs : 4 ≤ s) :
    52 * (4000 * jointPolynomialErrorConstant * jointCommonEnvelope μ s) ^ (1 - theta) *
      jointWeightedIncrementEnvelope C μ s ^ theta ≤ jointReverseBoundConstant C * s ^
        (-gammaRev) := by
  have hs₀ : 0 < s := by linarith
  have hθ := theta_pos_le
  have hA : 0 ≤ jointReverseUnweightedConstant :=
    (mul_pos (by norm_num) jointPolynomialErrorConstant_pos).le
  have ht := (jointWeightedPolynomialBase_pos (1 / 2)).le
  have hB : 0 ≤ jointReverseWeightedConstant C := by unfold jointReverseWeightedConstant; positivity
  have hX : 1 ≤ (1 + μ * s) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hμ.le hs₀.le))
  have hXp : ((1 + μ * s) ^ 2) ^ (1 - theta) ≤ (1 + μ * s) ^ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (show 1 - theta ≤ 1 by linarith)
  have hsp : (1 / s ^ 2) ^ (1 - theta) = s ^ (-gammaRev) := by
    rw [one_div, Real.inv_rpow (sq_nonneg s), ← Real.rpow_natCast_mul hs₀.le,
      ← Real.rpow_neg hs₀.le]
    rfl
  have he := jointReverse_exponential_le hμ hs
  have hx := one_add_sq_mul_exp_neg_le (mul_nonneg hμ.le hs₀.le)
  have hdecay : ((1 + μ * s) ^ 2) ^ (1 - theta) *
      (Real.exp (-μ * s / 2) ^ (1 - theta) *
        (Real.exp (-μ * s / 2) *
          Real.exp (2 * sourceMomentLambda (1 / 2) * μ * jointMidpointMomentRadius s)) ^ theta)
            ≤ 256 :=
    (mul_le_mul hXp he (by positivity) (sq_nonneg _)).trans hx
  have heq :
      (4000 * jointPolynomialErrorConstant * jointCommonEnvelope μ s) ^ (1 - theta) *
        jointWeightedIncrementEnvelope C μ s ^ theta =
      (jointReverseUnweightedConstant ^ (1 - theta) * jointReverseWeightedConstant C ^ theta) *
        s ^ (-gammaRev) * (((1 + μ * s) ^ 2) ^ (1 - theta) *
          (Real.exp (-μ * s / 2) ^ (1 - theta) *
            (Real.exp (-μ * s / 2) *
              Real.exp (2 * sourceMomentLambda (1 / 2) * μ * jointMidpointMomentRadius s)) ^
                theta)) := by
    change (jointReverseUnweightedConstant *
        ((1 / s ^ 2) * (1 + μ * s) ^ 2 * Real.exp (-μ * s / 2))) ^ (1 - theta) *
      ((jointReverseWeightedConstant C * Real.exp (-μ * s / 2)) *
        Real.exp (2 * sourceMomentLambda (1 / 2) * μ * jointMidpointMomentRadius s)) ^ theta = _
    rw [mul_assoc (jointReverseWeightedConstant C),
      Real.mul_rpow hA (by positivity), Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      Real.mul_rpow (by positivity) (sq_nonneg _), Real.mul_rpow hB (by positivity), hsp]
    ring
  calc
    _ = 52 * ((jointReverseUnweightedConstant ^ (1 - theta) * jointReverseWeightedConstant C ^
      theta) *
        s ^ (-gammaRev)) * (((1 + μ * s) ^ 2) ^ (1 - theta) *
          (Real.exp (-μ * s / 2) ^ (1 - theta) *
            (Real.exp (-μ * s / 2) *
              Real.exp (2 * sourceMomentLambda (1 / 2) * μ * jointMidpointMomentRadius s)) ^
                theta)) := by
      rw [mul_assoc 52, heq]
      ring
    _ ≤ 52 * ((jointReverseUnweightedConstant ^ (1 - theta) * jointReverseWeightedConstant C ^
      theta) *
        s ^ (-gammaRev)) * 256 := mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by unfold jointReverseBoundConstant; ring

end VacuumBellSeparation
