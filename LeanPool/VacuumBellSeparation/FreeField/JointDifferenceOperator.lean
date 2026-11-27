/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointDifferenceOperatorDefs
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialErrorOperators
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialEnvelope

/-!
# A genuine joint kernel operator and its norm-convergent polynomial approximants

The order-zero error has zero Taylor polynomial, and supplies the bounded
joint kernel operator. Subtracting the order-n error gives its approximant.
Identification with finite moment sums and the product-minus-joint test
covariance is recorded separately; neither identification is a hypothesis here.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Filter
open scoped Topology

theorem jointPolynomialErrorConstant_pos : 0 < jointPolynomialErrorConstant := by
  unfold jointPolynomialErrorConstant
  exact mul_pos (mul_pos (mul_pos (by norm_num) jointSmoothKernelUniversalConstant_pos)
    (by norm_num)) (by norm_num)

@[simp] theorem jointPolynomialKernelOperator_zero {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) : jointPolynomialKernelOperator hμ hs 0 = 0 := by
  simp only [jointPolynomialKernelOperator, jointDifferenceKernelOperator, sub_self]

theorem norm_jointErrorOperator_le {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    ‖jointErrorOperator hμ hs n‖ ≤
      jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n := by
  have hs₀ : 0 < s := by linarith
  have hC := jointSmoothKernelUniversalConstant_pos.le
  have hq : 0 ≤ (78643200 / s) ^ n := by positivity
  have henv : max 1 μ * jointFieldEnvelope μ s + jointMomentumEnvelope μ s ≤
      134 * jointCommonEnvelope μ s := by
    linarith [jointFieldEnvelope_mass_le hμ (show 1 ≤ s by linarith),
      jointMomentumEnvelope_le hμ (show 1 ≤ s by linarith)]
  calc
    _ ≤ ‖jointFieldErrorOperator hμ hs n‖ + ‖jointMomentumErrorOperator hμ hs n‖ := by
      simpa only [jointErrorOperator] using
        norm_add_le (jointFieldErrorOperator hμ hs n) (jointMomentumErrorOperator hμ hs n)
    _ ≤ (4 * jointSmoothKernelUniversalConstant) * max 1 μ *
          (11680000 * jointFieldEnvelope μ s * (78643200 / s) ^ n) +
        (4 * jointSmoothKernelUniversalConstant) *
          (11680000 * jointMomentumEnvelope μ s * (78643200 / s) ^ n) :=
      add_le_add (norm_jointFieldErrorOperator_le hμ hs n)
        (norm_jointMomentumErrorOperator_le hμ hs n)
    _ = (4 * jointSmoothKernelUniversalConstant * 11680000) *
        (max 1 μ * jointFieldEnvelope μ s + jointMomentumEnvelope μ s) * (78643200 / s) ^ n
          := by ring
    _ ≤ (4 * jointSmoothKernelUniversalConstant * 11680000) *
        (134 * jointCommonEnvelope μ s) * (78643200 / s) ^ n := by gcongr
    _ = _ := by unfold jointPolynomialErrorConstant; ring

theorem norm_jointDifferenceKernelOperator_le {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) :
    ‖jointDifferenceKernelOperator hμ hs‖ ≤ jointPolynomialErrorConstant * jointCommonEnvelope μ
      s := by
  simpa only [jointDifferenceKernelOperator, pow_zero, mul_one]
    using norm_jointErrorOperator_le hμ hs 0

theorem norm_jointPolynomialKernelOperator_error_le {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    ‖jointDifferenceKernelOperator hμ hs - jointPolynomialKernelOperator hμ hs n‖ ≤
      jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n := by
  simpa only [jointPolynomialKernelOperator, sub_sub_cancel]
    using norm_jointErrorOperator_le hμ hs n

theorem jointPolynomialKernelOperator_tendsto {μ s : ℝ}
    (hμ : 0 < μ) (hs : 157286400 ≤ s) :
    Tendsto (jointPolynomialKernelOperator hμ (show 600 ≤ s by linarith)) atTop
      (𝓝 (jointDifferenceKernelOperator hμ (show 600 ≤ s by linarith))) := by
  have hs₀ : 0 < s := by linarith
  have hq₀ : 0 ≤ 78643200 / s := by positivity
  have hq₁ : 78643200 / s < 1 := (div_lt_one hs₀).mpr (by linarith)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  have hn : Tendsto (fun n => ‖jointErrorOperator hμ (show 600 ≤ s by linarith) n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg
      (jointErrorOperator hμ (show 600 ≤ s by linarith) n)) (norm_jointErrorOperator_le hμ _)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds (x := jointPolynomialErrorConstant * jointCommonEnvelope μ s)).mul hp)
  have he : Tendsto (jointErrorOperator hμ (show 600 ≤ s by linarith))
      atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero
      (f := jointErrorOperator hμ (show 600 ≤ s by linarith)) (a := atTop)).mpr hn
  change Tendsto (fun n => jointDifferenceKernelOperator hμ (show 600 ≤ s by linarith) -
    jointErrorOperator hμ (show 600 ≤ s by linarith) n) atTop
    (𝓝 (jointDifferenceKernelOperator hμ (show 600 ≤ s by linarith)))
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := jointDifferenceKernelOperator hμ (show 600 ≤ s by linarith))).sub he

end VacuumBellSeparation
