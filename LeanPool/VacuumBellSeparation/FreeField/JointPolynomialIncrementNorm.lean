/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialSelfAdjoint
public import LeanPool.VacuumBellSeparation.FreeField.JointRegionMomentFamily

/-! # Actual self-adjoint polynomial increments and their geometric norm bound -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian

/-- Continuous linear map for the joint polynomial increment, of type `SourceHilbert hμ
(jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s)`. -/
def jointPolynomialIncrement {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    SourceHilbert hμ (jointSourceRegion s) →L[ℝ] SourceHilbert hμ (jointSourceRegion s) :=
  jointPolynomialKernelOperator hμ hs (n + 1) - jointPolynomialKernelOperator hμ hs n

theorem jointPolynomialIncrement_eq_errors {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    jointPolynomialIncrement hμ hs n = jointErrorOperator hμ hs n - jointErrorOperator hμ hs
      (n + 1) := by
  unfold jointPolynomialIncrement jointPolynomialKernelOperator
  abel

theorem jointPolynomialIncrement_isSelfAdjoint {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (n : ℕ) :
    IsSelfAdjoint (jointPolynomialIncrement hμ hs n) :=
  (jointPolynomialKernelOperator_isSelfAdjoint hμ hs (jointRegionMomentFamily hμ s) (n + 1)).sub
    (jointPolynomialKernelOperator_isSelfAdjoint hμ hs (jointRegionMomentFamily hμ s) n)

theorem norm_jointPolynomialIncrement_le {μ s : ℝ}
    (hμ : 0 < μ) (hs : 157286400 ≤ s) (n : ℕ) :
    ‖jointPolynomialIncrement hμ (show 600 ≤ s by linarith) n‖ ≤
      2 * jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n := by
  have hs6 : 600 ≤ s := by linarith
  have hs₀ : 0 < s := by linarith
  have hq₀ : 0 ≤ 78643200 / s := by positivity
  have hq₁ : 78643200 / s ≤ 1 := (div_le_one hs₀).mpr (by linarith)
  have hp : (78643200 / s) ^ (n + 1) ≤ (78643200 / s) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hq₀ n) hq₁
  have hC := jointPolynomialErrorConstant_pos.le
  have hE := jointCommonEnvelope_nonneg μ s
  rw [jointPolynomialIncrement_eq_errors]
  calc
    _ ≤ ‖jointErrorOperator hμ hs6 n‖ + ‖jointErrorOperator hμ hs6 (n + 1)‖ :=
      norm_sub_le (jointErrorOperator hμ hs6 n) (jointErrorOperator hμ hs6 (n + 1))
    _ ≤ jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n +
        jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ (n + 1) :=
      add_le_add (norm_jointErrorOperator_le hμ hs6 n) (norm_jointErrorOperator_le hμ hs6 (n + 1))
    _ ≤ jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n +
        jointPolynomialErrorConstant * jointCommonEnvelope μ s * (78643200 / s) ^ n := by gcongr
    _ = _ := by ring

end VacuumBellSeparation
