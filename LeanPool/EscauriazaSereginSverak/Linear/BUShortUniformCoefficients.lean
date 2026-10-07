/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShellError
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic

/-!
# Radius-independent cutoff coefficients

For spatial radii at least one, the shell derivative constants are
bounded independently of the radius.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The spatial cutoff gradient bound at radius at least one is no
larger than its fixed cutoff constant. -/
theorem buShort_cutoff_gradient_ratio_le
    {R : ℝ} (hR : 1 ≤ R) :
    cutoffGradientConstant / (2 * R) ≤ cutoffGradientConstant := by
  have hG : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hden : 0 < 2 * R := by linarith only [hR]
  have hden1 : 1 ≤ 2 * R := by linarith only [hR]
  apply (div_le_iff₀ hden).2
  have h := mul_le_mul_of_nonneg_left hden1 hG
  nlinarith only [h]

/-- The spatial cutoff Hessian bound at radius at least one is no
larger than its fixed cutoff constant. -/
theorem buShort_cutoff_second_ratio_le
    {R : ℝ} (hR : 1 ≤ R) :
    cutoffSecondDerivativeConstant / (2 * R) ^ 2 ≤
      cutoffSecondDerivativeConstant := by
  have hS : 0 ≤ cutoffSecondDerivativeConstant :=
    CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  have hden : 0 < (2 * R) ^ 2 := by positivity
  have hden1 : 1 ≤ (2 * R) ^ 2 := by nlinarith only [hR]
  apply (div_le_iff₀ hden).2
  have h := mul_le_mul_of_nonneg_left hden1 hS
  nlinarith only [h]

end ESS
