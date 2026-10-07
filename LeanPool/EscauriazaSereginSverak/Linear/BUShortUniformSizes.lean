/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUniformCoefficients

/-!
# Uniform polynomial bounds for cutoff derivative sizes

For radii at least one, the derivative sizes are controlled by fixed
coefficients times the square of one plus the normal height.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A radius-independent coefficient for the sum of spatial cutoff
derivatives. -/
@[expose] def buShortUniformGradientCoeff (scale : ℝ) : ℝ :=
  3 * (cutoffGradientConstant + 16 + 48 * (12 / buShortB scale))

/-- A radius-independent coefficient for the scalar heat derivative. -/
@[expose] def buShortUniformHeatCoeff (scale C₁ C₂ : ℝ) : ℝ :=
  56 * (12 / buShortB scale) +
    3 * (cutoffSecondDerivativeConstant +
      2 * cutoffGradientConstant *
        (16 + 48 * (12 / buShortB scale)) +
      C₁ + 1536 * (12 / buShortB scale) +
      36 * C₂ * (12 / buShortB scale) ^ 2 +
      24 * (12 / buShortB scale))

/-- The gradient size of the spatial-phase cutoff has a quadratic
height bound uniform over spatial radii at least one. -/
theorem buShortSpacePhaseGradientSize_uniform
    {scale R : ℝ} (hscale : 0 < scale) (hR : 1 ≤ R)
    {z : ParabolicPoint} (hy : 2 < z.1 2)
    (hs : 1 / 2 ≤ z.2) (hs1 : z.2 ≤ 1) :
    buShortSpacePhaseGradientSize scale R (by linarith only [hR]) z ≤
      buShortUniformGradientCoeff scale * (1 + z.1 2) ^ 2 := by
  let K := 12 / buShortB scale
  let P := 1 + z.1 2
  have hK : 0 ≤ K := (div_pos (by norm_num) (buShortB_pos hscale)).le
  have hG : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hP : 1 ≤ P := by dsimp [P]; linarith only [hy]
  have hP2 : 1 ≤ P ^ 2 := by nlinarith only [hP]
  have hPLe : P ≤ P ^ 2 := by nlinarith only [hP]
  have hR0 : 0 < R := by linarith only [hR]
  have hbase := buShortSpacePhaseGradientSize_bound
    hscale hR0 hy hs hs1
  have hratio := buShort_cutoff_gradient_ratio_le hR
  have hcoef : 0 ≤ 16 + 48 * K := by positivity
  have hstep :
      cutoffGradientConstant / (2 * R) +
        (16 + 48 * K) * P ≤
      (cutoffGradientConstant + 16 + 48 * K) * P ^ 2 := by
    have h₁ := (mul_le_mul_of_nonneg_left hP2 hG)
    have h₂ := (mul_le_mul_of_nonneg_left hPLe hcoef)
    nlinarith only [hratio, h₁, h₂]
  change buShortSpacePhaseGradientSize scale R hR0 z ≤
    3 * (cutoffGradientConstant + 16 + 48 * K) * P ^ 2
  calc
    _ ≤ 3 * (cutoffGradientConstant / (2 * R) +
        (16 + 48 * K) * P) := hbase
    _ ≤ 3 * ((cutoffGradientConstant + 16 + 48 * K) * P ^ 2) := by
      gcongr
    _ = _ := by ring

/-- The scalar heat size of the spatial-phase cutoff has a quadratic
height bound uniform over spatial radii at least one. -/
theorem buShortSpacePhaseHeatSize_uniform
    {scale R C₁ C₂ : ℝ} (hscale : 0 < scale) (hR : 1 ≤ R)
    {z : ParabolicPoint} (hy : 2 < z.1 2)
    (hs : 1 / 2 < z.2) (hs1 : z.2 ≤ 1)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂) :
    buShortSpacePhaseHeatSize scale R (by linarith only [hR]) z ≤
      buShortUniformHeatCoeff scale C₁ C₂ * (1 + z.1 2) ^ 2 := by
  let K := 12 / buShortB scale
  let P := 1 + z.1 2
  let E₁ := 16 + 48 * K
  let E₂ := C₁ + 1536 * K + 36 * C₂ * K ^ 2 + 24 * K
  have hK : 0 ≤ K := (div_pos (by norm_num) (buShortB_pos hscale)).le
  have hG : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hS : 0 ≤ cutoffSecondDerivativeConstant :=
    CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hP0 : 0 ≤ P := by dsimp [P]; linarith only [hy]
  have hP1 : 1 ≤ P := by dsimp [P]; linarith only [hy]
  have hP2 : 1 ≤ P ^ 2 := by nlinarith only [hP1]
  have hPLe : P ≤ P ^ 2 := by nlinarith only [hP1]
  have hR0 : 0 < R := by linarith only [hR]
  have hbase := buShortSpacePhaseHeatSize_bound
    hscale hR0 hy hs hs1 hC₁ hN hC₂ hP
  have hratio₁ := buShort_cutoff_gradient_ratio_le hR
  have hratio₂ := buShort_cutoff_second_ratio_le hR
  have hcross :
      2 * (cutoffGradientConstant / (2 * R)) * (E₁ * P) ≤
        2 * cutoffGradientConstant * E₁ * P ^ 2 := by
    calc
      2 * (cutoffGradientConstant / (2 * R)) * (E₁ * P) ≤
          2 * cutoffGradientConstant * (E₁ * P) := by
        gcongr
      _ = (2 * cutoffGradientConstant * E₁) * P := by ring
      _ ≤ (2 * cutoffGradientConstant * E₁) * P ^ 2 := by gcongr
      _ = _ := by ring
  have hshell :
      cutoffSecondDerivativeConstant / (2 * R) ^ 2 +
        2 * (cutoffGradientConstant / (2 * R)) * (E₁ * P) +
        E₂ * P ^ 2 ≤
      (cutoffSecondDerivativeConstant +
        2 * cutoffGradientConstant * E₁ + E₂) * P ^ 2 := by
    have hSsq := mul_le_mul_of_nonneg_left hP2 hS
    nlinarith only [hratio₂, hSsq, hcross]
  calc
    _ ≤ (56 * K) * P ^ 2 +
        3 * (cutoffSecondDerivativeConstant / (2 * R) ^ 2 +
          2 * (cutoffGradientConstant / (2 * R)) * (E₁ * P) +
          E₂ * P ^ 2) := hbase
    _ ≤ (56 * K) * P ^ 2 +
        3 * ((cutoffSecondDerivativeConstant +
          2 * cutoffGradientConstant * E₁ + E₂) * P ^ 2) := by
      gcongr
    _ = (56 * K + 3 *
      (cutoffSecondDerivativeConstant +
        2 * cutoffGradientConstant * E₁ + E₂)) * P ^ 2 := by ring
    _ = buShortUniformHeatCoeff scale C₁ C₂ *
        (1 + z.1 2) ^ 2 := by
      dsimp [buShortUniformHeatCoeff, E₁, E₂, K, P]
      ring

end ESS
