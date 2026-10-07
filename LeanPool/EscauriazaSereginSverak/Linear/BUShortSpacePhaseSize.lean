/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSpacePhaseBounds
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTimeErrorBound

/-!
# Scalar derivative sizes of the two-factor cutoff

The gradient and heat sizes are bounded by a phase polynomial and
inverse-radius shell terms.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The sum of absolute spatial derivatives separates the spatial shell
from the normal-phase growth. -/
theorem buShortSpacePhaseGradientSize_bound
    {scale R : ℝ} (hscale : 0 < scale) (hR : 0 < R)
    {z : ParabolicPoint} (hy : 2 < z.1 2)
    (hs : 1 / 2 ≤ z.2) (hs1 : z.2 ≤ 1) :
    buShortSpacePhaseGradientSize scale R hR z ≤
      3 * (cutoffGradientConstant / (2 * R) +
        (16 + 48 * (12 / buShortB scale)) * (1 + z.1 2)) := by
  unfold buShortSpacePhaseGradientSize
  calc
    _ ≤ ∑ _j : Fin 3,
        (cutoffGradientConstant / (2 * R) +
          (16 + 48 * (12 / buShortB scale)) * (1 + z.1 2)) := by
      apply Finset.sum_le_sum
      intro j _
      exact buShortSpacePhase_spatialPartial_bound
        hscale hR hy hs hs1 j
    _ = _ := by simp; ring

/-- The absolute scalar heat derivative separates the spatial shell
from quadratic normal-phase growth. -/
theorem buShortSpacePhaseHeatSize_bound
    {scale R C₁ C₂ : ℝ} (hscale : 0 < scale) (hR : 0 < R)
    {z : ParabolicPoint} (hy : 2 < z.1 2)
    (hs : 1 / 2 < z.2) (hs1 : z.2 ≤ 1)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂) :
    buShortSpacePhaseHeatSize scale R hR z ≤
      (56 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2 +
      3 * (cutoffSecondDerivativeConstant / (2 * R) ^ 2 +
        2 * (cutoffGradientConstant / (2 * R)) *
          ((16 + 48 * (12 / buShortB scale)) * (1 + z.1 2)) +
        (C₁ + 1536 * (12 / buShortB scale) +
          36 * C₂ * (12 / buShortB scale) ^ 2 +
          24 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2) := by
  let T := (56 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2
  let S := cutoffSecondDerivativeConstant / (2 * R) ^ 2 +
      2 * (cutoffGradientConstant / (2 * R)) *
        ((16 + 48 * (12 / buShortB scale)) * (1 + z.1 2)) +
      (C₁ + 1536 * (12 / buShortB scale) +
        36 * C₂ * (12 / buShortB scale) ^ 2 +
        24 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2
  have htime := buShortSpacePhase_timePartial_bound hscale hR hy hs hs1
  have hsum :
      (∑ j : Fin 3,
        |spatialSecondPartial
          (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j j z|) ≤
        3 * S := by
    calc
      _ ≤ ∑ _j : Fin 3, S := by
        apply Finset.sum_le_sum
        intro j _
        exact buShortSpacePhase_spatialSecondPartial_diag_bound
          hscale hR hy hs.le hs1 hC₁ hN hC₂ hP j
      _ = 3 * S := by simp
  unfold buShortSpacePhaseHeatSize
  calc
    _ ≤ |timePartial
        (buCutScalar (buShortSpacePhaseCutoff scale R hR)) z| +
        |∑ j : Fin 3,
          spatialSecondPartial
            (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j j z| :=
      abs_add_le _ _
    _ ≤ |timePartial
        (buCutScalar (buShortSpacePhaseCutoff scale R hR)) z| +
        ∑ j : Fin 3,
          |spatialSecondPartial
            (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j j z| :=
      add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ T + 3 * S := add_le_add htime hsum

end ESS
