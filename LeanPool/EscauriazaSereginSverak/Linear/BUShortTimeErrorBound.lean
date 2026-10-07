/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTimeDerivative

/-!
# Separating the lower-time error

The cutoff error consists of the error for the fixed spatial-phase cutoff,
multiplied by a bounded time factor, and one term of size `8/ε`.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Sum of absolute spatial derivatives of the cutoff without its
lower-time factor. -/
@[expose] def buShortSpacePhaseGradientSize (scale R : ℝ) (hR : 0 < R)
    (z : ParabolicPoint) : ℝ :=
  ∑ j : Fin 3,
    |spatialPartial (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j z|

/-- Absolute scalar heat derivative of the cutoff without its
lower-time factor. -/
@[expose] def buShortSpacePhaseHeatSize (scale R : ℝ) (hR : 0 < R)
    (z : ParabolicPoint) : ℝ :=
  |timePartial (buCutScalar (buShortSpacePhaseCutoff scale R hR)) z +
    ∑ j : Fin 3,
      spatialSecondPartial (buCutScalar (buShortSpacePhaseCutoff scale R hR))
        j j z|

/-- The two-factor cutoff takes values in the unit interval. -/
theorem buShortSpacePhaseCutoff_bounds
    (scale R : ℝ) (hR : 0 < R) (q : Vec3 × ℝ) :
    0 ≤ buShortSpacePhaseCutoff scale R hR q ∧
      buShortSpacePhaseCutoff scale R hR q ≤ 1 := by
  obtain ⟨hχ0, hχ1⟩ :=
    ucSpatialCutoff_bounds (show 0 < 2 * R by positivity) q.1
  obtain ⟨hη0, hη1⟩ := buShortEtaExt_bounds scale q
  dsimp [buShortSpacePhaseCutoff]
  exact ⟨mul_nonneg hχ0 hη0,
    (mul_le_mul_of_nonneg_right hχ1 hη0).trans (by simpa using hη1)⟩

/-- Spatial derivative size of the full cutoff is bounded by that of
the two-factor cutoff. -/
theorem buShortCutoffGradientSize_le_spacePhase
    (scale R ε : ℝ) (hR : 0 < R) (z : ParabolicPoint) :
    buShortCutoffGradientSize scale R hR ε z ≤
      buShortSpacePhaseGradientSize scale R hR z := by
  have hθ := ucInitialTimeCutoff_bounds ε (z.2 - 1 / 2)
  have hθ0 : 0 ≤ buShortTimeCutoff ε z.2 := hθ.1
  have hθ1 : buShortTimeCutoff ε z.2 ≤ 1 := hθ.2
  unfold buShortCutoffGradientSize buShortSpacePhaseGradientSize
  apply Finset.sum_le_sum
  intro j _
  rw [buShortFullCutoff_spatialPartial_time_factor]
  rw [abs_mul, abs_of_nonneg hθ0]
  exact mul_le_of_le_one_right (abs_nonneg _) hθ1

end ESS
