/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceFourierBounds

/-!
# The literal energy choice and dimensional moment prefactors
-/

@[expose] public section

namespace VacuumBellSeparation

theorem sourceMomentLambda_pos {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    0 < sourceMomentLambda b := by
  rw [sourceMomentLambda_eq]
  exact mul_pos (by norm_num) (sourceEvaluationRate_pos hb hb1)

theorem one_le_sourceMomentLambda {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    1 ≤ sourceMomentLambda b := by
  have hs : 0 < Real.sin (Real.pi * b) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (by linarith))
      (by nlinarith [Real.pi_pos])
  unfold sourceMomentLambda
  apply (le_div_iff₀ hs).mpr
  nlinarith [Real.sin_le_one (Real.pi * b)]

/-- Source moment energy given by `m + 1 / (sourceMomentLambda b * T) + ‖z‖`. -/
noncomputable def sourceMomentEnergy (m T b : ℝ) (z : EuclideanSpace ℂ (Fin 3)) : ℝ :=
  m + 1 / (sourceMomentLambda b * T) + ‖z‖

theorem sourceMomentEnergy_lower {b m T : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (hT : 0 < T) (z : EuclideanSpace ℂ (Fin 3)) :
    m + ‖z‖ ≤ sourceMomentEnergy m T b z := by
  have hΛ := sourceMomentLambda_pos hb hb1
  have hp : 0 < 1 / (sourceMomentLambda b * T) := by positivity
  unfold sourceMomentEnergy
  linarith

theorem sourceMomentEnergy_pos {b m T : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (hm : 0 < m) (hT : 0 < T) (z : EuclideanSpace ℂ (Fin 3)) :
    0 < sourceMomentEnergy m T b z := by
  have h := sourceMomentEnergy_lower (m := m) hb hb1 hT z
  linarith [norm_nonneg z]

theorem sourceMomentEnergy_exponent {b m T : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (hT : 0 < T) (z : EuclideanSpace ℂ (Fin 3)) :
    sourceMomentLambda b * T * sourceMomentEnergy m T b z =
      sourceMomentLambda b * m * T + 1 + sourceMomentLambda b * T * ‖z‖ := by
  have hn : sourceMomentLambda b * T ≠ 0 := (mul_pos (sourceMomentLambda_pos hb hb1) hT).ne'
  unfold sourceMomentEnergy
  field_simp [hn, (sourceMomentLambda_pos hb hb1).ne', hT.ne']

theorem sourceMomentEnergy_inv_le {b m T : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (hm : 0 < m) (hT : 0 < T) (z : EuclideanSpace ℂ (Fin 3)) :
    1 / sourceMomentEnergy m T b z ≤ sourceMomentLambda b * T / (1 + m * T) := by
  have hE := sourceMomentEnergy_pos hb hb1 hm hT z
  have hd : 0 < 1 + m * T := by positivity
  apply (div_le_div_iff₀ hE hd).mpr
  have he := sourceMomentEnergy_exponent (m := m) hb hb1 hT z
  have hΛ := one_le_sourceMomentLambda hb hb1
  have hΛpos := sourceMomentLambda_pos hb hb1
  have hmT := mul_le_mul_of_nonneg_right hΛ (show 0 ≤ m * T by positivity)
  have hsp : 0 ≤ sourceMomentLambda b * T * ‖z‖ := by positivity
  nlinarith

end VacuumBellSeparation
