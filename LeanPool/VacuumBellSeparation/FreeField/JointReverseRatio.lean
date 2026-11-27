/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointReverseEnvelope
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # One universal separation threshold controls the interpolated geometric ratio -/

@[expose] public section

namespace VacuumBellSeparation
open Filter
open scoped Topology

theorem exists_jointReverse_ratio_threshold :
    ∃ S : ℝ, 157286400 ≤ S ∧ ∀ s : ℝ, S ≤ s →
      (78643200 / s) ^ (1 - theta) * jointWeightedPolynomialBase (1 / 2) ^ theta ≤ 1 / 2 := by
  have hu : 0 < 1 - theta := by linarith [theta_pos_le.2]
  have hlim : Tendsto (fun s : ℝ =>
      (78643200 : ℝ) ^ (1 - theta) * s ^ (-(1 - theta)) *
        jointWeightedPolynomialBase (1 / 2) ^ theta) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_rpow_neg_atTop hu).const_mul ((78643200 : ℝ) ^ (1 - theta))).mul_const
        (jointWeightedPolynomialBase (1 / 2) ^ theta)
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨max 157286400 S, le_max_left _ _, ?_⟩
  intro s hs
  have hs₀ : 0 < s := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hs)
  rw [Real.div_rpow (by norm_num) hs₀.le, div_eq_mul_inv, ← Real.rpow_neg hs₀.le]
  exact hS s ((le_max_right _ _).trans hs)

end VacuumBellSeparation
