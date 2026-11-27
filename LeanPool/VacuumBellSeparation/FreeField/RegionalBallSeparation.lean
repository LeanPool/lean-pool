/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialKernelTaylorReal

/-! Separation of the actual unit balls used by both regional estimates. -/

@[expose] public section

namespace VacuumBellSeparation

open Metric

theorem regionalForward_unit_balls_disjoint {s : ℝ} (hs : 2 ≤ s) :
    Disjoint (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (ball (spatialAxisDisplacement s 0) 1) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  have hy' : ‖x - spatialAxisDisplacement s 0‖ < 1 := by
    simpa only [mem_ball, dist_eq_norm] using hy
  have h0 := lt_of_le_of_lt (PiLp.norm_apply_le x (0 : Fin 3)) hx'
  have h1 := lt_of_le_of_lt
    (PiLp.norm_apply_le (x - spatialAxisDisplacement s 0) (0 : Fin 3)) hy'
  simp only [Real.norm_eq_abs] at h0
  simp only [Real.norm_eq_abs, PiLp.sub_apply, spatialAxisDisplacement,
    PiLp.coe_symm_continuousLinearEquiv, PiLp.zero_apply, ite_true, add_zero] at h1
  have ha := (abs_lt.mp h0).2
  have hb := (abs_lt.mp h1).1
  linarith

end VacuumBellSeparation
