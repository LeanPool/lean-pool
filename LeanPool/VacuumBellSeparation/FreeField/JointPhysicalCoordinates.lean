/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.JointComponentGeometry
public import Mathlib.Analysis.Analytic.Polynomial

/-! # Literal physical centres and midpoint normalization of all six coordinates -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Metric

/-- Joint physical midpoint shift defined as `if j = 0 ∨ j = 3 then 1 / 2 else 0`. -/
def jointPhysicalMidpointShift (j : Fin 6) : ℂ :=
  if j = 0 ∨ j = 3 then 1 / 2 else 0

/-- Joint physical midpoint defined as `w j / (s : ℂ) - jointPhysicalMidpointShift j`. -/
def jointPhysicalMidpoint (s : ℝ) (w : Fin 6 → ℂ) (j : Fin 6) : ℂ :=
  w j / (s : ℂ) - jointPhysicalMidpointShift j

/-- The original spatial center corresponding to a normalized joint component. -/
def jointPhysicalComponentCenter (a b : Bool) (s : ℝ) (j : Fin 6) : ℂ :=
  (s : ℂ) * (jointComponentCenter a b j + jointPhysicalMidpointShift j)

/-- These are exactly the original centres zero and s times the first basis vector. -/
theorem jointPhysicalComponentCenter_eq (a b : Bool) (s : ℝ) (j : Fin 6) :
    jointPhysicalComponentCenter a b s j =
      if j = 0 then (if a then (s : ℂ) else 0)
      else if j = 3 then (if b then (s : ℂ) else 0) else 0 := by
  fin_cases j <;> cases a <;> cases b <;>
    simp [jointPhysicalComponentCenter, jointComponentCenter, jointPhysicalMidpointShift] <;> ring

/-- In physical joint component. -/
def InPhysicalJointComponent (a b : Bool) (s r : ℝ) (w : Fin 6 → ℂ) : Prop :=
  ∀ j, ‖w j - jointPhysicalComponentCenter a b s j‖ ≤ r

theorem physicalMidpoint_sub_center {s : ℝ} (hs : 0 < s)
    (a b : Bool) (w : Fin 6 → ℂ) (j : Fin 6) :
    jointPhysicalMidpoint s w j - jointComponentCenter a b j =
      (w j - jointPhysicalComponentCenter a b s j) / (s : ℂ) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  unfold jointPhysicalMidpoint jointPhysicalComponentCenter
  field_simp; ring

theorem InPhysicalJointComponent.normalize {a b : Bool} {s r : ℝ} (hs : 0 < s)
    {w : Fin 6 → ℂ} (hw : InPhysicalJointComponent a b s r w) :
    InJointComponent a b (r / s) (jointPhysicalMidpoint s w) := by
  intro j
  rw [physicalMidpoint_sub_center hs, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
  exact div_le_div_of_nonneg_right (hw j) hs.le

theorem InPhysicalJointComponent.ball_one {a b : Bool} {s : ℝ} {w : Fin 6 → ℂ}
    (hw : InPhysicalJointComponent a b s 2 w) {y : Fin 6 → ℂ} (hy : y ∈ ball w 1) :
    InPhysicalJointComponent a b s 3 y := by
  have hn : ‖y - w‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hy
  intro j
  have hcoord : ‖y j - w j‖ ≤ ‖y - w‖ := norm_le_pi_norm (y - w) j
  calc
    _ = ‖(y j - w j) + (w j - jointPhysicalComponentCenter a b s j)‖ := by congr 1; ring
    _ ≤ ‖y j - w j‖ + ‖w j - jointPhysicalComponentCenter a b s j‖ := norm_add_le _ _
    _ ≤ 3 := by linarith [hw j]

theorem jointPhysicalMidpoint_analyticAt (s : ℝ) (w : Fin 6 → ℂ) :
    AnalyticAt ℂ (jointPhysicalMidpoint s) w := by
  apply AnalyticAt.pi
  intro j
  simpa only [jointPhysicalMidpoint, div_eq_mul_inv, Pi.mul_def, Pi.sub_def,
    ContinuousLinearMap.proj_apply] using
    ((((ContinuousLinearMap.proj j : (Fin 6 → ℂ) →L[ℂ] ℂ).analyticAt w).mul
      analyticAt_const).sub analyticAt_const)

end VacuumBellSeparation
