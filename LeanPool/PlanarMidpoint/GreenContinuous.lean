/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import LeanPool.PlanarMidpoint.GreenOperator
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum

/-! The Dirichlet solution operator on continuous acceleration paths. -/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace PlanarMidpoint

/-- The compact real parameter interval `[0, 1]`. -/
abbrev UnitInterval := Icc (0 : ℝ) 1
/-- Continuous planar acceleration paths on the unit interval. -/
abbrev AccelerationPath := C(UnitInterval, E)
/-- Continuous position-velocity paths on the unit interval. -/
abbrev PhasePath := C(UnitInterval, E × E)

/-- Extension of an acceleration path by clamping the parameter to the unit interval. -/
def pathExtend (f : AccelerationPath) (t : ℝ) : E :=
  f (projIcc 0 1 (by norm_num) t)

theorem continuous_pathExtend (f : AccelerationPath) : Continuous (pathExtend f) :=
  f.continuous.comp continuous_projIcc

theorem pathExtend_mem (f : AccelerationPath) (t : ℝ) (ht : t ∈ UnitInterval) :
    pathExtend f t = f ⟨t, ht⟩ := by simp [pathExtend, projIcc_of_mem, ht]

/-- The integral of an extended acceleration path from zero to the given time. -/
def pathPrimitive (f : AccelerationPath) (t : ℝ) : E := ∫ s in (0 : ℝ)..t, pathExtend f s

theorem hasDerivAt_pathPrimitive (f : AccelerationPath) (t : ℝ) :
    HasDerivAt (pathPrimitive f) (pathExtend f t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_pathExtend f).intervalIntegrable _ _)
    (continuous_pathExtend f).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_pathExtend f).continuousAt

theorem continuous_pathPrimitive (f : AccelerationPath) : Continuous (pathPrimitive f) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_pathPrimitive f t).continuousAt

/-- The second primitive of an extended acceleration path. -/
def pathSecondPrimitive (f : AccelerationPath) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, pathPrimitive f s

theorem hasDerivAt_pathSecondPrimitive (f : AccelerationPath) (t : ℝ) :
    HasDerivAt (pathSecondPrimitive f) (pathPrimitive f t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_pathPrimitive f).intervalIntegrable _ _)
    (continuous_pathPrimitive f).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_pathPrimitive f).continuousAt

/-- The second primitive with its endpoint chord removed. -/
def greenPosition (f : AccelerationPath) (t : ℝ) : E :=
  pathSecondPrimitive f t - t • pathSecondPrimitive f 1

/-- The first primitive minus the endpoint correction. -/
def greenVelocity (f : AccelerationPath) (t : ℝ) : E :=
  pathPrimitive f t - pathSecondPrimitive f 1

theorem hasDerivAt_greenPosition (f : AccelerationPath) (t : ℝ) :
    HasDerivAt (greenPosition f) (greenVelocity f t) t := by
  convert! (hasDerivAt_pathSecondPrimitive f t).fun_sub
    ((hasDerivAt_id t).smul_const (pathSecondPrimitive f 1)) using 1
  simp [greenVelocity]

theorem hasDerivAt_greenVelocity (f : AccelerationPath) (t : ℝ) :
    HasDerivAt (greenVelocity f) (pathExtend f t) t :=
  (hasDerivAt_pathPrimitive f t).sub_const _

@[simp] theorem greenPosition_zero (f : AccelerationPath) : greenPosition f 0 = 0 := by
  simp [greenPosition, pathSecondPrimitive]

@[simp] theorem greenPosition_one (f : AccelerationPath) : greenPosition f 1 = 0 := by
  simp [greenPosition]

/-- The position-velocity path solving the zero-endpoint Dirichlet problem. -/
def greenPath (f : AccelerationPath) : PhasePath :=
  ⟨fun t => (greenPosition f t, greenVelocity f t),
    ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_greenPosition f t).continuousAt).prodMk
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_greenVelocity f t).continuousAt)).comp
      continuous_subtype_val⟩

theorem norm_greenPath_le (f : AccelerationPath) : ‖greenPath f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  change max ‖greenPosition f t‖ ‖greenVelocity f t‖ ≤ ‖f‖
  apply max_le
  · exact dirichlet_position_bound (greenPosition f) (greenVelocity f) (pathExtend f) ‖f‖
      (fun t _ => hasDerivAt_greenPosition f t) (fun t _ => hasDerivAt_greenVelocity f t)
      (fun t ht => by rw [pathExtend_mem f t ht]; exact f.norm_coe_le_norm _)
      (greenPosition_zero f) (greenPosition_one f) t t.property
  · exact dirichlet_velocity_bound (greenPosition f) (greenVelocity f) (pathExtend f) ‖f‖
      (fun t _ => hasDerivAt_greenPosition f t) (fun t _ => hasDerivAt_greenVelocity f t)
      (fun t ht => by rw [pathExtend_mem f t ht]; exact f.norm_coe_le_norm _)
      (greenPosition_zero f) (greenPosition_one f) t t.property

theorem pathPrimitive_add (f g : AccelerationPath) (t : ℝ) :
    pathPrimitive (f + g) t = pathPrimitive f t + pathPrimitive g t := by
  exact intervalIntegral.integral_add
    ((continuous_pathExtend f).intervalIntegrable _ _) ((continuous_pathExtend
        g).intervalIntegrable _ _)

theorem pathPrimitive_smul (r : ℝ) (f : AccelerationPath) (t : ℝ) :
    pathPrimitive (r • f) t = r • pathPrimitive f t := by
  exact intervalIntegral.integral_smul r _

theorem pathSecondPrimitive_add (f g : AccelerationPath) (t : ℝ) :
    pathSecondPrimitive (f + g) t = pathSecondPrimitive f t + pathSecondPrimitive g t := by
  simp only [pathSecondPrimitive, pathPrimitive_add]
  exact intervalIntegral.integral_add
    ((continuous_pathPrimitive f).intervalIntegrable _ _) ((continuous_pathPrimitive
        g).intervalIntegrable _ _)

theorem pathSecondPrimitive_smul (r : ℝ) (f : AccelerationPath) (t : ℝ) :
    pathSecondPrimitive (r • f) t = r • pathSecondPrimitive f t := by
  simp only [pathSecondPrimitive, pathPrimitive_smul, intervalIntegral.integral_smul]

/-- Linearity of the Dirichlet Green construction on continuous acceleration paths. -/
def greenLinear : AccelerationPath →ₗ[ℝ] PhasePath where
  toFun := greenPath
  map_add' f g := by
    ext t : 1
    apply Prod.ext <;> simp [greenPath, greenPosition, greenVelocity,
      pathPrimitive_add, pathSecondPrimitive_add] <;> module
  map_smul' r f := by
    ext t : 1
    apply Prod.ext <;> simp [greenPath, greenPosition, greenVelocity,
      pathPrimitive_smul, pathSecondPrimitive_smul] <;> module

/-- The bounded Dirichlet Green operator, with operator norm at most one. -/
def greenOperator : AccelerationPath →L[ℝ] PhasePath :=
  greenLinear.mkContinuous 1 (fun f => by
    change ‖greenPath f‖ ≤ 1 * ‖f‖
    simpa using norm_greenPath_le f)

@[simp] theorem greenOperator_apply (f : AccelerationPath) (t : UnitInterval) :
    greenOperator f t = (greenPosition f t, greenVelocity f t) := rfl

theorem norm_greenOperator_le : ‖greenOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖greenPath f‖ ≤ 1 * ‖f‖
  simpa using norm_greenPath_le f

end PlanarMidpoint
