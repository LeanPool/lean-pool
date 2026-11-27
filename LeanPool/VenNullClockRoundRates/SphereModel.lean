/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt imports and omit the separate finite-menu interface. -/

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Coordinate-fixed pair of axes in the physical round generator sphere:
first axis (1, 0, 0), second (cos θ, sin θ, 0). The measure may be the normalized
area law. The conclusion concerns scalar exponential reads, not a PDE. -/
@[expose] public section
noncomputable section
namespace VenMask
/-- The Cartesian unit sphere used by the scalar observation model. -/
def UnitSphere := {q : ℝ × ℝ × ℝ // q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1}
deriving instance TopologicalSpace, MeasurableSpace for UnitSphere

/-- Quadrupole energy as a function of the coordinate along the axis. -/
def energy (u : ℝ) : ℝ := (1 - u ^ 2) ^ 2

/-- Energy for the first axis, aligned with the first Cartesian coordinate. -/
def firstEnergy (y : UnitSphere) : ℝ := energy y.val.1

/-- Energy for the second axis rotated in the first two coordinates by `θ`. -/
def secondEnergy (θ : ℝ) (y : UnitSphere) : ℝ :=
  energy (Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1)

end VenMask
