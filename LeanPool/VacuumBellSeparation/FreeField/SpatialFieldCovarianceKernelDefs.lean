/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Special.BesselKDefs
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDefs

/-!
# Statement seed extracted from FreeField/SpatialFieldCovarianceKernel

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ComplexConjugate

/-- Spatial field Bessel kernel given by `m / (4 * Real.pi ^ 2 * ‖w‖) * besselKReal 1 (m * ‖w‖)`. -/
noncomputable def spatialFieldBesselKernel (m : ℝ) (w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  m / (4 * Real.pi ^ 2 * ‖w‖) * besselKReal 1 (m * ‖w‖)


end VacuumBellSeparation
