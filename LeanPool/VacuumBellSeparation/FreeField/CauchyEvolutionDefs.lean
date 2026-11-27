/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.EvolutionGenerator

/-! # Schwartz Cauchy data and evolution for the massive field -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform

/-- Cauchy positive data. -/
noncomputable def cauchyPositiveData (m : ℝ) (f g : SpatialSchwartz) : SpatialSchwartz :=
  (1 / 2 : ℂ) • (f - Complex.I • massiveSchwartzPower m (-1) g)

/-- Cauchy negative data. -/
noncomputable def cauchyNegativeData (m : ℝ) (f g : SpatialSchwartz) : SpatialSchwartz :=
  (1 / 2 : ℂ) • (f + Complex.I • massiveSchwartzPower m (-1) g)

/-- The actual velocity, itself a spatial Schwartz function at every real time. -/
noncomputable def massiveSchwartzCauchyVelocity (m t : ℝ) (f g : SpatialSchwartz) :
    SpatialSchwartz :=
  Complex.I • massiveSchwartzEvolution m t (massiveSchwartzPower m 1 (cauchyPositiveData m f g)) -
    Complex.I • massiveSchwartzEvolution m (-t)
      (massiveSchwartzPower m 1 (cauchyNegativeData m f g))

end VacuumBellSeparation
