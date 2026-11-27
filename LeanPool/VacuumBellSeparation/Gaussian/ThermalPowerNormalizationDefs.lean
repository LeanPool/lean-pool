/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers

/-!
# Actual CFC thermal power divided by its actual trace

This construction is separated from its later specification proofs.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

/-- Continuous linear map for the normalized thermal power, of type `OscillatorSpace →L[ℂ]
OscillatorSpace`. -/
noncomputable def normalizedThermalPower (q τ : ℝ) :
    OscillatorSpace →L[ℂ] OscillatorSpace :=
  (positiveTrace (thermalDensity q ^ τ)).toReal⁻¹ • (thermalDensity q ^ τ)


end VacuumBellSeparation.Gaussian
