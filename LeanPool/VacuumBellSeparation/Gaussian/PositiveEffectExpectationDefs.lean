/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace

/-! # Trace expectation of a positive effect -/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Positive effect expectation given by `positiveTrace (CFC.sqrt M * ρ * CFC.sqrt M)`. -/
def positiveEffectExpectation (ρ M : E →L[ℂ] E) : ℝ≥0∞ :=
  positiveTrace (CFC.sqrt M * ρ * CFC.sqrt M)

end VacuumBellSeparation.Gaussian
