/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Statement seed extracted from Gaussian/ThermalScalar

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- The constant `c_τ` of Lemma 4.3 (the two formulas agree at `τ = 1/2`). -/
noncomputable def thermalConst (τ : ℝ) : ℝ := if τ ≤ 1 / 2 then (2 : ℝ) ^ (1 - 2 * τ) else
  (1 - τ) / τ

/-- The scalar ratio `𝔮_τ(u) = sinh((1-τ)u)/sinh(τu) · cosh(u)^{2τ-1}`. -/
noncomputable def thermalRatio (τ u : ℝ) : ℝ :=
  Real.sinh ((1 - τ) * u) / Real.sinh (τ * u) * Real.cosh u ^ (2 * τ - 1)


end VacuumBellSeparation
