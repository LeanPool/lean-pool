/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Probability.Exponents

/-!
# Statement seed extracted from Constants/Parameters

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- `Λ₀ = 2¹⁵` of (7.10). -/
def Lambda0 : ℝ := 2 ^ 15

/-- `θ = 1/(4Λ₀)` of (7.10). -/
noncomputable def theta : ℝ := 1 / (4 * Lambda0)

/-- `a = θ/2` of (7.10). -/
noncomputable def aRev : ℝ := theta / 2

/-- `γ = 2(1 - θ)` of (7.10). -/
noncomputable def gammaRev : ℝ := 2 * (1 - theta)

/-- `r₋ = 1/(1 - a)` of (8.1). -/
noncomputable def rMinus : ℝ := 1 / (1 - aRev)

/-- `r₊ = 2²⁰` of (8.1) (the manuscript writes `r₊ = ⌈4/a⌉ = 2²⁰`; see `four_div_aRev`). -/
def rPlus : ℝ := 2 ^ 20


end VacuumBellSeparation
