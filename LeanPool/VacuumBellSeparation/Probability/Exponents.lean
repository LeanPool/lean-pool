/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Basic.Real.Basic

/-!
# Exponents of the probability criterion

Real exponents of Theorem 3.1 of the manuscript (`thm:probability`), equations
`eq:probability-exponents` (3.2) and `eq:nus` (3.4).  Here `rp` is the forward order
`r₊` and `rm` the reverse order `r₋`.  The manuscript assumes `2 < r₊` and `1 < r₋ < 2`.

This module contains definitions only.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- The exponent `b = 1 - 1/r₊` of equation (3.2). -/
noncomputable def expB (rp : ℝ) : ℝ := 1 - 1 / rp

/-- The exponent `a = 1 - 1/r₋` of equation (3.2). -/
noncomputable def expA (rm : ℝ) : ℝ := 1 - 1 / rm

/-- The exponent `η = 1 - (1 - b)/(a b²)` of equation (3.2). -/
noncomputable def expEta (rp rm : ℝ) : ℝ :=
  1 - (1 - expB rp) / (expA rm * expB rp ^ 2)

/-- The exponent `ν₊ = (1 + b)/(a r₊ b²)` of equation (3.4). -/
noncomputable def nuPlus (rp rm : ℝ) : ℝ :=
  (1 + expB rp) / (expA rm * rp * expB rp ^ 2)

/-- The exponent `ν₋ = (1 - a)/a` of equation (3.4). -/
noncomputable def nuMinus (rm : ℝ) : ℝ := (1 - expA rm) / expA rm

end VacuumBellSeparation
