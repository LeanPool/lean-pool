/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public import Mathlib.Init

/-! # Natural-number bounds used by tableau measures -/

public section

namespace PDL.NaturalBounds

/-- A bound on the left summand gives a strict bound after adding one. -/
theorem lt_sum_left {value left right : Nat} (bound : value ≤ left) :
    value < 1 + left + right := by omega

/-- A bound on the right summand gives a strict bound after adding one. -/
theorem lt_sum_right {value left right : Nat} (bound : value ≤ right) :
    value < 1 + left + right := by omega

/-- Adding one turns a non-strict bound into a strict bound. -/
theorem lt_one_add {value bound : Nat} (bounded : value ≤ bound) :
    value < 1 + bound := by omega

/-- The smallest nonzero program measure stays below a two-step extension. -/
theorem one_lt_two_add (right : Nat) : 1 < 2 + right := by omega

end PDL.NaturalBounds
