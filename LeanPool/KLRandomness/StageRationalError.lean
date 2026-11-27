/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageErrorBudget
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Rational errors for the stage search

The finite verifier uses rational arithmetic. Its positive rational error is
identified here with the ENNReal dyadic budget used by the final stage API.
-/

@[expose] public section

namespace Klr.StageErrorBudget

open scoped ENNReal

/-- The executable rational presentation of the stage error. -/
def rational (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ n / 100

theorem rational_pos (n : ℕ) : 0 < rational n := by unfold rational; positivity

theorem rational_cast_pos (n : ℕ) : (0 : ℝ) < rational n := by
  exact_mod_cast rational_pos n

theorem ofReal_rational (n : ℕ) : ENNReal.ofReal (rational n : ℝ) = error n := by
  unfold rational error
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

theorem ofReal_mul_rational (k n : ℕ) :
    ENNReal.ofReal ((k : ℝ) * (rational n : ℝ)) = (k : ℝ≥0∞) * error n := by
  rw [ENNReal.ofReal_mul (by positivity), ofReal_rational, ENNReal.ofReal_natCast]

end Klr.StageErrorBudget
