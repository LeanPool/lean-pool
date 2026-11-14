/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

/-!
Exact telescoping for the reciprocal-quadratic comparison sums used
in the sharp dyadic harmonic-tail estimates.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Shifted reciprocal-product sums have an exact endpoint formula.
This is the finite algebraic ingredient of the two-sided tail estimate. -/
theorem proposed_randomInitialStake_reciprocalTail_telescope
    (m n : Nat) (hm : 0 < m) :
    (Finset.range n).sum (fun j =>
      1 / (4 * (((m+j : Nat) : Real)) * (((m+j+1 : Nat) : Real)))) =
      1 / (4 * (m : Real)) - 1 / (4 * (((m+n : Nat) : Real))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hmpos : (0 : Real) < (m : Real) := by exact_mod_cast hm
      have hmnpos : (0 : Real) < ((m+n : Nat) : Real) := by
        exact_mod_cast (by omega : 0 < m+n)
      have hidx : m + (n + 1) = m + n + 1 := by omega
      have hcast : ((m+n+1 : Nat) : Real) =
          ((m+n : Nat) : Real) + 1 := by push_cast; ring
      rw [hidx, hcast]
      have hnp1 : ((m+n : Nat) : Real) + 1 ≠ 0 := by positivity
      field_simp [ne_of_gt hmpos, ne_of_gt hmnpos, hnp1]
      ring

end ECRuntime
