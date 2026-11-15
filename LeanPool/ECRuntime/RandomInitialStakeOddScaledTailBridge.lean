/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.FitnessLevel

/-!
An exact bridge between the scaled odd- and even-dimensional harmonic
tails, including the additional reciprocal contribution.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

namespace ECRuntime

/-- Raising the upper harmonic index from 2m to 2m+1 changes the
(2m+1)-scaled harmonic-log error by exactly one. -/
theorem proposed_randomInitialStake_oddScaledTail_evenBridge (m : Nat) :
    (((2 * m + 1 : Nat) : Real) *
      (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) =
    (((2 * m + 1 : Nat) : Real) *
      (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) + 1 := by
  have hsucc : harmonicReal (2 * m + 1) =
      harmonicReal (2 * m) + ((2 * m + 1 : Nat) : Real)⁻¹ := by
    simp [harmonicReal, harmonic_succ]
  rw [hsucc]
  have hne : ((2 * m + 1 : Nat) : Real) ≠ 0 := by positivity
  field_simp
  ring

end ECRuntime
