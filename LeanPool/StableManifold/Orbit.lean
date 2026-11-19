/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Logic.Function.Iterate

/-! # Iterates of an orbit with a prescribed recurrence -/

@[expose] public section

namespace StableManifold

/-- A sequence starting at `x` and stepping by `f` consists of the iterates of `f` at `x`. -/
theorem orbit_eq_iterate {X : Type*} {f : X → X} {orbit : ℕ → X} {x : X}
    (initial : orbit 0 = x) (step : ∀ n, orbit (n + 1) = f (orbit n)) (n : ℕ) :
    orbit n = f^[n] x := by
  induction n with
  | zero => exact initial
  | succ n ih => rw [step, ih, Function.iterate_succ_apply']

end StableManifold
