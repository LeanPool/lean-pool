/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector

/-! # Extending a listed function by fixed points -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Routing
open Coloring

/-- Embeds `B h` into `B (h + 1)`. -/
def lowerHalf (h : ℕ) : B h ↪ B (h + 1) := Fin.castLEEmb (by rw [pow_succ]; omega)

/-- Returns `lowerHalf h (x ⟨a, ha⟩)` when `ha : a.val < 2 ^ h` holds, and `a` otherwise. -/
def inflate (h : ℕ) (x : (Perm h).obj) (a : B (h + 1)) : B (h + 1) :=
  if ha : a.val < 2 ^ h then lowerHalf h (x ⟨a, ha⟩) else a

end MatrixMultiplicationAllFields.MatrixExponent.Routing
