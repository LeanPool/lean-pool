/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Fin

/-! # Coefficient rank for rectangular matrix multiplication -/

@[expose] public section

open scoped BigOperators

namespace MatrixMultiplicationAllFields.TensorSpectrum

/-- A rank decomposition indexed by the two input positions and the output position. -/
def MatrixRank (F : Type*) [CommSemiring F] (i j k r : ℕ) : Prop :=
  ∃ (a : Fin r → (Fin i × Fin k) → F) (b : Fin r → (Fin k × Fin j) → F)
    (c : Fin r → (Fin i × Fin j) → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

end MatrixMultiplicationAllFields.TensorSpectrum
