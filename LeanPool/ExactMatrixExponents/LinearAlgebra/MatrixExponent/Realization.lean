/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Obstruction
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.BatchDescent.Hard
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Install

/-!
# Reduction to the compression installation

Exact many-list hardness holds over all finite fields. The arithmetic
equality and the rectangular rigidity therefore reduce to the
compression construction over prime fields under shared prices.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent

theorem contact_of_installations
    (rounds : ∀ (p : ℕ) [Fact p.Prime], Prices.SharedPrice (AlgebraicClosure (ZMod p)) →
      Rounds.Installable (ZMod p))
    (F : Type*) [Field F] : omega F = 9 / 4 ∧ Rectangle.Rigidity F :=
  contact_of_network_estimates (fun p _ => BatchDescent.hard (ZMod p))
    (fun p _ h => (rounds p h).reduction) F

end MatrixMultiplicationAllFields.MatrixExponent
