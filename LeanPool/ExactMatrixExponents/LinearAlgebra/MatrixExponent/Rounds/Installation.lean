/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Construct
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Price.Run
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Shaving.Network
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Valued.Shared

/-! # Compression of tensor powers over finite fields -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent

theorem Rounds.installable (F : Type) [Field F] [Finite F]
    (h : Prices.SharedPrice (AlgebraicClosure F)) : Rounds.Installable F := by
  apply Rounds.installable_of_controller F h
  intro K _ _ s hs p l b
  exact Rounds.SphereScale.controlled K s hs p l b

theorem compresses_of_shared_price {F : Type} [Field F] [Finite F]
    (h : Prices.SharedPrice (AlgebraicClosure F)) : Compresses F := by
  obtain ⟨q, hq, hq₂, sort⟩ := Routing.sorting_of_shared_price h
  exact compresses_of_stages hq hq₂ sort (Rounds.installable F h).reduction

theorem compression_of_square_saving {F : Type} [Field F] [Finite F]
    (h : omega F < 9 / 4) : Compression (Realizes F) :=
  (compresses_of_shared_price (shared_of_saving h)).lists

end MatrixMultiplicationAllFields.MatrixExponent
