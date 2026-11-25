/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Square
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Dual
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Tagged.Reduction
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Iteration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Shaving.Network

/-!
# The two alternatives on the spectral space

Failure of shared pricing forces contact on a tripod. Shared pricing
supplies both kinds of sorting and local concentration. Two network
estimates over prime fields would exclude this second alternative.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent

/-- Square equality and rectangular rigidity follow simultaneously. -/
theorem contact_of_network_estimates
    (hard : ∀ (p : ℕ) [Fact p.Prime], Tagged.Hard (ZMod p))
    (stage : ∀ (p : ℕ) [Fact p.Prime], Prices.SharedPrice (AlgebraicClosure (ZMod p)) →
      ArityReduction (ZMod p))
    (F : Type*) [Field F] : omega F = 9 / 4 ∧ Rectangle.Rigidity F := by
  apply Rectangle.of_prime_fields _ F
  intro p _
  apply contact_of_not_shared
  intro sync
  obtain ⟨q, hq, hq', sort⟩ := Routing.sorting_of_shared_price sync
  have shrink := compresses_of_stages hq hq' sort (stage p sync)
  exact incompatible (seed _) (Tagged.manyList_of_tag (hard p)) shrink.lists

end MatrixMultiplicationAllFields.MatrixExponent
