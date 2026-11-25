/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Tagged.Tags

/-! # Width estimates for tagged permutations -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Lookup

/-- The ordinary-width tagged permutation estimate. -/
def ShortTag (F : Type) [Field F] (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∃ v : ℕ,
    Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) v ∧
    (v : ℝ) ≤ C * (2 : ℝ) ^ w * (w : ℝ) ^ p

end MatrixMultiplicationAllFields.MatrixExponent.Lookup
