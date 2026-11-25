/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Tagged.Tags

/-! # Power-of-logarithm lower bound for verifying one permutation -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Tagged
open Filter

/-- Only square payloads at powers of two are required. Count vertices
of exact trivalent networks. Any constant in the lower bound can be
absorbed by decreasing the positive exponent. -/
def Hard (F : Type) [Field F] : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ m,
    Net F (inputs w (word w)) .unit (tag F w (word w)) m →
    (2 : ℝ) ^ w * w * (w : ℝ) ^ σ ≤ m

end MatrixMultiplicationAllFields.MatrixExponent.Tagged
