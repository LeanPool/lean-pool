/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Lookup.ShortTag

/-! # Tagged permutation estimates with wider keys -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Radix

/-- Computes the tag by the application `Net F (Tagged.inputs w (word v)) .unit (Tagged.tag F w
(word v)) m`. -/
def Tag (F : Type) [Field F] (w v m : ℕ) : Prop :=
  Net F (Tagged.inputs w (word v)) .unit (Tagged.tag F w (word v)) m

/-- The wide-record estimate in the conditional stable sorting theorem. -/
def WideTag (F : Type) [Field F] : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ A : ℕ, 2 ≤ A ∧ ∃ C : ℝ, ∀ w v : ℕ, 1 ≤ w → w ^ A ≤ v →
    ∃ m : ℕ, Tag F w v m ∧ (m : ℝ) ≤ C * (2 : ℝ) ^ w * v * (w : ℝ) ^ ζ

end MatrixMultiplicationAllFields.MatrixExponent.Radix
