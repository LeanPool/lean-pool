/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagOptimized

/-! # Optimization of tag weights using finite fiber bounds -/

@[expose] public section

open MatrixMultiplicationAllFields.TensorSpectrum
namespace MatrixMultiplicationAllFields.MatrixExponent.Integral
theorem tag_optimized_of_fiber_bounds
    {s : ℕ} (hs : 0 < s) (p : ℝ) (hp : 0 < p)
    (c : Fin s → ℝ) (hc : ∀ i, 0 < c i) (x : ℝ) (hx : 0 ≤ x)
    (hfinite : ∀ N : ℕ, 1 ≤ N → ∀ v : TagWords.CountVector s N,
      0 < (TagWords.fiber v).card →
      ((TagWords.fiber v).card : ℝ) ^ p * TagWords.countWeight c v ≤
        6 * x ^ N) :
    (∑ i, (c i) ^ (1 / p)) ^ p ≤ x :=
  TensorSpectrum.tag_optimized_of_fiber_bounds 6 (by norm_num) hs p hp c hc x hx hfinite

end MatrixMultiplicationAllFields.MatrixExponent.Integral
