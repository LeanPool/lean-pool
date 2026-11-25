/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

/-! # Rank lower bound from flattening the square multiplication tensor -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent

/-- The square output flattening has rank equal to the area. -/
theorem rank_lower {F : Type*} [Field F] {n r : ℕ} (h : RankLE F n r) :
    n ^ 2 ≤ r := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [pow_two]
    exact Rectangle.RankLE.area h (Nat.pos_of_ne_zero hn)

end MatrixMultiplicationAllFields.MatrixExponent
