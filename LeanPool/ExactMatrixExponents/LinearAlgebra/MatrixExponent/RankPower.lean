/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

/-! Square specializations of the rectangular rank constructions. -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent

variable {F K : Type*} [Field F] [Field K] {n m r s : ℕ}

theorem rank_map (f : F →+* K) (h : RankLE F n r) : RankLE K n r :=
  Rectangle.RankLE.map h f

theorem rank_mul (h : RankLE F n r) (h' : RankLE F m s) : RankLE F (n * m) (r * s) :=
  Rectangle.RankLE.tensor h h'

theorem rank_pow (h : RankLE F n r) (k : ℕ) : RankLE F (n ^ k) (r ^ k) :=
  Rectangle.RankLE.pow h k

end MatrixMultiplicationAllFields.MatrixExponent
