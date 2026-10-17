/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Main.lean`, by Jeroen Zuiddam,
2026: Theorem 1.1 and `omega_le_nine_quarters` stated over an algebraically closed field `K`;
`complex_omega_le_nine_quarters` is now the instance `K = ℂ`; `ℂ` replaced by a field `K`;
`[IsAlgClosed K]` is assumed by the declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankBound
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.RankLowerBound
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Bounds
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Floor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Matrix multiplication via auxiliary separation and polynomial multiplication

Theorem 1.1 gives a uniform arithmetic-operation bound for square matrix
multiplication over an algebraically closed field `K` of any characteristic
(in particular `K = ℂ`), and consequently an upper bound of `9/4` on its
exponent.  The two conclusions are stated separately in the existing arithmetic
model.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



namespace MatrixMultiplication.AuxiliarySeparation

/-- Theorem 1.1: for every positive exponent slack, one constant bounds the cost
of correct matrix multiplication programs over `K` at every positive size. -/
theorem matrix_multiplication_cost_le [IsAlgClosed K] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm K n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  arithmeticComplexity_of_exactRankExponent_le exactRankExponent_le_nine_quarters ε hε

/-- The arithmetic matrix multiplication exponent of an algebraically closed
field is at most `9/4`. -/
theorem omega_le_nine_quarters [IsAlgClosed K] : Arithmetic.omega K ≤ (9 : ℝ) / 4 :=
  omega_le_exactRankExponent.trans exactRankExponent_le_nine_quarters

/-- The complex case. -/
theorem complex_omega_le_nine_quarters : Arithmetic.omega ℂ ≤ (9 : ℝ) / 4 :=
  omega_le_nine_quarters

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
