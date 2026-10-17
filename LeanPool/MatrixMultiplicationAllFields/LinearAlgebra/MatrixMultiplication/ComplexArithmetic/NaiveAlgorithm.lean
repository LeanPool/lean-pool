/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexExpressionFamily
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Expression

variable {Input : Type*}

/-- Form a finite sum using the shared field-generic expression implementation. -/
abbrev sumFin {n : ℕ} (f : Fin n → Expression Input) : Expression Input :=
  MatrixMultiplication.Arithmetic.Expression.sumFin f

export MatrixMultiplication.Arithmetic.Expression (sumFin_eval sumFin_cost)

end Expression

/-- The schoolbook dot-product expression, specialized from the generic implementation. -/
abbrev naiveEntry {n : ℕ} (i k : Fin n) : Expression (MatrixInput n) :=
  MatrixMultiplication.Arithmetic.naiveEntry i k

theorem naiveEntry_eval {n : ℕ} (i k : Fin n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k :=
  MatrixMultiplication.Arithmetic.naiveEntry_eval i k A B

theorem naiveEntry_cost {n : ℕ} (i k : Fin n) :
    (naiveEntry i k).cost = 2 * n :=
  MatrixMultiplication.Arithmetic.naiveEntry_cost i k

/-- Compile the schoolbook algorithm using the shared field-generic construction. -/
abbrev naiveAlgorithm (n : ℕ) : MatrixAlgorithm n :=
  MatrixMultiplication.Arithmetic.naiveAlgorithm n n n

theorem naiveAlgorithm_correct (n : ℕ) : (naiveAlgorithm n).Correct :=
  MatrixMultiplication.Arithmetic.naiveAlgorithm_correct n n n

theorem naiveAlgorithm_cost (n : ℕ) : (naiveAlgorithm n).cost = 2 * n ^ 3 := by
  change (MatrixMultiplication.Arithmetic.naiveAlgorithm (F := ℂ) n n n).cost = _
  rw [MatrixMultiplication.Arithmetic.naiveAlgorithm_cost]
  ring

theorem naiveAlgorithm_cost_le (n : ℕ) : (naiveAlgorithm n).cost ≤ 2 * n ^ 3 :=
  (naiveAlgorithm_cost n).le

theorem admissibleExponent_three : AdmissibleExponent 3 :=
  MatrixMultiplication.Arithmetic.admissibleExponent_three

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent τ} :=
  MatrixMultiplication.Arithmetic.admissibleExponent_nonempty

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
