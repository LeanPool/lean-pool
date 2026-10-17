/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

/-- Complex gates are the field-generic gates specialized to the complex numbers. -/
abbrev Gate (Input Register : Type*) :=
  MatrixMultiplication.Arithmetic.Gate ℂ Input Register

namespace Gate

export MatrixMultiplication.Arithmetic.Gate (literal input add sub mul)

/-- Evaluate a complex gate using the shared arithmetic semantics. -/
abbrev eval {Input Register : Type*} (inputs : Input → ℂ) (registers : Register → ℂ) :
    Gate Input Register → ℂ := MatrixMultiplication.Arithmetic.Gate.eval inputs registers

/-- Count the arithmetic operation performed by a complex gate. -/
abbrev cost {Input Register : Type*} : Gate Input Register → ℕ :=
  MatrixMultiplication.Arithmetic.Gate.cost

end Gate

/-- Complex programs use the shared field-generic straight-line syntax. -/
abbrev Program (Input : Type*) (registers : ℕ) :=
  MatrixMultiplication.Arithmetic.Program ℂ Input registers

namespace Program

export MatrixMultiplication.Arithmetic.Program (eval_step_zero eval_step_succ cost_step)

/-- The empty complex program. -/
abbrev nil {Input : Type*} : Program Input 0 := MatrixMultiplication.Arithmetic.Program.nil

/-- Append one gate to a complex program. -/
abbrev step {Input : Type*} {r : ℕ} (p : Program Input r) (g : Gate Input (Fin r)) :
    Program Input (r + 1) := MatrixMultiplication.Arithmetic.Program.step p g

/-- Evaluate the registers of a complex program using the shared interpreter. -/
abbrev eval {Input : Type*} : {r : ℕ} → Program Input r → (Input → ℂ) → Fin r → ℂ :=
  MatrixMultiplication.Arithmetic.Program.eval

/-- Total arithmetic cost of a complex program. -/
abbrev cost {Input : Type*} : {r : ℕ} → Program Input r → ℕ :=
  MatrixMultiplication.Arithmetic.Program.cost

end Program

/-- Input entries for the two square matrices. -/
abbrev MatrixInput (n : ℕ) := MatrixMultiplication.Arithmetic.MatrixInput n n n

/-- Assemble the two square matrices in the shared input representation. -/
abbrev matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : MatrixInput n → ℂ :=
  MatrixMultiplication.Arithmetic.matrixInputs A B

/-- Square complex matrix algorithms are a specialization of rectangular field algorithms. -/
abbrev MatrixAlgorithm (n : ℕ) :=
  MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ n n n

namespace MatrixAlgorithm

export MatrixMultiplication.Arithmetic.MatrixAlgorithm (correct_iff_entries)

/-- Evaluate the output matrix of a square complex algorithm. -/
abbrev eval {n : ℕ} (P : MatrixAlgorithm n) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := MatrixMultiplication.Arithmetic.MatrixAlgorithm.eval P A B

/-- Correctness for every pair of square complex input matrices. -/
abbrev Correct {n : ℕ} (P : MatrixAlgorithm n) : Prop :=
  MatrixMultiplication.Arithmetic.MatrixAlgorithm.Correct P

/-- Total arithmetic cost of a square complex matrix algorithm. -/
abbrev cost {n : ℕ} (P : MatrixAlgorithm n) : ℕ :=
  MatrixMultiplication.Arithmetic.MatrixAlgorithm.cost P

end MatrixAlgorithm

/-- The shared one-multiplication scalar algorithm over the complex numbers. -/
abbrev scalarAlgorithm : MatrixAlgorithm 1 := MatrixMultiplication.Arithmetic.scalarAlgorithm ℂ

theorem scalarAlgorithm_correct : scalarAlgorithm.Correct :=
  MatrixMultiplication.Arithmetic.scalarAlgorithm_correct ℂ

theorem scalarAlgorithm_cost : scalarAlgorithm.cost = 1 :=
  MatrixMultiplication.Arithmetic.scalarAlgorithm_cost ℂ

/-- Uniform complex arithmetic bounds with arbitrarily small positive exponent slack. -/
abbrev AdmissibleExponent (exponent : ℝ) : Prop :=
  MatrixMultiplication.Arithmetic.AdmissibleExponent ℂ exponent

/-- The field-generic matrix multiplication exponent specialized to the complex numbers. -/
abbrev omega : ℝ := MatrixMultiplication.Arithmetic.omega ℂ

end MatrixMultiplication.Foundation.Arithmetic

namespace MatrixMultiplication.Foundation

namespace Tensor

/-- The coefficient tensor encoding rectangular matrix multiplication. -/
def matrixMultiplication (a b c : ℕ) :
    Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

@[simp] theorem matrixMultiplication_matching (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    matrixMultiplication a b c (i, j) (j, k) (k, i) = 1 := by
  simp [matrixMultiplication]

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
