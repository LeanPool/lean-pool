/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

export MatrixMultiplication.Arithmetic.Gate (eval_mapRegister cost_mapRegister)

/-- Relabel register references through the generic gate implementation. -/
abbrev mapRegister {Input R S : Type*} (f : R → S) : Gate Input R → Gate Input S :=
  MatrixMultiplication.Arithmetic.Gate.mapRegister f

end Gate

namespace Program

export MatrixMultiplication.Arithmetic.Program
  (oldIndex newIndex oldIndex_zero oldIndex_succ newIndex_zero newIndex_succ
    eval_append_new eval_append_old cost_append)

/-- Concatenate complex programs through the generic append implementation. -/
abbrev append {Input : Type*} {r : ℕ} (p : Program Input r) :
    {s : ℕ} → Program Input s → Program Input (r + s) :=
  MatrixMultiplication.Arithmetic.Program.append p

end Program

/-- Complex expressions use the shared field-generic arithmetic syntax. -/
abbrev Expression (Input : Type*) := MatrixMultiplication.Arithmetic.Expression ℂ Input

namespace Expression

export MatrixMultiplication.Arithmetic.Expression
  (literal input add sub mul Compiled)

/-- Interpret a complex expression with the shared field-generic semantics. -/
abbrev eval {Input : Type*} (inputs : Input → ℂ) : Expression Input → ℂ :=
  MatrixMultiplication.Arithmetic.Expression.eval inputs

/-- Count the arithmetic operations in a complex expression. -/
abbrev cost {Input : Type*} : Expression Input → ℕ :=
  MatrixMultiplication.Arithmetic.Expression.cost

/-- Compile a complex expression with the shared correctness and cost certificates. -/
abbrev compile {Input : Type*} (e : Expression Input) : Compiled e :=
  MatrixMultiplication.Arithmetic.Expression.compile e

end Expression

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
