/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Programs

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

@[expose] public section

namespace MatrixMultiplicationAllFields

namespace MatrixMultiplication.Foundation.Arithmetic.Expression

export MatrixMultiplication.Arithmetic.Expression (CompiledFamily compileFinFamily compileFamily)

end MatrixMultiplication.Foundation.Arithmetic.Expression

end MatrixMultiplicationAllFields
