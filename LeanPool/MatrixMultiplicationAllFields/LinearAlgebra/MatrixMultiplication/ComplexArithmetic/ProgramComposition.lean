/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Programs

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Gate

export MatrixMultiplication.Arithmetic.Gate
  (eval_mapInput cost_mapInput eval_mapSource cost_mapSource)

/-- Relabel the inputs of a complex gate through the generic implementation. -/
abbrev mapInput {Input Input' Register : Type*} (f : Input → Input') :
    Gate Input Register → Gate Input' Register := MatrixMultiplication.Arithmetic.Gate.mapInput f

/-- Substitute input wires or scalars in a complex gate. -/
abbrev mapSource {Input Input' Register : Type*} (f : Input → Input' ⊕ ℂ) :
    Gate Input Register → Gate Input' Register := MatrixMultiplication.Arithmetic.Gate.mapSource f

end Gate

namespace Program

export MatrixMultiplication.Arithmetic.Program
  (eval_mapInput cost_mapInput eval_mapSource cost_mapSource Substituted)

/-- Relabel complex program inputs through the generic implementation. -/
abbrev mapInput {Input Input' : Type*} (f : Input → Input') :
    {r : ℕ} → Program Input r → Program Input' r :=
  MatrixMultiplication.Arithmetic.Program.mapInput f

/-- Substitute input wires or scalars throughout a complex program. -/
abbrev mapSource {Input Input' : Type*} (f : Input → Input' ⊕ ℂ) :
    {r : ℕ} → Program Input r → Program Input' r :=
  MatrixMultiplication.Arithmetic.Program.mapSource f

/-- Compose complex programs using the generic substitution proof and certificates. -/
abbrev substitute {Input Mid : Type*} {r : ℕ} (p : Program Input r) :
    {s : ℕ} → (q : Program Mid s) → (wires : Mid → Fin r) → Substituted p q wires :=
  MatrixMultiplication.Arithmetic.Program.substitute p

namespace Substituted

export MatrixMultiplication.Arithmetic.Program.Substituted (step)

end Substituted
end Program

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
