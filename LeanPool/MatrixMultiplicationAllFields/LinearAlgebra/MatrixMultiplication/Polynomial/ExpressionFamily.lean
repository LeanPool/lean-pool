/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic.Expression

variable {F : Type*} [Field F]

variable {Input Output : Type*}

/-- A compiled output family with semantic and total operation-count certificates. -/
structure CompiledFamily [Fintype Output] (expressions : Output → Expression F Input) where
  /-- Number of registers allocated to the compiled output family. -/
  registers : ℕ
  /-- Program computing the entire indexed output family. -/
  program : Program F Input registers
  /-- Register holding each compiled output expression. -/
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

/-- Compile a family indexed by a standard finite set, appending the individual programs. -/
def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression F Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

/-- Compile an arbitrary finite family after transporting its indices to a standard finite
set. -/
def compileFamily [Fintype Output] (expressions : Output → Expression F Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Arithmetic.Expression

end

end MatrixMultiplicationAllFields
