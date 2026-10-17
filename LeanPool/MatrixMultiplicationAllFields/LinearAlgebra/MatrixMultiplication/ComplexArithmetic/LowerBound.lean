/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Program

theorem eval_eq_constant_or_input_of_cost_eq_zero {Input : Type*} {r : ℕ}
    (p : Program Input r) (hp : p.cost = 0) (i : Fin r) :
    (∃ z : ℂ, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert hp i
  induction p with
  | nil =>
    intro _ i
    exact Fin.elim0 i
  | @step r p g ih =>
    intro hp i
    have hcost : p.cost + g.cost = 0 := hp
    have hp0 : p.cost = 0 := by omega
    have hg0 : g.cost = 0 := by omega
    refine Fin.cases ?_ (fun j => ?_) i
    · cases g with
      | literal z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [MatrixMultiplication.Arithmetic.Gate.cost] at hg0
      | sub a b => simp [MatrixMultiplication.Arithmetic.Gate.cost] at hg0
      | mul a b => simp [MatrixMultiplication.Arithmetic.Gate.cost] at hg0
    · simpa only [eval_step_succ] using ih hp0 j

end Program

namespace MatrixAlgorithm

theorem one_le_cost {n : ℕ} (P : MatrixAlgorithm n) (hn : 1 ≤ n)
    (hP : P.Correct) : 1 ≤ P.cost :=
  (Nat.mul_le_mul hn hn).trans (MatrixMultiplication.Arithmetic.MatrixAlgorithm.output_size_le_cost
    P hn hP)

end MatrixAlgorithm

theorem admissibleExponent_nonneg {τ : ℝ} (hτ : AdmissibleExponent τ) : 0 ≤ τ :=
  (by norm_num : (0 : ℝ) ≤ 2).trans
    (MatrixMultiplication.Arithmetic.admissibleExponent_two_le hτ)

theorem admissibleExponent_bddBelow : BddBelow {τ : ℝ | AdmissibleExponent τ} :=
  MatrixMultiplication.Arithmetic.admissibleExponent_bddBelow ℂ

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
