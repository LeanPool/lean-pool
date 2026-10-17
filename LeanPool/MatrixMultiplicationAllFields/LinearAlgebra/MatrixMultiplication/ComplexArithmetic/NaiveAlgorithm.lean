/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexExpressionFamily
public import Mathlib.Tactic.NormNum

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Expression

variable {Input : Type*}

/-- Build an arithmetic expression for a finite sum, with zero as the empty sum. -/
def sumFin : {n : ℕ} → (Fin n → Expression Input) → Expression Input
  | 0, _ => .literal 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression Input) (inputs : Input → ℂ) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

/-- The schoolbook dot-product expression for one matrix-product entry. -/
def naiveEntry {n : ℕ} (i k : Fin n) : Expression (MatrixInput n) :=
  Expression.sumFin fun j : Fin n =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {n : ℕ} (i k : Fin n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {n : ℕ} (i k : Fin n) :
    (naiveEntry i k).cost = 2 * n := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

/-- Compile all schoolbook dot products into one matrix multiplication program. -/
def naiveAlgorithm (n : ℕ) : MatrixAlgorithm n :=
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (n : ℕ) : (naiveAlgorithm n).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (n : ℕ) : (naiveAlgorithm n).cost = 2 * n ^ 3 := by
  let p := Expression.compileFamily (fun ik : Fin n × Fin n => naiveEntry ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (n : ℕ) : (naiveAlgorithm n).cost ≤ 2 * n ^ 3 :=
  (naiveAlgorithm_cost n).le

theorem admissibleExponent_three : AdmissibleExponent 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n, naiveAlgorithm_correct n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n ^ 3 : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n ^ 3 : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
