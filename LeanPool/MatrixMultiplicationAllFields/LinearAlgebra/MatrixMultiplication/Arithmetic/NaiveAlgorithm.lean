/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily
public import Mathlib.Tactic.NormNum

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Division-free arithmetic programs over a field and their operation counts. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression F Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

def naiveEntry {a b c : ℕ} (i : Fin a) (k : Fin c) : Expression F (MatrixInput a b c) :=
  Expression.sumFin fun j : Fin b =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {a b c : ℕ} (i : Fin a) (k : Fin c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {a b c : ℕ} (i : Fin a) (k : Fin c) :
    (naiveEntry (F := F) (b := b) i k).cost = 2 * b := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

def naiveAlgorithm (a b c : ℕ) : MatrixAlgorithm F a b c :=
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (b := b) ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (a b c : ℕ) : (naiveAlgorithm (F := F) a b c).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost = 2 * a * b * c := by
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost ≤ 2 * a * b * c :=
  (naiveAlgorithm_cost a b c).le

theorem admissibleExponent_three : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n n n, naiveAlgorithm_correct n n n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          push_cast
          ring
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Arithmetic

end

end MatrixMultiplicationAllFields
