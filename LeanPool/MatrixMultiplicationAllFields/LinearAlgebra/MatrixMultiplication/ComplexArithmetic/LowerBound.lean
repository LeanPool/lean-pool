/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

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
      | add a b => simp [Gate.cost] at hg0
      | sub a b => simp [Gate.cost] at hg0
      | mul a b => simp [Gate.cost] at hg0
    · simpa only [eval_step_succ] using ih hp0 j

end Program

namespace MatrixAlgorithm

theorem one_le_cost {n : ℕ} (P : MatrixAlgorithm n) (hn : 1 ≤ n)
    (hP : P.Correct) : 1 ≤ P.cost := by
  by_contra hcost
  have hzero : P.program.cost = 0 := by
    change ¬ 1 ≤ P.program.cost at hcost
    omega
  let i : Fin n := ⟨0, by omega⟩
  have hentry (A B : Matrix (Fin n) (Fin n) ℂ) :
      P.program.eval (matrixInputs A B) (P.output i i) = (A * B) i i :=
    congrFun (congrFun (hP A B) i) i
  rcases P.program.eval_eq_constant_or_input_of_cost_eq_zero hzero (P.output i i)
      with ⟨z, hz⟩ | ⟨a, ha⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry 1 1
      rw [hz] at h
      simpa using h
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (hz0.symm.trans hz1)
  · rcases a with ⟨j, k⟩ | ⟨j, k⟩
    · have h := hentry (Matrix.of fun _ _ => 1) 0
      rw [ha] at h
      simp [matrixInputs, Matrix.mul_apply] at h
    · have h := hentry 0 (Matrix.of fun _ _ => 1)
      rw [ha] at h
      simp [matrixInputs, Matrix.mul_apply] at h

end MatrixAlgorithm

theorem admissibleExponent_nonneg {τ : ℝ} (hτ : AdmissibleExponent τ) : 0 ≤ τ := by
  by_contra hneg
  have hτneg : τ < 0 := lt_of_not_ge hneg
  let ε : ℝ := -τ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsum : τ + ε = -ε := by dsimp [ε]; ring
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hcostone : (1 : ℝ) ≤ P.cost :=
    (Nat.one_le_cast (α := ℝ)).mpr (P.one_le_cost hn1 hP)
  rw [hsum, Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv] at hcost
  have hsmall : C / (n : ℝ) ^ ε < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hnpos ε)).mpr hpow
  exact (not_lt_of_ge (hcostone.trans hcost)) hsmall

theorem admissibleExponent_bddBelow : BddBelow {τ : ℝ | AdmissibleExponent τ} := by
  refine ⟨0, ?_⟩
  intro τ hτ
  exact admissibleExponent_nonneg hτ

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
