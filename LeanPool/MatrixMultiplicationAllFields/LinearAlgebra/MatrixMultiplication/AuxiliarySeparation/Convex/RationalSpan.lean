/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dual.Lemmas

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Descent of rational linear systems

A rational linear system which has a real solution also has a rational solution.
The proof applies a rational-linear projection from the reals onto the rationals.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

/-- A rational-linear functional on the reals taking `1` to `1`. -/
theorem exists_ratLinear_one :
    ∃ p : ℝ →ₗ[ℚ] ℚ, p 1 = 1 :=
  Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)

/-- A rational-linear projection from the reals to the rationals. -/
theorem exists_ratLinear_retraction :
    ∃ p : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, p (q : ℝ) = q := by
  obtain ⟨p, hp⟩ := exists_ratLinear_one
  refine ⟨p, fun q ↦ ?_⟩
  have h := p.map_smul q (1 : ℝ)
  simpa [hp] using h

/-- Solvability of a finite rational linear system descends from real to rational
coefficients. The set of equations need not be finite. -/
theorem exists_rat_solution_of_real {I : Type*} {J : Type*} [Fintype I]
    (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ q : I → ℚ, ∀ j, ∑ i, q i * A i j = b j := by
  obtain ⟨p, hp⟩ := exists_ratLinear_retraction
  obtain ⟨x, hx⟩ := h
  refine ⟨fun i ↦ p (x i), fun j ↦ ?_⟩
  have heq := congrArg p (hx j)
  simp only [map_sum, hp] at heq
  convert heq using 1
  apply Finset.sum_congr rfl
  intro i _
  have hmul := p.map_smul (A i j) (x i)
  simpa only [Rat.smul_def, smul_eq_mul, mul_comm] using hmul.symm

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
