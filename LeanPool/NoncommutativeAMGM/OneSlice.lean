/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ZeroSlice

/-! # The full integer slice and Boolean vertex-square positivity -/

@[expose] public section
namespace NoncommutativeAMGM

/-- Evaluation of all Boolean variables at one. -/
noncomputable def booleanOneEval (n : ℕ) : BooleanPolynomial n →ₐ[ℝ] ℝ :=
  MonoidAlgebra.lift ℝ ℝ (BooleanMonomial n) (1 : BooleanMonomial n →* ℝ)

theorem booleanOneEval_monomial {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    booleanOneEval n (booleanMonomial S a) = a := by
  rw [booleanOneEval, booleanMonomial, MonoidAlgebra.lift_single]
  change a * (1 : ℝ) = a
  exact mul_one a

theorem sliceFunctional_full_monomial {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    sliceFunctional n (n : ℝ) (booleanMonomial S a) = a := by
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hne : falling (n : ℝ) S.card ≠ 0 := by
    rw [falling_natCast]
    exact_mod_cast (Nat.descFactorial_pos.mpr hcard).ne'
  rw [sliceFunctional_monomial, sliceMoment, div_self hne, mul_one]

theorem sliceFunctional_full_eval (n : ℕ) (f : BooleanPolynomial n) :
    sliceFunctional n (n : ℝ) f = booleanOneEval n f := by
  classical
  have he : f = ∑ S ∈ f.coeff.support, booleanMonomial S.toFinset (f.coeff S) :=
    (MonoidAlgebra.sum_coeff_single f).symm
  rw [he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [sliceFunctional_full_monomial, booleanOneEval_monomial]

theorem sliceFunctional_zero_square_nonneg {n : ℕ} (f : BooleanPolynomial n) :
    0 ≤ sliceFunctional n 0 (f ^ 2) := by
  rw [sliceFunctional_zero_eval, map_pow]
  exact sq_nonneg _

theorem sliceFunctional_full_square_nonneg {n : ℕ} (f : BooleanPolynomial n) :
    0 ≤ sliceFunctional n (n : ℝ) (f ^ 2) := by
  rw [sliceFunctional_full_eval, map_pow]
  exact sq_nonneg _

end NoncommutativeAMGM
