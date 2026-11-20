/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.RootEndpoint

/-! # The integer zero slice as the actual Boolean vertex evaluation -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial Matrix
open scoped BigOperators


noncomputable def booleanZeroMonoid (n : ℕ) : BooleanMonomial n →* ℝ where
  toFun S := if S = 1 then 1 else 0
  map_one' := by simp
  map_mul' S T := by
    classical
    let s : Finset (Fin n) := S
    let t : Finset (Fin n) := T
    change (if s ∪ t = ∅ then (1 : ℝ) else 0) =
      (if s = ∅ then 1 else 0) * (if t = ∅ then 1 else 0)
    by_cases hs : s = ∅ <;> by_cases ht : t = ∅ <;> simp [Finset.union_eq_empty, hs, ht]

/-- Evaluation of all Boolean variables at zero. -/
noncomputable def booleanZeroEval (n : ℕ) : BooleanPolynomial n →ₐ[ℝ] ℝ :=
  MonoidAlgebra.lift ℝ ℝ (BooleanMonomial n) (booleanZeroMonoid n)

theorem booleanZeroEval_monomial {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    booleanZeroEval n (booleanMonomial S a) = if S = ∅ then a else 0 := by
  classical
  rw [booleanZeroEval, booleanMonomial, MonoidAlgebra.lift_single]
  change a * (if S = ∅ then 1 else 0) = _
  split_ifs <;> simp

theorem sliceFunctional_zero_monomial {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    sliceFunctional n 0 (booleanMonomial S a) = if S = ∅ then a else 0 := by
  classical
  rw [sliceFunctional_monomial]
  by_cases hS : S = ∅
  · subst S
    simp
  · have hc : S.card ≠ 0 := by simpa using hS
    simp only [sliceMoment, falling_zero_argument hc, zero_div, mul_zero, ite_eq_right hS]

theorem sliceFunctional_zero_eval (n : ℕ) (f : BooleanPolynomial n) :
    sliceFunctional n 0 f = booleanZeroEval n f := by
  classical
  have he : f = ∑ S ∈ f.coeff.support, booleanMonomial S.toFinset (f.coeff S) :=
    (MonoidAlgebra.sum_coeff_single f).symm
  rw [he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [sliceFunctional_zero_monomial, booleanZeroEval_monomial]

theorem booleanZeroEval_var {n : ℕ} (i : Fin n) : booleanZeroEval n (booleanVar i) = 0 := by
  rw [booleanVar, booleanZeroEval_monomial]
  simp

theorem booleanMatrixImage_zero_slice {n : ℕ} {ι κ : Type*} (M : Matrix ι κ (BooleanPolynomial n)) :
    booleanMatrixImage (sliceFunctional n 0) M = M.map (booleanZeroEval n) := by
  apply Matrix.ext
  intro i j
  exact sliceFunctional_zero_eval n (M i j)

theorem booleanZeroEval_matrix_input {n : ℕ} {ι : Type*} (E : Fin n → Matrix ι ι ℝ) :
    (booleanLinearMatrix E).map (booleanZeroEval n) = 0 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, booleanLinearMatrix, map_sum, map_mul, booleanZeroEval_var,
    zero_mul, Finset.sum_const_zero, Matrix.zero_apply]

/-- At the zero vertex, the Chebyshev matrix polynomial is the identity. -/
theorem zero_slice_chebyshev {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (m : ℕ) :
    booleanMatrixImage (sliceFunctional n 0)
      (aeval (booleanChebyshevArgument E) (Polynomial.Chebyshev.T ℝ (m : ℤ))) = 1 := by
  rw [booleanMatrixImage_zero_slice]
  let Φ : Matrix ι ι (BooleanPolynomial n) →ₐ[ℝ] Matrix ι ι ℝ := (booleanZeroEval n).mapMatrix
  change Φ (aeval (booleanChebyshevArgument E) (Polynomial.Chebyshev.T ℝ (m : ℤ))) = 1
  have hX : Φ (booleanChebyshevArgument E) = 1 := by
    rw [booleanChebyshevArgument, map_sub, map_one, map_smul]
    have hB : Φ (booleanLinearMatrix E) = 0 := booleanZeroEval_matrix_input E
    rw [hB, smul_zero, sub_zero]
  rw [← aeval_algHom_apply, hX]
  simp [Polynomial.aeval_def]

end NoncommutativeAMGM
