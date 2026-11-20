/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.BooleanMatrixInput
public import LeanPool.NoncommutativeAMGM.ChebyshevSquares

/-! # Polynomial evaluation on symmetric Boolean matrices, with degree bounds -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial
open scoped BigOperators

theorem booleanMatrix_one_degree (n : ℕ) {ι : Type*} [DecidableEq ι] (i j : ι) :
    BooleanDegreeLE ((1 : Matrix ι ι (BooleanPolynomial n)) i j) 0 := by
  classical
  rw [Matrix.one_apply]
  split_ifs
  · exact booleanDegreeLE_one n
  · exact booleanDegreeLE_zero n 0

theorem booleanMatrix_pow_degree {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι (BooleanPolynomial n)) (hX : ∀ i j, BooleanDegreeLE (X i j) 1) (k : ℕ) :
    ∀ i j, BooleanDegreeLE ((X ^ k) i j) k := by
  induction k with
  | zero => simpa using booleanMatrix_one_degree n (ι := ι)
  | succ k ih =>
    rw [pow_succ]
    exact booleanMatrix_mul_degree _ _ ih hX

theorem booleanMatrix_aeval_degree {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι (BooleanPolynomial n)) (hX : ∀ i j, BooleanDegreeLE (X i j) 1)
    (p : Polynomial ℝ) : ∀ i j, BooleanDegreeLE ((aeval X p) i j) p.natDegree := by
  intro i j
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  apply booleanDegreeLE_sum
  intro k hk
  apply booleanDegreeLE_smul
  exact booleanDegreeLE_mono (booleanMatrix_pow_degree X hX k i j)
    (by have := Finset.mem_range.mp hk; omega)

theorem booleanMatrix_aeval_transpose {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι (BooleanPolynomial n)) (hX : X.transpose = X) (p : Polynomial ℝ) :
    (aeval X p).transpose = aeval X p := by
  simp only [aeval_eq_sum_range, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_pow, hX]

theorem booleanLinearMatrix_degree {n : ℕ} {ι : Type*} (E : Fin n → Matrix ι ι ℝ) (i j : ι) :
    BooleanDegreeLE (booleanLinearMatrix E i j) 1 := by
  apply booleanDegreeLE_sum
  intro a _
  have hc : BooleanDegreeLE (algebraMap ℝ (BooleanPolynomial n) (E a i j)) 0 := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      booleanDegreeLE_smul (E a i j) (booleanDegreeLE_one n)
  simpa only [add_zero, booleanVar] using booleanDegreeLE_mul
    (booleanDegreeLE_monomial {a} 1 (by simp)) hc

theorem booleanLinearMatrix_transpose {n : ℕ} {ι : Type*}
    (E : Fin n → Matrix ι ι ℝ) (hE : ∀ a, (E a).transpose = E a) :
    (booleanLinearMatrix E).transpose = booleanLinearMatrix E := by
  apply Matrix.ext
  intro i j
  change (∑ a, booleanVar a * algebraMap ℝ (BooleanPolynomial n) (E a j i)) = _
  apply Finset.sum_congr rfl
  intro a _
  have he := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) (hE a)
  simp only [Matrix.transpose_apply] at he
  rw [he]

/-- The affine Chebyshev matrix argument `I-2B`. -/
noncomputable def booleanChebyshevArgument {n : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) : Matrix ι ι (BooleanPolynomial n) :=
  1 - (2 : ℝ) • booleanLinearMatrix E

theorem booleanChebyshevArgument_degree {n : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (i j : ι) :
    BooleanDegreeLE (booleanChebyshevArgument E i j) 1 := by
  apply booleanDegreeLE_sub
  · exact booleanDegreeLE_mono (booleanMatrix_one_degree n i j) (by omega)
  · exact booleanDegreeLE_smul 2 (booleanLinearMatrix_degree E i j)

theorem booleanChebyshevArgument_transpose {n : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (hE : ∀ a, (E a).transpose = E a) :
    (booleanChebyshevArgument E).transpose = booleanChebyshevArgument E := by
  simp only [booleanChebyshevArgument, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, booleanLinearMatrix_transpose E hE]

end NoncommutativeAMGM
