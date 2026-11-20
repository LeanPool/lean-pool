/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.OrderedWords
public import LeanPool.NoncommutativeAMGM.RootCoefficientExtraction

/-! # Extracting the top Boolean coefficient of an actual matrix polynomial -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- For a degree-`m` matrix polynomial in `B`, the top Boolean layer is its leading
scalar coefficient times the actual ordered distinct-index product sum. -/
theorem booleanMatrix_aeval_top {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (p : Polynomial ℝ) (hp : p.natDegree ≤ m) :
    booleanMatrixImage (layerCoefficientSum n m) (aeval (booleanLinearMatrix E) p) =
      p.coeff m • distinctProductSum n m E := by
  classical
  apply Matrix.ext
  intro i j
  change layerCoefficientSum n m ((aeval (booleanLinearMatrix E) p) i j) = _
  rw [aeval_eq_sum_range' (show p.natDegree < m + 1 by omega), Matrix.sum_apply, map_sum]
  simp only [Matrix.smul_apply, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single m]
  · have he := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) (booleanLinearMatrix_pow_top E m)
    change layerCoefficientSum n m ((booleanLinearMatrix E ^ m) i j) =
      distinctProductSum n m E i j at he
    rw [he]
  · intro k hk hkm
    have hlt : k < m := by have := Finset.mem_range.mp hk; omega
    rw [layerCoefficientSum_eq_zero _
      (booleanMatrix_pow_degree _ (booleanLinearMatrix_degree E) k i j) hlt, mul_zero]
  · simp

end NoncommutativeAMGM
