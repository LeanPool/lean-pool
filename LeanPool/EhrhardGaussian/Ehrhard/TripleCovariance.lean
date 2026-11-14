/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalHessian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-!
# The singular covariance matrix in the three-function interpolation

The third variable is `p X + q Y`. A rectangular Gaussian factor proves
positive semidefiniteness without requiring a nonsingular three-dimensional
density. The weighted Hessian matrix has an explicit sum-of-squares form.
-/

@[expose] public noncomputable section

open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The triple covariance matrix describes two unit variance correlated variables and their weighted
sum. -/
def tripleCovariance (p q ρ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, ρ, p + q * ρ;
     ρ, 1, q + p * ρ;
     p + q * ρ, q + p * ρ, p ^ 2 + q ^ 2 + 2 * p * q * ρ]

/-- The triple Gaussian factor realizes the correlated triple using two independent standard
Gaussian coordinates. -/
def tripleGaussianFactor (p q ρ : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0;
     ρ, Real.sqrt (1 - ρ ^ 2);
     p + q * ρ, q * Real.sqrt (1 - ρ ^ 2)]

/-- The triple covariance matrix equals its Gaussian factor times its transpose for admissible
correlation. -/
theorem tripleCovariance_eq_factor (p q : ℝ) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    tripleCovariance p q ρ = tripleGaussianFactor p q ρ * (tripleGaussianFactor p q ρ)ᴴ := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hρ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripleCovariance, tripleGaussianFactor, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> simp only [hs] <;> ring



/-- The triple comparison coefficients are the two input weights and the negative output scale. -/
def tripleTheta (p q σ : ℝ) : Fin 3 → ℝ := ![p, q, -σ]

/-- The matrix denoted `B` in NP16's perturbation argument. -/
def tripleHessianMatrix (p q ρ σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  tripleCovariance p q ρ ⊙ Matrix.vecMulVec (tripleTheta p q σ) (tripleTheta p q σ)

/-- The triple Hessian matrix is symmetric. -/
theorem tripleHessianMatrix_isHermitian (p q ρ σ : ℝ) :
    (tripleHessianMatrix p q ρ σ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripleHessianMatrix, tripleCovariance, tripleTheta, Matrix.conjTranspose_apply,
      Matrix.hadamard_apply, mul_comm, mul_left_comm, mul_assoc]

/-- The triple Hessian quadratic form decomposes into two weighted squares. -/
theorem tripleHessianMatrix_quadratic (p q ρ σ : ℝ) (x : Fin 3 → ℝ) :
    x ⬝ᵥ (tripleHessianMatrix p q ρ σ *ᵥ x) =
      (p * (x 0 - σ * x 2) + ρ * q * (x 1 - σ * x 2)) ^ 2 +
        (1 - ρ ^ 2) * q ^ 2 * (x 1 - σ * x 2) ^ 2 := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, tripleHessianMatrix,
    tripleCovariance, tripleTheta, Matrix.hadamard_apply]
  ring



end EhrhardGaussian.Ehrhard

end
