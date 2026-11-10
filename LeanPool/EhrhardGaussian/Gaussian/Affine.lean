/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Gaussian.GaussianLaw
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-! Finite-dimensional Gaussian laws, including singular laws and dimension zero, admit affine
representations by independent standard normal coordinates. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace EhrhardGaussian.Gaussian

/-- The coordinate covariance matrix of a Euclidean Gaussian law. -/
def gaussianCovarianceMatrix {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (covarianceBilin μ).toBilinForm

/-- The covariance matrix is positive semidefinite, including for degenerate laws. -/
theorem gaussianCovarianceMatrix_posSemidef {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    (gaussianCovarianceMatrix μ).PosSemidef := by
  apply (LinearMap.isPosSemidef_iff_posSemidef_toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).mp
  exact { eq := covarianceBilin_comm, nonneg := covarianceBilin_self_nonneg }

/-- A Gaussian law is the multivariate Gaussian with its mean and covariance. -/
theorem eq_multivariateGaussian {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsGaussian μ] :
    μ = multivariateGaussian (∫ x, x ∂μ) (gaussianCovarianceMatrix μ) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    intro i j
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_multivariateGaussian (gaussianCovarianceMatrix_posSemidef μ)]
    simp [gaussianCovarianceMatrix]

/-- The affine square-root map realizing a Gaussian law from independent standard normals. -/
def gaussianAffineMap {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (∫ y, y ∂μ) + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (gaussianCovarianceMatrix μ))
    (WithLp.toLp 2 x)

/-- The realizing affine map is measurable. -/
theorem measurable_gaussianAffineMap {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : Measurable (gaussianAffineMap μ) := by
  unfold gaussianAffineMap
  fun_prop

/-- Every Mathlib Gaussian on Euclidean space is an affine image of the coordinate product law. -/
theorem hasLaw_gaussianAffineMap {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsGaussian μ] : HasLaw (gaussianAffineMap μ) μ (standardGaussianMeasure n) where
  aemeasurable := (measurable_gaussianAffineMap μ).aemeasurable
  map_eq := by
    conv_rhs => rw [eq_multivariateGaussian μ]
    rw [multivariateGaussian, ← map_pi_eq_stdGaussian,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

end EhrhardGaussian.Gaussian

end
