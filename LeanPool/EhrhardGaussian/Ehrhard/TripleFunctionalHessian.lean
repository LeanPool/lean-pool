/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalTimeDerivative

/-! # The covariance-Hessian identity for the singular triple -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The quantile vector applies the Gaussian quantile to each of three probabilities. -/
def quantileVector (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => gaussianCDFChart.symm (x i)

/-- The inverse profile matrix has reciprocal Gaussian densities at the coordinate quantiles on its
diagonal. -/
def inverseProfileDiagonal (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun i => (gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)))⁻¹)

/-- The triple quantile combination equals the triple linear form applied to the quantile vector. -/
theorem quantileLinear_tripleTheta (p q σ : ℝ) (x : Fin 3 → ℝ) :
    quantileLinear (tripleTheta p q σ) x = tripleLinearForm p q σ (quantileVector x) := by
  simp [quantileLinear, tripleTheta, tripleLinearForm, quantileVector, Fin.sum_univ_three]
  ring

/-- The covariance weighted functional Hessian factors through the inverse profile and the explicit
triple matrices. -/
theorem covariance_hessian_triple {p q ρ σ : ℝ}
    (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ) (r : ℝ)
    {x : Fin 3 → ℝ} (hx : x ∈ probabilityBox) :
    tripleCovariance p q ρ ⊙ coordinateHessian (gaussianFunctional (tripleTheta p q σ) r) x =
      (r * gaussianPDFReal 0 1 (r * tripleLinearForm p q σ (quantileVector x))) •
        (inverseProfileDiagonal x *
          (tripleD0 p q σ (quantileVector x) -
            (r ^ 2 * tripleLinearForm p q σ (quantileVector x)) • tripleHessianMatrix p q ρ σ) *
          inverseProfileDiagonal x) := by
  have hcoeff : (fun i => tripleCovariance p q ρ i i * tripleTheta p q σ i * gaussianCDFChart.symm
    (x i)) =
      ![p * quantileVector x 0, q * quantileVector x 1, -σ ^ 3 * quantileVector x 2] := by
    funext i
    fin_cases i
    · simp [tripleCovariance, tripleTheta, quantileVector]
    · simp [tripleCovariance, tripleTheta, quantileVector]
    · change (p ^ 2 + q ^ 2 + 2 * p * q * ρ) * (-σ) * gaussianCDFChart.symm (x 2) =
        -σ ^ 3 * gaussianCDFChart.symm (x 2)
      rw [← hvar]
      ring
  rw [covariance_hessian_gaussianFunctional _ _ _ hx, hcoeff, quantileLinear_tripleTheta]
  rfl

/-- The time-dependent covariance-Hessian condition, with the time
derivative and diagonal congruence computed explicitly. -/
theorem exists_time_covariance_hessian_posSemidef {p q ρ σ κ ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1)
    (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (hκ : 0 < κ) (hε : 0 < ε) (L : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
      x ∈ probabilityBox → (∀ i, |quantileVector x i| ≤ L) →
      tripleLinearForm p q σ (quantileVector x) ≤ -κ →
      (tripleCovariance p q ρ ⊙
          coordinateHessian (gaussianFunctional (tripleTheta p q σ) (interpolationScale R ε t)) x -
        ((Real.exp (2 * (t + ε)) - 1) *
          deriv (fun s => gaussianFunctional (tripleTheta p q σ) (interpolationScale R ε s) x) t) •
          (inverseProfileDiagonal x * tripleE p q σ * inverseProfileDiagonal x)).PosSemidef := by
  obtain ⟨R, hR, hbase⟩ := exists_interpolationScale_posSemidef hp hq hsum hρ hσ hκ hε L
  refine ⟨R, hR, ?_⟩
  intro t ht x hx hbound hgap
  have hmiddle := hbase t ht (quantileVector x) hbound hgap
  have hcong := hmiddle.conjTranspose_mul_mul_same (inverseProfileDiagonal x)
  have hD : (inverseProfileDiagonal x).IsHermitian := Matrix.isHermitian_diagonal _
  rw [hD.eq] at hcong
  have hpref : 0 ≤ interpolationScale R ε t *
      gaussianPDFReal 0 1 (interpolationScale R ε t * tripleLinearForm p q σ (quantileVector x)) :=
    mul_nonneg (mul_nonneg hR.le (Real.sqrt_nonneg _)) (gaussianPDFReal_nonneg 0 1 _)
  have h := hcong.smul hpref
  convert h using 1
  rw [covariance_hessian_triple hvar _ hx, (hasDerivAt_time_gaussianFunctional _ _ R hε ht).deriv,
    quantileLinear_tripleTheta]
  ext i j
  simp only [inverseProfileDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, interpolationTimeCoefficient, div_eq_mul_inv]
  ring

end EhrhardGaussian.Ehrhard

end
