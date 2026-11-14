/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TripleFunctionalHessian
public import LeanPool.EhrhardGaussian.Ehrhard.InterpolationWeights

/-! The interpolation weights of a correlated Gaussian triple determine its diagonal matrix. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The triple interpolation weights normalize the input weights and inverse output scale. -/
def tripleInterpolationWeights (p q σ : ℝ) (i : Fin 3) : ℝ := ![p, q, σ⁻¹] i / (1 + σ⁻¹)

/-- The triple variances are one for each input and the squared scale for the output. -/
def tripleVariances (σ : ℝ) : Fin 3 → ℝ := ![1, 1, σ ^ 2]

/-- Nonnegative input weights and positive output scale give nonnegative interpolation weights. -/
theorem tripleInterpolationWeights_nonneg {p q σ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hσ : 0 < σ) :
    ∀ i, 0 ≤ tripleInterpolationWeights p q σ i := by
  intro i
  have hden : 0 ≤ 1 + σ⁻¹ := by positivity
  fin_cases i
  · exact div_nonneg hp hden
  · exact div_nonneg hq hden
  · exact div_nonneg (inv_nonneg.mpr hσ.le) hden

/-- The triple interpolation weights sum to one when the input weights sum to one. -/
theorem sum_tripleInterpolationWeights {p q σ : ℝ} (hsum : p + q = 1) (hσ : 0 < σ) :
    ∑ i, tripleInterpolationWeights p q σ i = 1 := by
  have hq : q = 1 - p := by linarith only [hsum]
  subst q
  simp [tripleInterpolationWeights, Fin.sum_univ_three]
  field_simp
  ring

/-- Multiplying each interpolation weight by its variance gives its perturbation coefficient. -/
theorem tripleInterpolationWeights_mul_variance (p q : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (i : Fin 3) :
    tripleInterpolationWeights p q σ i * tripleVariances σ i = tripleEcoeff p q σ i := by
  fin_cases i <;> simp [tripleInterpolationWeights, tripleVariances, tripleEcoeff]
  field_simp

/-- The diagonal congruence of E equals D. -/
theorem tripleInterpolationWeightMatrix (p q : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (x : Fin 3 → ℝ) :
    interpolationWeightMatrix (tripleInterpolationWeights p q σ) (tripleVariances σ)
        (fun i => gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i))) =
      inverseProfileDiagonal x * tripleE p q σ * inverseProfileDiagonal x := by
  ext i j
  simp only [interpolationWeightMatrix, inverseProfileDiagonal, tripleE, Matrix.mul_diagonal]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      tripleInterpolationWeights_mul_variance p q hσ]
    ring
  · simp only [Matrix.diagonal_apply_ne _ hij, zero_mul]

/-- Suitable time parameters satisfy the interpolation conditions with normalized weights and the
diagonal matrix `D`. -/
theorem exists_time_interpolation_conditions {p q ρ σ κ ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1)
    (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (hκ : 0 < κ) (hε : 0 < ε) (L : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
      x ∈ probabilityBox → (∀ i, |quantileVector x i| ≤ L) →
      tripleLinearForm p q σ (quantileVector x) ≤ -κ →
      deriv (fun s => gaussianFunctional (tripleTheta p q σ) (interpolationScale R ε s) x) t ≤ 0 ∧
      (tripleCovariance p q ρ ⊙
          coordinateHessian (gaussianFunctional (tripleTheta p q σ) (interpolationScale R ε t)) x -
        ((Real.exp (2 * (t + ε)) - 1) *
          deriv (fun s => gaussianFunctional (tripleTheta p q σ) (interpolationScale R ε s) x) t) •
          interpolationWeightMatrix (tripleInterpolationWeights p q σ) (tripleVariances σ)
            (fun i => gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)))).PosSemidef := by
  obtain ⟨R, hR, hbase⟩ := exists_time_covariance_hessian_posSemidef hp hq hsum hρ hσ hvar hκ hε L
  refine ⟨R, hR, ?_⟩
  intro t ht x hx hbound hgap
  constructor
  · apply deriv_time_gaussianFunctional_nonpos _ _ hR.le hε ht
    rw [quantileLinear_tripleTheta]
    exact hgap.trans (neg_nonpos.mpr hκ.le)
  · rw [tripleInterpolationWeightMatrix p q hσ.ne']
    exact hbase t ht x hx hbound hgap

end EhrhardGaussian.Ehrhard

end
