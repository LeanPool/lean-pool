/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OULinearPullback
public import LeanPool.EhrhardGaussian.Ehrhard.TripleWeights
public import LeanPool.EhrhardGaussian.Ehrhard.OUFamily

/-! # The scalar-gradient conditions for the correlated triple -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative)
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The triple scales are unit scale for the inputs and the specified scale for the output. -/
def tripleScales (σ : ℝ) : Fin 3 → ℝ := ![1, 1, σ]

/-- The triple lift pulls each scalar function back along its Gaussian factor row. -/
def tripleLift (f : Fin 3 → ℝ → ℝ) (p q ρ : ℝ) (i : Fin 3) : (Fin 2 → ℝ) → ℝ :=
  f i ∘ coordinateForm (tripleGaussianFactor p q ρ i)


/-- A positive output scale makes all three scales positive. -/
theorem tripleScales_pos {σ : ℝ} (hσ : 0 < σ) (i : Fin 3) : 0 < tripleScales σ i := by
  fin_cases i
  · exact zero_lt_one
  · exact zero_lt_one
  · exact hσ

/-- The Gram matrix of the triple Gaussian factor is the triple covariance matrix. -/
theorem tripleFactor_gram (p q : ℝ) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    tripleGaussianFactor p q ρ * (tripleGaussianFactor p q ρ)ᵀ = tripleCovariance p q ρ := by
  convert (tripleCovariance_eq_factor p q hρ).symm using 1
  congr 1

/-- The squared norm of each Gaussian factor row equals its prescribed squared scale. -/
theorem tripleFactor_row_variance {p q ρ σ : ℝ} (hρ : ρ ^ 2 ≤ 1)
    (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ) (i : Fin 3) :
    ∑ j, tripleGaussianFactor p q ρ i j ^ 2 = tripleScales σ i ^ 2 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i i) (tripleFactor_gram p q hρ)
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  have hdiag : tripleCovariance p q ρ i i = tripleScales σ i ^ 2 := by
    fin_cases i
    · norm_num [tripleCovariance, tripleScales]
    · norm_num [tripleCovariance, tripleScales]
    · exact hvar.symm
  simpa only [pow_two] using h.trans hdiag

/-- The output Gaussian factor form is the weighted sum of the two input forms. -/
theorem tripleFactor_relation (p q ρ : ℝ) (x : Fin 2 → ℝ) :
    coordinateForm (tripleGaussianFactor p q ρ 2) x =
      p * coordinateForm (tripleGaussianFactor p q ρ 0) x +
        q * coordinateForm (tripleGaussianFactor p q ρ 1) x := by
  simp [coordinateForm_apply, tripleGaussianFactor, Fin.sum_univ_two]
  ring

/-- Ornstein–Uhlenbeck averaging of the lifted triple reduces coordinatewise to scalar averaging. -/
theorem ouFamily_tripleLift {f : Fin 3 → ℝ → ℝ} (hf : ∀ i, Measurable (f i))
    {p q ρ σ : ℝ} (hρ : ρ ^ 2 ≤ 1) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (x : Fin 2 → ℝ) (t : ℝ) (i : Fin 3) :
    ouFamily (tripleLift f p q ρ) (t, x) i =
      scalarOU (f i) (tripleScales σ i) (coordinateForm (tripleGaussianFactor p q ρ i) x) t :=
  ouAverage_comp_coordinateForm (hf i) _ (tripleFactor_row_variance hρ hvar i) x t

/-- The triple scalar gradient records the scalar spatial derivative of each averaged lifted
function. -/
def tripleScalarGradient (f : Fin 3 → ℝ → ℝ) (p q ρ σ t : ℝ) (x : Fin 2 → ℝ) (i : Fin 3) : ℝ :=
  deriv (fun u => scalarOU (f i) (tripleScales σ i) u t) (coordinateForm (tripleGaussianFactor p q ρ
    i) x)

/-- The spatial gradient of each averaged lifted function is its scalar gradient times its Gaussian
factor row. -/
theorem tripleLift_ou_gradient_shape {f : Fin 3 → ℝ → ℝ} (hf : ∀ i, Measurable (f i))
    (hbound : ∀ i z, f i z ∈ Icc (0 : ℝ) 1) {p q ρ σ t : ℝ}
    (hρ : ρ ^ 2 ≤ 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (ht : 0 < t) (x : Fin 2 → ℝ) (i : Fin 3) (j : Fin 2) :
    coordinateDerivative (fun y => ouAverage (tripleLift f p q ρ i) y t) j x =
      tripleScalarGradient f p q ρ σ t x i * tripleGaussianFactor p q ρ i j :=
  coordinateDerivative_ouAverage_comp_coordinateForm (hf i) (hbound i) _
    (tripleScales_pos hσ i) (tripleFactor_row_variance hρ hvar i) x ht j

/-- The scalar half-line estimate supplies the `vᵀDv` bound for the singular correlated triple. -/
theorem triple_ou_gradient_condition {f : Fin 3 → ℝ → ℝ} (hf : ∀ i, Measurable (f i))
    {lo hi p q ρ σ t : ℝ} (hlo : 0 < lo) (hhi : hi < 1)
    (hbound : ∀ i z, f i z ∈ Icc lo hi) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q = 1)
    (hρ : ρ ^ 2 ≤ 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (ht : 0 < t) (x : Fin 2 → ℝ) :
    tripleScalarGradient f p q ρ σ t x ⬝ᵥ
      (interpolationWeightMatrix (tripleInterpolationWeights p q σ) (tripleVariances σ)
        (fun i => gaussianPDFReal 0 1 (gaussianCDFChart.symm (ouFamily (tripleLift f p q ρ) (t, x)
          i))) *ᵥ
          tripleScalarGradient f p q ρ σ t x) ≤ 1 / (Real.exp (2 * t) - 1) := by
  have hbound₀ (i z) : f i z ∈ Icc (0 : ℝ) 1 :=
    ⟨hlo.le.trans (hbound i z).1, (hbound i z).2.trans hhi.le⟩
  apply interpolationWeightMatrix_quadratic_le (tripleInterpolationWeights_nonneg hp hq hσ)
    (sum_tripleInterpolationWeights hsum hσ)
    (fun i => (gaussianPDFReal_pos 0 1 _ (by norm_num)).ne')
  intro i
  have hmean := scalarOU_mem_Icc (hf i) (hbound i) (tripleScales σ i)
    (coordinateForm (tripleGaussianFactor p q ρ i) x) t
  have h := sq_deriv_scalarOU_le_profile (hf i) (hbound₀ i) (tripleScales_pos hσ i) ht
    (coordinateForm (tripleGaussianFactor p q ρ i) x) ⟨hlo.trans_le hmean.1, hmean.2.trans_lt hhi⟩
  rw [ouFamily_tripleLift hf hρ hvar x t i]
  have hv : tripleVariances σ i = tripleScales σ i ^ 2 := by
    fin_cases i <;> norm_num [tripleVariances, tripleScales]
  rw [hv]
  exact h

end EhrhardGaussian.Ehrhard

end
