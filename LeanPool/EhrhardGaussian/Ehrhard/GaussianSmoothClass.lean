/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott N. Armstrong
-/

/-
Adapted from ASDExplicitGamma-dev/Gaussian/FiniteProduct.lean,
commit 2c9673f0bcca8062b441989bdc56f87b38715bb8.
Modified for EhrhardGaussian, 2026.
-/
module

public import LeanPool.EhrhardGaussian.Gaussian.IntegrationByParts

/-! Polynomial growth classes justify Gaussian integration by parts and semigroup differentiation.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- A `C¹` function with a common polynomial bound for its value and
coordinate derivatives. -/
def HasPolynomiallyBoundedCoordinateDerivatives {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    (∀ x, |F x| ≤ C * (1 + ‖x‖) ^ d) ∧
    ∀ i x, |F x| + |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d

/-- Gaussian moments supply all polynomial domination needed for integrability. -/
theorem integrable_of_pi_polynomial_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hg : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) :
    Integrable f (standardGaussianMeasure n) := by
  have := EhrhardGaussian.Gaussian.isGaussian_standardGaussianMeasure n
  exact (EhrhardGaussian.Gaussian.memLp_of_polynomial_bound_gaussian hf.aestronglyMeasurable
    ⟨C, d, hC, hg⟩).integrable (by norm_num)

private theorem fderiv_coordinate_bound {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (x : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i, |coordinateDerivative F i x| ≤ B) :
    ‖fderiv ℝ F x‖ ≤ (n : ℝ) * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro v
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  have heq : fderiv ℝ F x v = ∑ i, v i * coordinateDerivative F i x := by
    rw [hv, map_sum]
    simp [coordinateDerivative, smul_eq_mul, Pi.single_apply]
  rw [heq, Real.norm_eq_abs]
  calc
    |∑ i, v i * coordinateDerivative F i x| ≤ ∑ i, |v i * coordinateDerivative F i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (hcoord i) (abs_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * B * ‖v‖ := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring

/-- The common coordinate bound controls the full derivative norm. -/
theorem polynomiallySmooth_opNorm_bound {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x, |F x| + ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ N := by
  obtain ⟨_, C, hC, d, hvalue, hfirst⟩ := hF
  refine ⟨(n + 1) * C, d, mul_nonneg (by positivity) hC, ?_⟩
  intro x
  have hb : 0 ≤ C * (1 + ‖x‖) ^ d := mul_nonneg hC (pow_nonneg (by positivity) _)
  have hd := fderiv_coordinate_bound x hb (fun j =>
    (le_add_of_nonneg_left (abs_nonneg (F x))).trans (hfirst j x))
  calc
    |F x| + ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ d + n * (C * (1 + ‖x‖) ^ d) :=
      add_le_add (hvalue x) hd
    _ = (n + 1) * C * (1 + ‖x‖) ^ d := by ring


/-- Integration by parts for the polynomially smooth test class. -/
theorem integral_eval_mul_eq_integral_coordinateDerivative {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : HasPolynomiallyBoundedCoordinateDerivatives F) (i : Fin n) :
    ∫ x, x i * F x ∂standardGaussianMeasure n =
      ∫ x, coordinateDerivative F i x ∂standardGaussianMeasure n :=
  EhrhardGaussian.Gaussian.standardGaussian_integration_by_parts hF.1
    (polynomiallySmooth_opNorm_bound hF) i

end EhrhardGaussian.Ehrhard

end
