/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Gaussian.GaussianPolynomial

/-! # Gaussian integration by parts with automatic polynomial integrability -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace EhrhardGaussian.Gaussian

/-- Convert Gaussian integrability to Lebesgue integrability with the product density. -/
theorem integrable_standardGaussian_weight {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f (standardGaussianMeasure n)) :
    Integrable (fun x => f x * standardGaussianDensityReal x) volume := by
  rw [standardGaussianMeasure_eq_withDensity] at hf
  rw [integrable_withDensity_iff_integrable_smul' measurable_standardGaussianDensity
    (ae_of_all _ fun _ => ENNReal.prod_lt_top fun _ _ => gaussianPDF_lt_top)] at hf
  simpa only [standardGaussianDensity_toReal, smul_eq_mul, mul_comm] using hf

/-- The coordinatewise IBP identity for `C¹` functions with polynomially bounded first derivative.
All integrability requirements of the density proof follow from Gaussian moments. -/
theorem standardGaussian_integration_by_parts {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (i : Fin n) :
    ∫ x, x i * f x ∂standardGaussianMeasure n =
      ∫ x, coordinateDerivative f i x ∂standardGaussianMeasure n := by
  have : IsGaussian (standardGaussianMeasure n) := isGaussian_standardGaussianMeasure n
  obtain ⟨C, N, hC, hb⟩ := hgrowth
  have hf2 : MemLp f 2 (standardGaussianMeasure n) := by
    apply memLp_of_polynomial_bound_gaussian hcont.continuous.measurable.aestronglyMeasurable
    exact ⟨C, N, hC, fun x => (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)⟩
  have hd2 (j : Fin n) : MemLp (coordinateDerivative f j) 2 (standardGaussianMeasure n) := by
    apply memLp_of_polynomial_bound_gaussian
    · have hc := hcont.continuous_fderiv_apply one_ne_zero
      exact (hc.comp (by fun_prop : Continuous
        (fun x : Fin n → ℝ => (x, Pi.single j (1 : ℝ))))).measurable.aestronglyMeasurable
    · refine ⟨C, N, hC, fun x => ?_⟩
      have hn : ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
        rw [Pi.norm_single]
        exact norm_one
      have h := (fderiv ℝ f x).le_opNorm (Pi.single j 1)
      rw [hn, mul_one] at h
      exact h.trans ((le_add_of_nonneg_left (abs_nonneg (f x))).trans (hb x))
  have hx2 (j : Fin n) : MemLp (fun x : Fin n → ℝ => x j) 2
      (standardGaussianMeasure n) := by
    apply memLp_of_polynomial_bound_gaussian (measurable_pi_apply j).aestronglyMeasurable
    refine ⟨1, 1, zero_le_one, fun x => ?_⟩
    simpa only [one_mul, pow_one, ← Real.norm_eq_abs] using
      (norm_le_pi_norm x j).trans (le_add_of_nonneg_left zero_le_one)
  exact standardGaussianIntegrationByParts hcont
    (integrable_standardGaussian_weight (hf2.integrable (by norm_num)))
    (fun j => integrable_standardGaussian_weight ((hd2 j).integrable (by norm_num)))
    (fun j => integrable_standardGaussian_weight ((hx2 j).integrable_mul hf2)) i

end EhrhardGaussian.Gaussian

end
