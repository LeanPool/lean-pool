/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ScalarLinearDerivatives

/-! # Bounded scalar derivatives supply the regularity of the lifted inputs -/

@[expose] public noncomputable section

open EhrhardGaussian.Gaussian (coordinateDerivative)

namespace EhrhardGaussian.Ehrhard

/-- Each coefficient of a linear form is bounded by its operator norm. -/
theorem abs_coordinate_le_norm_coordinateForm {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    |c i| ≤ ‖coordinateForm c‖ := by
  simpa only [coordinateForm_single, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
    (coordinateForm c).le_opNorm (Pi.single i 1)

/-- A scalar derivative bound controls the derivative of its composition with a linear form. -/
theorem norm_fderiv_scalar_comp_le {n : ℕ} {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {G : ℝ} (hgrad : ∀ y, |deriv f y| ≤ G) (c : Fin n → ℝ) (x : Fin n → ℝ) :
    ‖fderiv ℝ (f ∘ coordinateForm c) x‖ ≤ G * ‖coordinateForm c‖ := by
  rw [(hasFDerivAt_scalar_comp c x (hf _)).fderiv, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hgrad _) (norm_nonneg _)

/-- Bounded scalar derivatives through order three give polynomial derivative bounds after linear
pullback. -/
theorem hasPolynomiallyBoundedThird_scalar_comp {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) {B G H J : ℝ} (hB : 0 ≤ B) (hG : 0 ≤ G) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hvalue : ∀ y, |f y| ≤ B) (hgrad : ∀ y, |deriv f y| ≤ G)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ H) (hthird : ∀ y, |deriv (deriv (deriv f)) y| ≤ J)
    (c : Fin n → ℝ) : HasPolynomiallyBoundedThirdCoordinateDerivatives (f ∘ coordinateForm c) := by
  let N := ‖coordinateForm c‖
  let C := B + N * G + N ^ 2 * H + N ^ 3 * J
  have hN : 0 ≤ N := norm_nonneg _
  have h₁ : 0 ≤ N * G := mul_nonneg hN hG
  have h₂ : 0 ≤ N ^ 2 * H := mul_nonneg (sq_nonneg _) hH
  have h₃ : 0 ≤ N ^ 3 * J := by positivity
  have hC : 0 ≤ C := by dsimp only [C]; linarith only [hB, h₁, h₂, h₃]
  have hc (i) : |c i| ≤ N := abs_coordinate_le_norm_coordinateForm c i
  have hcc (i j) : |c i * c j| ≤ N ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hc i) (hc j) (abs_nonneg _) hN
  have hccc (i j k) : |c i * c j * c k| ≤ N ^ 3 := by
    rw [abs_mul]
    exact (mul_le_mul (hcc i j) (hc k) (abs_nonneg _) (sq_nonneg _)).trans_eq (by ring)
  refine ⟨hf.comp (coordinateForm c).contDiff, C, hC, 0, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [pow_zero, mul_one, Function.comp_apply]
    exact (hvalue _).trans (by dsimp only [C]; linarith only [h₁, h₂, h₃])
  · intro i x
    simp only [pow_zero, mul_one]
    rw [coordinateDerivative_scalar_comp (hf.differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0)),
      abs_mul]
    exact (mul_le_mul (hc i) (hgrad _) (abs_nonneg _) hN).trans
      (by dsimp only [C]; linarith only [hB, h₂, h₃])
  · intro i j x
    simp only [pow_zero, mul_one]
    rw [secondCoordinateDerivative_scalar_comp (hf.of_le (by norm_num)), abs_mul]
    exact (mul_le_mul (hcc i j) (hsecond _) (abs_nonneg _) (sq_nonneg _)).trans
      (by dsimp only [C]; linarith only [hB, h₁, h₃])
  · intro i j k x
    simp only [pow_zero, mul_one]
    rw [thirdCoordinateDerivative_scalar_comp hf, abs_mul]
    exact (mul_le_mul (hccc i j k) (hthird _) (abs_nonneg _) (by positivity)).trans
      (by dsimp only [C]; linarith only [hB, h₁, h₂])

/-- Scalar second derivative and weighted first derivative bounds control the generator of a linear
pullback. -/
theorem abs_ouGenerator_scalar_comp_le {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {H M : ℝ} (hsecond : ∀ y, |deriv (deriv f) y| ≤ H)
    (hweighted : ∀ y, |y * deriv f y| ≤ M) (c : Fin n → ℝ) (x : Fin n → ℝ) :
    |ouGenerator (f ∘ coordinateForm c) x| ≤ (∑ i, c i ^ 2) * H + M := by
  rw [ouGenerator_scalar_comp hf]
  calc
    _ ≤ |(∑ i, c i ^ 2) * deriv (deriv f) (coordinateForm c x)| +
        |coordinateForm c x * deriv f (coordinateForm c x)| := by
      simpa only [abs_neg, sub_eq_add_neg] using abs_add_le
        ((∑ i, c i ^ 2) * deriv (deriv f) (coordinateForm c x))
        (-(coordinateForm c x * deriv f (coordinateForm c x)))
    _ = (∑ i, c i ^ 2) * |deriv (deriv f) (coordinateForm c x)| +
        |coordinateForm c x * deriv f (coordinateForm c x)| := by
      rw [abs_mul, abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg (c i)))]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (hsecond _) (Finset.sum_nonneg (fun i _ => sq_nonneg (c i))))
        (hweighted _)

end EhrhardGaussian.Ehrhard

end
