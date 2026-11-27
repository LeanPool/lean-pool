/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.MultivariateCoefficientNorm
public import LeanPool.VacuumBellSeparation.Polynomial.TotalDegreeCauchy

/-!
# Actual multivariable Taylor polynomials and affine coefficient bounds

The polynomial has the contour coefficients, followed by an explicit
coordinatewise affine substitution. Its evaluation is exactly the
previous finite Taylor sum. Degree and coefficient l1 bounds concern
the actual polynomial, including cancellation and zero coefficients.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace VacuumBellSeparation
open Gaussian MvPolynomial

/-- Literal affine substitution into the contour Taylor polynomial. -/
def cauchyTaylorPolynomial (d N : ℕ) (R : ℝ) (F : (Fin d → ℂ) → ℂ)
    (a b : Fin d → ℂ) : MvPolynomial (Fin d) ℂ :=
  ∑ k ∈ multiIndexBelow d N, C (polydiscCoefficient d R F k) *
    ∏ j, (C (a j) * X j + C (b j)) ^ k j

theorem eval_cauchyTaylorPolynomial (d N : ℕ) (R : ℝ) (F : (Fin d → ℂ) → ℂ)
    (a b z : Fin d → ℂ) :
    eval z (cauchyTaylorPolynomial d N R F a b) =
      cauchyTaylor d N R F (fun j => a j * z j + b j) := by
  simp [cauchyTaylorPolynomial, cauchyTaylor]

theorem cauchyTaylorPolynomial_totalDegree_le (d N : ℕ) (R : ℝ)
    (F : (Fin d → ℂ) → ℂ) (a b : Fin d → ℂ) :
    (cauchyTaylorPolynomial d N R F a b).totalDegree ≤ N := by
  classical
  have hlin (j : Fin d) : (C (a j) * X j + C (b j) : MvPolynomial (Fin d) ℂ).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simp)
    · simp
  apply totalDegree_finsetSum_le
  intro k hk
  have hkN := (mem_multiIndexBelow k).mp hk
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun j _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hlin j))))
  simpa only [mul_one] using hkN.le

/-- A finite total-degree power sum, without a polynomial coefficient count. -/
theorem sum_totalDegree_power_le (d N : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    (∑ k ∈ multiIndexBelow d N, B ^ (∑ j, k j)) ≤ (2 * B) ^ N * 2 ^ d := by
  classical
  have hg := (hasSum_half_multiIndex d).mul_left ((2 * B) ^ N)
  calc
    _ ≤ ∑ k ∈ multiIndexBelow d N,
        (2 * B) ^ N * (1 / 2 : ℝ) ^ (∑ j, k j) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := (mem_multiIndexBelow k).mp hk
      calc
        _ = (2 * B) ^ (∑ j, k j) * (1 / 2 : ℝ) ^ (∑ j, k j) := by
          rw [← mul_pow]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by linarith) hkN.le) (by positivity)
    _ ≤ ∑' k : Fin d → ℕ, (2 * B) ^ N * (1 / 2 : ℝ) ^ (∑ j, k j) :=
      hg.summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ = _ := hg.tsum_eq

/-- Coefficient norm after an affine change of coordinates. -/
theorem cauchyTaylorPolynomial_coefficientNorm_le (d N : ℕ) {R M H : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (F : (Fin d → ℂ) → ℂ)
    (hbound : ∀ z ∈ coordinateClosedPolydisc d R, ‖F z‖ ≤ M)
    (a b : Fin d → ℂ) (hab : ∀ j, ‖a j‖ + ‖b j‖ ≤ H) :
    mvCoefficientNorm (cauchyTaylorPolynomial d N R F a b) ≤
      M * (2 * max 1 (H / R)) ^ N * 2 ^ d := by
  classical
  have hcoeff (k : Fin d → ℕ) :
      ‖polydiscCoefficient d R F k‖ ≤ M * R⁻¹ ^ (∑ j, k j) := by
    simpa only [Finset.prod_pow_eq_pow_sum] using
      polydiscCoefficient_norm_le d hR hM F hbound k
  have hlin (j : Fin d) :
      mvCoefficientNorm (C (a j) * X j + C (b j) : MvPolynomial (Fin d) ℂ) ≤ H :=
    (mvCoefficientNorm_affine_le _ _ _).trans (hab j)
  have hterm (k : Fin d → ℕ) :
      mvCoefficientNorm (C (polydiscCoefficient d R F k) *
        ∏ j, (C (a j) * X j + C (b j)) ^ k j) ≤ M * max 1 (H / R) ^ (∑ j, k j) := by
    calc
      _ ≤ ‖polydiscCoefficient d R F k‖ *
          mvCoefficientNorm (∏ j, (C (a j) * X j + C (b j)) ^ k j) := by
        simpa only [mvCoefficientNorm_C] using mvCoefficientNorm_mul_le
          (C (polydiscCoefficient d R F k)) (∏ j, (C (a j) * X j + C (b j)) ^ k j)
      _ ≤ (M * R⁻¹ ^ (∑ j, k j)) * (∏ j, H ^ k j) := by
        apply mul_le_mul (hcoeff k) _ (mvCoefficientNorm_nonneg _) (by positivity)
        apply (mvCoefficientNorm_prod_le _ _).trans
        apply Finset.prod_le_prod₀
        · intro j _
          exact mvCoefficientNorm_nonneg _
        · intro j _
          exact (mvCoefficientNorm_pow_le _ _).trans
            (pow_le_pow_left₀ (mvCoefficientNorm_nonneg _) (hlin j) _)
      _ = M * (H / R) ^ (∑ j, k j) := by
        rw [Finset.prod_pow_eq_pow_sum, mul_assoc, ← mul_pow]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hH hR.le) (le_max_right _ _) _) hM
  calc
    _ ≤ ∑ k ∈ multiIndexBelow d N,
        mvCoefficientNorm (C (polydiscCoefficient d R F k) *
          ∏ j, (C (a j) * X j + C (b j)) ^ k j) := mvCoefficientNorm_sum_le _ _
    _ ≤ ∑ k ∈ multiIndexBelow d N, M * max 1 (H / R) ^ (∑ j, k j) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = M * ∑ k ∈ multiIndexBelow d N, max 1 (H / R) ^ (∑ j, k j) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ M * ((2 * max 1 (H / R)) ^ N * 2 ^ d) :=
      mul_le_mul_of_nonneg_left (sum_totalDegree_power_le d N (le_max_left _ _)) hM
    _ = _ := by ring

end VacuumBellSeparation
