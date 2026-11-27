/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.JointMidpointPolynomialDefs
public import LeanPool.VacuumBellSeparation.Polynomial.MultivariateCauchyPolynomial
public import LeanPool.VacuumBellSeparation.Polynomial.MultivariateSelector
public import LeanPool.VacuumBellSeparation.Polynomial.SelectorTaylorBounds

/-!
# The actual joint polynomial in midpoint coordinates

The six variables are (x-s e₀/2)/s and (y-s e₀/2)/s.
The oriented polynomial is the original pair of selectors times the
actual Taylor polynomial; the joint kernel is its negative symmetrization.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace VacuumBellSeparation
open Gaussian MvPolynomial

@[simp] theorem swapSpatialSix_involution (j : Fin 6) : swapSpatialSix (swapSpatialSix j) = j := by
  fin_cases j <;> rfl

theorem eval_jointMidpointOriented (F : (Fin 6 → ℂ) → ℂ) (n : ℕ) (z : Fin 6 → ℂ) :
    eval z (jointMidpointOriented F n) =
      selectedCauchyTaylor n (1 / 100) F (z 0 + 1 / 2) (1 / 2 - z 3)
        (fun j => z j + jointMidpointShift j) := by
  simp only [jointMidpointOriented, eval_mul, eval_realPolynomialSubstitution,
    eval_cauchyTaylorPolynomial, jointMidpointLeft, jointMidpointRight,
    eval_add, eval_mul, eval_C, eval_X, one_mul, neg_one_mul, selectedCauchyTaylor]
  congr 2
  ring_nf

theorem eval_jointMidpointPolynomial_symmetric (F : (Fin 6 → ℂ) → ℂ)
    (n : ℕ) (z : Fin 6 → ℂ) :
    eval (z ∘ swapSpatialSix) (jointMidpointPolynomial F n) =
      eval z (jointMidpointPolynomial F n) := by
  have hi : (z ∘ swapSpatialSix) ∘ swapSpatialSix = z := by
    funext j
    simp only [Function.comp_apply, swapSpatialSix_involution]
  simp only [jointMidpointPolynomial, map_neg, map_add, eval_rename, hi]
  ring

theorem jointMidpointLeft_degree : jointMidpointLeft.totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by simp)
  · simp

theorem jointMidpointRight_degree : jointMidpointRight.totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by simp)
  · simp

theorem jointMidpointOriented_degree (F : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    (jointMidpointOriented F n).totalDegree ≤ 9 * n := by
  have hl := selectorSubstitution_totalDegree_le (2 * n) jointMidpointLeft jointMidpointLeft_degree
  have hr := selectorSubstitution_totalDegree_le
    (2 * n) jointMidpointRight jointMidpointRight_degree
  have ht := cauchyTaylorPolynomial_totalDegree_le 6 n (1 / 100) F (fun _ => 1) jointMidpointShift
  have h1 := totalDegree_mul (realPolynomialSubstitution (selector (2 * n)) jointMidpointLeft)
    (realPolynomialSubstitution (selector (2 * n)) jointMidpointRight)
  have h2 := totalDegree_mul
    (realPolynomialSubstitution (selector (2 * n)) jointMidpointLeft *
      realPolynomialSubstitution (selector (2 * n)) jointMidpointRight)
    (cauchyTaylorPolynomial 6 n (1 / 100) F (fun _ => 1) jointMidpointShift)
  unfold jointMidpointOriented
  omega

theorem jointMidpointPolynomial_degree (F : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    (jointMidpointPolynomial F n).totalDegree ≤ 9 * n := by
  unfold jointMidpointPolynomial
  rw [totalDegree_neg]
  apply (totalDegree_add _ _).trans
  exact max_le (jointMidpointOriented_degree F n)
    ((totalDegree_rename_le _ _).trans (jointMidpointOriented_degree F n))

theorem jointMidpointLeft_coefficientNorm : mvCoefficientNorm jointMidpointLeft ≤ 2 := by
  have h := mvCoefficientNorm_affine_le (σ := Fin 6) (1 : ℂ) (1 / 2) 0
  norm_num at h
  simpa [jointMidpointLeft] using h.trans (show (3 / 2 : ℝ) ≤ 2 by norm_num)

theorem jointMidpointRight_coefficientNorm : mvCoefficientNorm jointMidpointRight ≤ 2 := by
  have h := mvCoefficientNorm_affine_le (σ := Fin 6) (-1 : ℂ) (1 / 2) 3
  norm_num at h
  simpa [jointMidpointRight] using h.trans (show (3 / 2 : ℝ) ≤ 2 by norm_num)

theorem jointMidpointOriented_coefficientNorm {M : ℝ} (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M) (n : ℕ) :
    mvCoefficientNorm (jointMidpointOriented F n) ≤ 64 * M * (314572800 : ℝ) ^ n := by
  have hshift (j : Fin 6) : ‖(1 : ℂ)‖ + ‖jointMidpointShift j‖ ≤ (3 / 2 : ℝ) := by
    unfold jointMidpointShift
    split_ifs <;> norm_num
  have ht := cauchyTaylorPolynomial_coefficientNorm_le 6 n (R := 1 / 100)
    (by norm_num) hM (show (0 : ℝ) ≤ 3 / 2 by norm_num) F hbound
    (fun _ => 1) jointMidpointShift hshift
  norm_num at ht
  have hl := selectorSubstitution_coefficientNorm_le
    (2 * n) jointMidpointLeft jointMidpointLeft_coefficientNorm
  have hr := selectorSubstitution_coefficientNorm_le
    (2 * n) jointMidpointRight jointMidpointRight_coefficientNorm
  unfold jointMidpointOriented
  calc
    _ ≤ (mvCoefficientNorm (realPolynomialSubstitution (selector (2 * n)) jointMidpointLeft) *
        mvCoefficientNorm (realPolynomialSubstitution (selector (2 * n)) jointMidpointRight)) *
          mvCoefficientNorm (cauchyTaylorPolynomial 6 n (1 / 100) F
            (fun _ => 1) jointMidpointShift) :=
      (mvCoefficientNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (mvCoefficientNorm_mul_le _ _) (mvCoefficientNorm_nonneg _))
    _ ≤ (32 ^ (2 * n) * 32 ^ (2 * n)) * (M * 300 ^ n * 64) := by
      gcongr <;> exact mvCoefficientNorm_nonneg _
    _ = 64 * M * (((32 : ℝ) ^ 2 * 32 ^ 2) * 300) ^ n := by
      simp only [mul_pow, pow_mul]
      ring
    _ = _ := by norm_num

theorem jointMidpointPolynomial_coefficientNorm {M : ℝ} (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M) (n : ℕ) :
    mvCoefficientNorm (jointMidpointPolynomial F n) ≤ 128 * M * (314572800 : ℝ) ^ n := by
  unfold jointMidpointPolynomial
  rw [mvCoefficientNorm_neg]
  have hb := jointMidpointOriented_coefficientNorm hM F hbound n
  have hr := mvCoefficientNorm_rename_le swapSpatialSix (jointMidpointOriented F n)
  exact (mvCoefficientNorm_add_le _ _).trans (by linarith)

end VacuumBellSeparation
