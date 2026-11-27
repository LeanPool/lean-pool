/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.ComplexSelectorBounds
public import LeanPool.VacuumBellSeparation.Polynomial.TotalDegreeCauchy

/-!
# Selector-weighted actual Taylor approximation

The scalar selectors are evaluated at the two oriented coordinates. The
Taylor polynomial is the actual six-variable contour truncation. Bounds
hold in complex neighborhoods, so subsequent Cauchy differentiation can
be carried out before restricting to real physical coordinates.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace VacuumBellSeparation

open Gaussian

/-- Two selectors of order 2n multiplying the genuine Taylor truncation. -/
def selectedCauchyTaylor (n : ℕ) (R : ℝ) (F : (Fin 6 → ℂ) → ℂ)
    (u v : ℂ) (z : Fin 6 → ℂ) : ℂ :=
  complexPolynomialEval (selector (2 * n)) u *
    complexPolynomialEval (selector (2 * n)) v * cauchyTaylor 6 n R F z

theorem complexSelector_near_zero_norm_le_three (N : ℕ) {z : ℂ} {δ : ℝ}
    (hz : ‖z‖ ≤ δ) (hδ : δ ≤ 1 / 8) :
    ‖complexPolynomialEval (selector N) z‖ ≤ 3 := by
  have hδ₀ := (norm_nonneg z).trans hz
  have hp : (8 * δ) ^ N ≤ (1 : ℝ) := pow_le_one₀ (by positivity) (by linarith)
  have he := norm_complexSelector_near_zero_geometric N hz (by linarith)
  calc
    _ = ‖(complexPolynomialEval (selector N) z - 1) + 1‖ := by congr 1; ring
    _ ≤ ‖complexPolynomialEval (selector N) z - 1‖ + 1 := by
      simpa only [norm_one] using norm_add_le (complexPolynomialEval (selector N) z - 1) (1 : ℂ)
    _ ≤ 3 := by linarith

theorem complexSelector_product_near_zero (N : ℕ) {u v : ℂ} {δ : ℝ}
    (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ δ) (hδ : δ ≤ 1 / 8) :
    ‖complexPolynomialEval (selector N) u * complexPolynomialEval (selector N) v - 1‖ ≤
      8 * (8 * δ) ^ N := by
  let p := complexPolynomialEval (selector N) u
  let q := complexPolynomialEval (selector N) v
  have hp : ‖p‖ ≤ 3 := complexSelector_near_zero_norm_le_three N hu hδ
  have hpu : ‖p - 1‖ ≤ 2 * (8 * δ) ^ N :=
    norm_complexSelector_near_zero_geometric N hu (by linarith)
  have hqv : ‖q - 1‖ ≤ 2 * (8 * δ) ^ N :=
    norm_complexSelector_near_zero_geometric N hv (by linarith)
  change ‖p * q - 1‖ ≤ _
  calc
    _ = ‖p * (q - 1) + (p - 1)‖ := by congr 1; ring
    _ ≤ ‖p‖ * ‖q - 1‖ + ‖p - 1‖ := by simpa only [norm_mul] using norm_add_le (p * (q - 1)) (p - 1)
    _ ≤ 3 * (2 * (8 * δ) ^ N) + 2 * (8 * δ) ^ N := by gcongr
    _ = _ := by ring

/-- On the desired component, both selectors are close to one. -/
theorem selectedCauchyTaylor_desired_error {n : ℕ} {R δ M : ℝ}
    (hR : 0 < R) (hδ : 0 ≤ δ) (hδR : δ ≤ R / 2)
    (hsmall : δ ≤ 1 / 8) (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 R, DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 R, ‖F z‖ ≤ M)
    (u v : ℂ) (z : Fin 6 → ℂ) (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ δ)
    (hz : ∀ j, ‖z j‖ ≤ δ) :
    ‖F z - selectedCauchyTaylor n R F u v z‖ ≤
      M * (576 * (2 * (δ / R)) ^ n + 8 * (8 * δ) ^ (2 * n)) := by
  let p := complexPolynomialEval (selector (2 * n)) u *
    complexPolynomialEval (selector (2 * n)) v
  have hp : ‖p‖ ≤ 9 := by
    dsimp [p]
    rw [norm_mul]
    nlinarith [complexSelector_near_zero_norm_le_three (2 * n) hu hsmall,
      complexSelector_near_zero_norm_le_three (2 * n) hv hsmall,
      norm_nonneg (complexPolynomialEval (selector (2 * n)) u),
      norm_nonneg (complexPolynomialEval (selector (2 * n)) v)]
  have hpe : ‖p - 1‖ ≤ 8 * (8 * δ) ^ (2 * n) :=
    complexSelector_product_near_zero (2 * n) hu hv hsmall
  have hrem := cauchyTaylor_remainder_le 6 n hR hδ hδR hM F hF hbound z hz
  norm_num only [show (2 : ℝ) ^ 6 = 64 by norm_num] at hrem
  have hfz : ‖F z‖ ≤ M := hbound z (fun j => (hz j).trans (by linarith))
  change ‖F z - p * cauchyTaylor 6 n R F z‖ ≤ _
  calc
    _ = ‖p * (F z - cauchyTaylor 6 n R F z) - (p - 1) * F z‖ := by congr 1; ring
    _ ≤ ‖p‖ * ‖F z - cauchyTaylor 6 n R F z‖ + ‖p - 1‖ * ‖F z‖ := by
      simpa only [norm_mul] using norm_sub_le
        (p * (F z - cauchyTaylor 6 n R F z)) ((p - 1) * F z)
    _ ≤ 9 * (M * (2 * (δ / R)) ^ n * 64) +
        (8 * (8 * δ) ^ (2 * n)) * M := by gcongr
    _ = _ := by ring

/-- On an unwanted component a selector has a zero of order 2n. -/
theorem selectedCauchyTaylor_wrong_component {n : ℕ} {R r δ M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 R, ‖F z‖ ≤ M)
    (u v : ℂ) (z : Fin 6 → ℂ) (hu : ‖u‖ ≤ 2) (hv : ‖v‖ ≤ 2)
    (hzero : ‖1 - u‖ ≤ δ ∨ ‖1 - v‖ ≤ δ) (hz : ∀ j, ‖z j‖ ≤ r) :
    ‖selectedCauchyTaylor n R F u v z‖ ≤
      64 * M * ((256 * δ) ^ 2 * (2 * max 1 (r / R))) ^ n := by
  have hδ : 0 ≤ δ := hzero.elim
    (fun h => (norm_nonneg _).trans h) (fun h => (norm_nonneg _).trans h)
  have hp : ‖complexPolynomialEval (selector (2 * n)) u *
      complexPolynomialEval (selector (2 * n)) v‖ ≤ (256 * δ) ^ (2 * n) := by
    rcases hzero with h | h
    · exact norm_complexSelector_product_wrong_component (2 * n) hu hv h
    · simpa only [mul_comm] using norm_complexSelector_product_wrong_component (2 * n) hv hu h
  have ht := cauchyTaylor_norm_le 6 n hR hM F hbound z hz
  norm_num only [show (2 : ℝ) ^ 6 = 64 by norm_num] at ht
  unfold selectedCauchyTaylor
  rw [norm_mul]
  calc
    _ ≤ (256 * δ) ^ (2 * n) * (M * (2 * max 1 (r / R)) ^ n * 64) :=
      mul_le_mul hp ht (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [pow_mul, mul_pow]
      ring

end VacuumBellSeparation
