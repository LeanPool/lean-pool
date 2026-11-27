/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyCoefficients
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialSeriesConstants

/-!
# Absolute convergence of the actual contour coefficient series

These are the coefficients defined by iterated Cauchy integrals. A true
geometric majorant proves absolute convergence at every interior point
and the exact 2^n bound on the half-radius polydisc. Identifying the sum
with the original function is a separate reconstruction theorem.
-/

@[expose] public section

open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

theorem polydiscCoefficient_monomial_norm_le (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, ‖F z‖ ≤ M)
    (k : Fin n → ℕ) (x : Fin n → ℂ) :
    ‖polydiscCoefficient n R F k * ∏ j, x j ^ k j‖ ≤
      M * ∏ j, (‖x j‖ / R) ^ k j := by
  rw [norm_mul, norm_prod]
  simp only [norm_pow]
  calc
    _ ≤ (M * ∏ j, R⁻¹ ^ k j) * ∏ j, ‖x j‖ ^ k j :=
      mul_le_mul_of_nonneg_right (polydiscCoefficient_norm_le n hR hM F hF k)
        (Finset.prod_nonneg (fun _ _ => by positivity))
    _ = M * ∏ j, (‖x j‖ / R) ^ k j := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      rw [← mul_pow]
      congr 1
      ring

theorem summable_norm_polydiscCoefficient_monomial (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    Summable (fun k : Fin n → ℕ =>
      ‖polydiscCoefficient n R F k * ∏ j, x j ^ k j‖) := by
  have hs := hasSum_fin_product_nonneg n
    (fun j m => (‖x j‖ / R) ^ m) (fun j => (1 - ‖x j‖ / R)⁻¹)
    (fun _ _ => by positivity)
    (fun j => hasSum_geometric_of_lt_one (div_nonneg (norm_nonneg _) hR.le)
      ((div_lt_one hR).mpr (hx j)))
  exact (hs.summable.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => polydiscCoefficient_monomial_norm_le n hR hM F hF k x)

theorem polydiscCoefficient_half_monomial_norm_le (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ ≤ R / 2) (k : Fin n → ℕ) :
    ‖polydiscCoefficient n R F k * ∏ j, x j ^ k j‖ ≤
      M * (1 / 2 : ℝ) ^ (∑ j, k j) := by
  apply (polydiscCoefficient_monomial_norm_le n hR hM F hF k x).trans
  rw [← Finset.prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left _ hM
  apply Finset.prod_le_prod₀
  · intro j _
    positivity
  · intro j _
    apply pow_le_pow_left₀ (by positivity)
    exact (div_le_iff₀ hR).mpr (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hx j)

theorem tsum_norm_polydiscCoefficient_half_le (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ ≤ R / 2) :
    (∑' k : Fin n → ℕ, ‖polydiscCoefficient n R F k * ∏ j, x j ^ k j‖) ≤
      M * 2 ^ n := by
  have hx' : ∀ j, ‖x j‖ < R := fun j => (hx j).trans_lt (by linarith)
  have hs := summable_norm_polydiscCoefficient_monomial n hR hM F hF x hx'
  have hg := (hasSum_half_multiIndex n).mul_left M
  calc
    _ ≤ ∑' k : Fin n → ℕ, M * (1 / 2 : ℝ) ^ (∑ j, k j) :=
      hs.tsum_le_tsum (fun k => polydiscCoefficient_half_monomial_norm_le n hR hM F hF x hx k)
        hg.summable
    _ = M * 2 ^ n := hg.tsum_eq

end VacuumBellSeparation.Gaussian
