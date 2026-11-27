/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyWeights
public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyFormula

/-!
# The product-angle and iterated-contour definitions agree

The same actual coefficients and the same actual Cauchy integral are
obtained from either order of integration. Uniform boundary bounds and
continuity discharge joint integrability at each Fubini step.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

theorem angularPolydiscCoefficient_succ (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (F : (Fin (n + 1) → ℂ) → ℂ)
    (hcont : Continuous (fun θ => F (polydiscBoundaryPoint (n + 1) R θ)))
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M) (k : Fin (n + 1) → ℕ) :
    angularPolydiscCoefficient (n + 1) R F k = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t, (circleMap 0 R t)⁻¹ ^ k 0 * angularPolydiscCoefficient n R
        (fun z => F (Fin.cons (circleMap 0 R t) z)) (fun j => k j.succ)
        ∂circleAngleMeasure := by
  unfold angularPolydiscCoefficient
  rw [polydiscAngularIntegral_succ n hR.le _
    (continuous_boundary_coefficient_weight (n + 1) hR F hcont k)
    (M := M * ∏ j, R⁻¹ ^ k j) (by
      intro z hz
      simp only [norm_mul, norm_prod, norm_pow, norm_inv, hz]
      exact mul_le_mul_of_nonneg_right (hF z hz) (by positivity))]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have heq (z : Fin n → ℂ) :
      F (Fin.cons (circleMap 0 R t) z) * ∏ j : Fin (n + 1),
        (Fin.cons (circleMap 0 R t) z j)⁻¹ ^ k j =
      (circleMap 0 R t)⁻¹ ^ k 0 *
        (F (Fin.cons (circleMap 0 R t) z) * ∏ j : Fin n, (z j)⁻¹ ^ k j.succ) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  simp only [heq, polydiscAngularIntegral_const_mul]

theorem angularPolydiscCoefficient_eq (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (F : (Fin n → ℂ) → ℂ)
    (hcont : Continuous (fun θ => F (polydiscBoundaryPoint n R θ)))
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M) (k : Fin n → ℕ) :
    angularPolydiscCoefficient n R F k = polydiscCoefficient n R F k := by
  induction n with
  | zero => simp [angularPolydiscCoefficient, polydiscAngularIntegral_zero, polydiscCoefficient]
  | succ n ih =>
    rw [angularPolydiscCoefficient_succ n hR F hcont hF k,
      polydiscCoefficient, circleCoefficient_eq_angle hR]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    apply ih
    · exact polydiscBoundaryPoint_slice_continuous n R t F hcont
    · intro z hz
      apply hF (Fin.cons (circleMap 0 R t) z)
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa only [Fin.cons_zero, polydiscBoundaryPoint]
          using norm_polydiscBoundaryPoint 1 hR.le (fun _ => t) 0
      · simpa only [Fin.cons_succ] using hz i

theorem angularPolydiscCauchy_succ (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin (n + 1) → ℂ) → ℂ)
    (hcont : Continuous (fun θ => F (polydiscBoundaryPoint (n + 1) R θ)))
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M)
    (x : Fin (n + 1) → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    angularPolydiscCauchy (n + 1) R F x = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t, (1 - x 0 / circleMap 0 R t)⁻¹ * angularPolydiscCauchy n R
        (fun z => F (Fin.cons (circleMap 0 R t) z)) (fun j => x j.succ)
        ∂circleAngleMeasure := by
  unfold angularPolydiscCauchy
  rw [polydiscAngularIntegral_succ n hR.le _
    (continuous_boundary_cauchy_weight (n + 1) hR F hcont x hx)
    (boundary_cauchy_weight_norm_le (n + 1) hR hM F hF x hx)]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have heq (z : Fin n → ℂ) :
      F (Fin.cons (circleMap 0 R t) z) * ∏ j : Fin (n + 1),
        (1 - x j / (Fin.cons (circleMap 0 R t) z : Fin (n + 1) → ℂ) j)⁻¹ =
      (1 - x 0 / circleMap 0 R t)⁻¹ *
        (F (Fin.cons (circleMap 0 R t) z) * ∏ j : Fin n, (1 - x j.succ / z j)⁻¹) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  simp only [heq, polydiscAngularIntegral_const_mul]

theorem angularPolydiscCauchy_eq (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hcont : Continuous (fun θ => F (polydiscBoundaryPoint n R θ)))
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    angularPolydiscCauchy n R F x = polydiscCauchyTransform n R F x := by
  induction n with
  | zero => simp [angularPolydiscCauchy, polydiscAngularIntegral_zero, polydiscCauchyTransform]
  | succ n ih =>
    rw [angularPolydiscCauchy_succ n hR hM F hcont hF x hx]
    change _ = (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(0, R),
      (z - x 0)⁻¹ * polydiscCauchyTransform n R
        (fun w => F (Fin.cons z w)) (fun j => x j.succ)
    rw [normalized_circleCauchy_eq_angle hR _ _ (hx 0)]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    apply ih
    · exact polydiscBoundaryPoint_slice_continuous n R t F hcont
    · intro z hz
      apply hF (Fin.cons (circleMap 0 R t) z)
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa only [Fin.cons_zero, polydiscBoundaryPoint]
          using norm_polydiscBoundaryPoint 1 hR.le (fun _ => t) 0
      · simpa only [Fin.cons_succ] using hz i
    · exact fun j => hx j.succ

end VacuumBellSeparation.Gaussian
