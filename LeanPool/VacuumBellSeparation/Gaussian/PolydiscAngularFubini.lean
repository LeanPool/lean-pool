/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscAngularIntegral

/-!
# Fubini and the exact contour normalization

The finite product-angle integral is related to one actual outer circle
and the remaining product integral. All uses of Fubini below include a
genuine joint integrability proof.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

theorem polydiscAngle_integral_succ (n : ℕ) (g : (Fin (n + 1) → ℝ) → ℂ)
    (hg : Integrable g (polydiscAngleMeasure (n + 1))) :
    (∫ θ, g θ ∂polydiscAngleMeasure (n + 1)) =
      ∫ t, ∫ θ, g (Fin.cons t θ) ∂polydiscAngleMeasure n ∂circleAngleMeasure := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => circleAngleMeasure) 0).symm
  have heq (p : ℝ × (Fin n → ℝ)) : e p = Fin.cons p.1 p.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => g (Fin.cons p.1 p.2))
      (circleAngleMeasure.prod (polydiscAngleMeasure n)) := by
    have hi := he.integrable_comp_of_integrable hg
    change Integrable (fun p => g (e p))
      (circleAngleMeasure.prod (polydiscAngleMeasure n)) at hi
    simpa only [heq] using hi
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), g (Fin.cons p.1 p.2)
        ∂circleAngleMeasure.prod (polydiscAngleMeasure n) := by
      change (∫ θ, g θ ∂Measure.pi (fun _ : Fin (n + 1) => circleAngleMeasure)) = _
      rw [← he.integral_comp']
      change (∫ p, g (e p) ∂circleAngleMeasure.prod (polydiscAngleMeasure n)) = _
      simp only [heq]
    _ = _ := integral_prod _ hint

theorem polydiscAngularIntegral_zero (R : ℝ) (F : (Fin 0 → ℂ) → ℂ) :
    polydiscAngularIntegral 0 R F = F Fin.elim0 := by
  have h (θ : Fin 0 → ℝ) : polydiscBoundaryPoint 0 R θ = Fin.elim0 := by
    funext j
    exact Fin.elim0 j
  simp only [polydiscAngularIntegral, h, integral_const, measureReal_def,
    polydiscAngleMeasure, Measure.pi_univ, Finset.univ_eq_empty,
    Finset.prod_empty, ENNReal.toReal_one, one_smul, pow_zero, inv_one, one_mul]

theorem polydiscAngularIntegral_succ (n : ℕ) {R M : ℝ} (hR : 0 ≤ R)
    (F : (Fin (n + 1) → ℂ) → ℂ)
    (hcont : Continuous (fun θ => F (polydiscBoundaryPoint (n + 1) R θ)))
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M) :
    polydiscAngularIntegral (n + 1) R F = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t, polydiscAngularIntegral n R (fun z => F (Fin.cons (circleMap 0 R t) z))
        ∂circleAngleMeasure := by
  have hi := integrable_polydiscBoundary (n + 1) hR F hcont hF
  have heq (t : ℝ) (θ : Fin n → ℝ) :
      polydiscBoundaryPoint (n + 1) R (Fin.cons t θ) =
        Fin.cons (circleMap 0 R t) (polydiscBoundaryPoint n R θ) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> rfl
  unfold polydiscAngularIntegral
  rw [polydiscAngle_integral_succ n _ hi]
  simp only [heq, integral_const_mul]
  rw [pow_succ, mul_inv_rev]
  ring

theorem circleCoefficient_eq_angle {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℂ) (k : ℕ) :
    circleCoefficient R f k = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t, (circleMap 0 R t)⁻¹ ^ k * f (circleMap 0 R t) ∂circleAngleMeasure := by
  have hz (t : ℝ) : circleMap 0 R t ≠ 0 := circleMap_ne_center hR.ne'
  have hi (t : ℝ) : deriv (circleMap 0 R) t *
      ((circleMap 0 R t)⁻¹ ^ k * ((circleMap 0 R t)⁻¹ * f (circleMap 0 R t))) =
      I * ((circleMap 0 R t)⁻¹ ^ k * f (circleMap 0 R t)) := by
    rw [deriv_circleMap]
    field_simp [hz t]
  simp only [circleCoefficient, circleIntegral, smul_eq_mul, hi,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, circleAngleMeasure,
    integral_const_mul]
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  field_simp

theorem normalized_circleCauchy_eq_angle {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℂ) (x : ℂ) (hx : ‖x‖ < R) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, R), (z - x)⁻¹ * f z) =
      (2 * Real.pi : ℂ)⁻¹ *
        ∫ t, (1 - x / circleMap 0 R t)⁻¹ * f (circleMap 0 R t) ∂circleAngleMeasure := by
  have hz (t : ℝ) : circleMap 0 R t ≠ 0 := circleMap_ne_center hR.ne'
  have hzx (t : ℝ) : circleMap 0 R t - x ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hn : ‖circleMap 0 R t‖ = R := by simp [abs_of_pos hR]
    rw [heq] at hn
    linarith
  have hi (t : ℝ) : deriv (circleMap 0 R) t *
      ((circleMap 0 R t - x)⁻¹ * f (circleMap 0 R t)) =
      I * ((1 - x / circleMap 0 R t)⁻¹ * f (circleMap 0 R t)) := by
    rw [deriv_circleMap]
    field_simp [hz t, hzx t]
  simp only [circleIntegral, smul_eq_mul, hi,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, circleAngleMeasure,
    integral_const_mul]
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  field_simp

end VacuumBellSeparation.Gaussian
