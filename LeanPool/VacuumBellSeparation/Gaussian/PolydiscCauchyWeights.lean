/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscAngularSeries
public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscAngularFubini

/-!
# Actual boundary continuity and geometric Cauchy weights
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped BigOperators

namespace VacuumBellSeparation.Gaussian

theorem polydiscAngularIntegral_const_mul (n : ℕ) (R : ℝ) (c : ℂ)
    (F : (Fin n → ℂ) → ℂ) :
    polydiscAngularIntegral n R (fun z => c * F z) =
      c * polydiscAngularIntegral n R F := by
  simp only [polydiscAngularIntegral, integral_const_mul]
  ring

theorem polydiscBoundaryPoint_cons (n : ℕ) (R t : ℝ) (θ : Fin n → ℝ) :
    polydiscBoundaryPoint (n + 1) R (Fin.cons t θ) =
      Fin.cons (circleMap 0 R t) (polydiscBoundaryPoint n R θ) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem polydiscBoundaryPoint_slice_continuous (n : ℕ) (R t : ℝ)
    (F : (Fin (n + 1) → ℂ) → ℂ)
    (hF : Continuous (fun θ => F (polydiscBoundaryPoint (n + 1) R θ))) :
    Continuous (fun θ => F (Fin.cons (circleMap 0 R t) (polydiscBoundaryPoint n R θ))) := by
  have hcons : Continuous (fun θ : Fin n → ℝ => (Fin.cons t θ : Fin (n + 1) → ℝ)) := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun i => ?_) j <;> fun_prop
  simpa only [Function.comp_def, polydiscBoundaryPoint_cons] using hF.comp hcons

theorem continuous_boundary_coefficient_weight (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F : (Fin n → ℂ) → ℂ)
    (hF : Continuous (fun θ => F (polydiscBoundaryPoint n R θ)))
    (k : Fin n → ℕ) :
    Continuous (fun θ => F (polydiscBoundaryPoint n R θ) *
      ∏ j, (polydiscBoundaryPoint n R θ j)⁻¹ ^ k j) := by
  apply hF.mul
  apply continuous_finsetProd
  intro j _
  apply Continuous.pow
  apply Continuous.inv₀
  · exact (continuous_apply j).comp (continuous_polydiscBoundaryPoint n R)
  · intro θ
    exact norm_ne_zero_iff.mp (by rw [norm_polydiscBoundaryPoint n hR.le]; exact hR.ne')

theorem cauchyWeight_ne_zero {R : ℝ} (hR : 0 < R) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ = R) : 1 - x / z ≠ 0 := by
  have hq : ‖x / z‖ < 1 := by rw [norm_div, hz]; exact (div_lt_one hR).mpr hx
  intro heq
  have heq' : x / z = 1 := (sub_eq_zero.mp heq).symm
  rw [heq', norm_one] at hq
  exact (lt_irrefl 1) hq

theorem cauchyWeight_norm_le {R : ℝ} (hR : 0 < R) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ = R) :
    ‖(1 - x / z)⁻¹‖ ≤ (1 - ‖x‖ / R)⁻¹ := by
  have hq : 0 < 1 - ‖x‖ / R := sub_pos.mpr ((div_lt_one hR).mpr hx)
  have hlo : 1 - ‖x‖ / R ≤ ‖1 - x / z‖ := by
    simpa only [norm_one, norm_div, hz] using norm_sub_norm_le (1 : ℂ) (x / z)
  rw [norm_inv]
  exact (inv_le_inv₀ (hq.trans_le hlo) hq).mpr hlo

theorem continuous_boundary_cauchy_weight (n : ℕ) {R : ℝ} (hR : 0 < R)
    (F : (Fin n → ℂ) → ℂ)
    (hF : Continuous (fun θ => F (polydiscBoundaryPoint n R θ)))
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R) :
    Continuous (fun θ => F (polydiscBoundaryPoint n R θ) *
      ∏ j, (1 - x j / polydiscBoundaryPoint n R θ j)⁻¹) := by
  apply hF.mul
  apply continuous_finsetProd
  intro j _
  apply Continuous.inv₀
  · apply continuous_const.sub
    apply continuous_const.div
    · exact (continuous_apply j).comp (continuous_polydiscBoundaryPoint n R)
    · intro θ
      exact norm_ne_zero_iff.mp (by rw [norm_polydiscBoundaryPoint n hR.le]; exact hR.ne')
  · intro θ
    exact cauchyWeight_ne_zero hR _ _ (hx j) (norm_polydiscBoundaryPoint n hR.le θ j)

theorem boundary_cauchy_weight_norm_le (n : ℕ) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z, (∀ j, ‖z j‖ = R) → ‖F z‖ ≤ M)
    (x : Fin n → ℂ) (hx : ∀ j, ‖x j‖ < R)
    (z : Fin n → ℂ) (hz : ∀ j, ‖z j‖ = R) :
    ‖F z * ∏ j, (1 - x j / z j)⁻¹‖ ≤ M * ∏ j, (1 - ‖x j‖ / R)⁻¹ := by
  rw [norm_mul, norm_prod]
  apply mul_le_mul (hF z hz) _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hM
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  exact fun j _ => cauchyWeight_norm_le hR _ _ (hx j) (hz j)

end VacuumBellSeparation.Gaussian
