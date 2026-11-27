/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointFourierSupportBound
public import LeanPool.VacuumBellSeparation.FreeField.Lorentz
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Uniform low-frequency absorption for a union of two unit balls

The literal support-volume coefficient is 4/(9π) after division by
(2π)^3. Absorption gives the manuscript's g comparison, including mass
zero, without a separation-dependent constant or a source synthesis inverse.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Set Filter

theorem volume_two_unit_balls_lt_top (a b : EuclideanSpace ℝ (Fin 3)) :
    volume (Metric.ball a 1 ∪ Metric.ball b 1) < ⊤ := by
  exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨measure_ball_lt_top,
    measure_ball_lt_top⟩)

theorem volume_two_unit_balls_toReal_le (a b : EuclideanSpace ℝ (Fin 3)) :
    (volume (Metric.ball a 1 ∪ Metric.ball b 1)).toReal ≤ 8 * Real.pi / 3 := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ball_ne_top, measure_ball_ne_top⟩)
    (measure_union_le (μ := volume) (Metric.ball a 1) (Metric.ball b 1))
  have hp : 0 ≤ Real.pi * 4 / 3 := by positivity
  simpa only [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, ← ENNReal.ofReal_add hp hp, ENNReal.toReal_ofReal
      (by positivity : 0 ≤ 8 * Real.pi / 3),
    show Real.pi * 4 / 3 + Real.pi * 4 / 3 = 8 * Real.pi / 3 by ring] using h

theorem joint_spatialFourier_low_frequency (f : SpatialTestFunction)
    (a b : EuclideanSpace ℝ (Fin 3))
    (hf : Function.support f.1 ⊆ Metric.ball a 1 ∪ Metric.ball b 1) :
    (∫ p in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖spatialFourier f p‖ ^ 2) ≤
      ((2 * Real.pi) ^ 3 * (4 / (9 * Real.pi))) * ∫ x, (f.1 x) ^ 2 := by
  have h := spatialFourier_low_frequency_le_support_volume f _
    (volume_two_unit_balls_lt_top a b) hf
  calc
    _ ≤ ((4 * Real.pi / 3) *
        (volume (Metric.ball a 1 ∪ Metric.ball b 1)).toReal) * ∫ x, (f.1 x) ^ 2 := h
    _ ≤ ((4 * Real.pi / 3) * (8 * Real.pi / 3)) * ∫ x, (f.1 x) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ => sq_nonneg _))
      exact mul_le_mul_of_nonneg_left (volume_two_unit_balls_toReal_le a b) (by positivity)
    _ = _ := by congr 1; field_simp; ring

theorem joint_low_frequency_coefficient_lt_half : 4 / (9 * Real.pi) < (1 / 2 : ℝ) := by
  apply (div_lt_iff₀ (by positivity : 0 < 9 * Real.pi)).mpr
  nlinarith [Real.pi_gt_three]

theorem integrable_dispersion_fourier_norm_sq {μ : ℝ} (hμ : 0 ≤ μ)
    (f : SpatialTestFunction) : Integrable (fun p => dispersion μ p * ‖spatialFourier f p‖ ^ 2)
      := by
  have h := (integrable_dispersion_spatialFourier_product hμ f f).norm
  convert h using 1
  funext p
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ dispersion μ p from Real.sqrt_nonneg _)]
  ring

/-- The manuscript g estimate in its original Fourier normalization. -/
theorem joint_position_L2_le_weighted_fourier {μ : ℝ} (hμ : 0 ≤ μ)
    (f : SpatialTestFunction) (a b : EuclideanSpace ℝ (Fin 3))
    (hf : Function.support f.1 ⊆ Metric.ball a 1 ∪ Metric.ball b 1) :
    (∫ x, (f.1 x) ^ 2) ≤
      (2 / (2 * Real.pi) ^ 3) * ∫ p, dispersion μ p * ‖spatialFourier f p‖ ^ 2 := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
  have hw := integrable_dispersion_fourier_norm_sq hμ f
  have hh : (∫ p in Bᶜ, ‖spatialFourier f p‖ ^ 2) ≤
      ∫ p, dispersion μ p * ‖spatialFourier f p‖ ^ 2 := by
    apply le_trans (b := ∫ p in Bᶜ, dispersion μ p * ‖spatialFourier f p‖ ^ 2)
    · apply integral_mono_ae (integrable_spatialFourier_norm_sq f).integrableOn hw.integrableOn
      filter_upwards [ae_restrict_mem (s := Bᶜ) Metric.isOpen_ball.measurableSet.compl] with p hp
      have hp1 : 1 ≤ ‖p‖ := by simpa only [B, Set.mem_compl_iff, Metric.mem_ball,
        dist_zero_right, not_lt] using hp
      have hd : 1 ≤ dispersion μ p := hp1.trans (norm_le_dispersion μ p)
      nlinarith [sq_nonneg ‖spatialFourier f p‖]
    · exact setIntegral_le_integral hw (Eventually.of_forall (fun p =>
        mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)))
  have hl := joint_spatialFourier_low_frequency f a b hf
  have hlhalf : (∫ p in B, ‖spatialFourier f p‖ ^ 2) ≤
      ((2 * Real.pi) ^ 3 / 2) * ∫ x, (f.1 x) ^ 2 := by
    apply hl.trans
    have h := mul_le_mul_of_nonneg_left joint_low_frequency_coefficient_lt_half.le
      (show 0 ≤ (2 * Real.pi) ^ 3 by positivity)
    exact mul_le_mul_of_nonneg_right (by nlinarith) (integral_nonneg (fun _ => sq_nonneg _))
  have hsplit := integral_add_compl (s := B) Metric.isOpen_ball.measurableSet
    (integrable_spatialFourier_norm_sq f)
  rw [integral_spatialFourier_norm_sq] at hsplit
  have hmain : (2 * Real.pi) ^ 3 * (∫ x, (f.1 x) ^ 2) ≤
      2 * ∫ p, dispersion μ p * ‖spatialFourier f p‖ ^ 2 := by linarith
  have hdiv : (∫ x, (f.1 x) ^ 2) ≤
      (2 * ∫ p, dispersion μ p * ‖spatialFourier f p‖ ^ 2) / (2 * Real.pi) ^ 3 :=
    (le_div_iff₀ (show 0 < (2 * Real.pi) ^ 3 by positivity)).mpr
      (by simpa only [mul_comm] using hmain)
  calc
    _ ≤ _ := hdiv
    _ = _ := by ring

end VacuumBellSeparation
