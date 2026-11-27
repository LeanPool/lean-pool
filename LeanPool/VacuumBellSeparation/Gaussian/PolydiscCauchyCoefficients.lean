/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCoefficientDefs
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Actual iterated Cauchy coefficients

The coefficients are normalized contour integrals, with one contour for
each coordinate. Their bounds retain the exact product of inverse radii.
The bound itself is valid for total integrals; reconstruction additionally
requires the analytic and convergence hypotheses proved separately.
-/

@[expose] public section

open Complex MeasureTheory Set Metric
open scoped BigOperators

namespace VacuumBellSeparation.Gaussian



theorem circleCoefficient_norm_le {R M : ℝ} (hR : 0 < R)
    (f : ℂ → ℂ) (hf : ∀ z, ‖z‖ = R → ‖f z‖ ≤ M) (k : ℕ) :
    ‖circleCoefficient R f k‖ ≤ M * R⁻¹ ^ k := by
  have hb : ∀ z ∈ sphere (0 : ℂ) R,
      ‖z⁻¹ ^ k • z⁻¹ • f z‖ ≤ R⁻¹ ^ k * R⁻¹ * M := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa only [mem_sphere_zero_iff_norm] using hz
    simp only [norm_smul, norm_pow, norm_inv, hz']
    nlinarith [mul_le_mul_of_nonneg_left (hf z hz')
      (show 0 ≤ R⁻¹ ^ k * R⁻¹ by positivity)]
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    hR.le hb
  change ‖circleCoefficient R f k‖ ≤ R * (R⁻¹ ^ k * R⁻¹ * M) at h
  calc
    _ ≤ R * (R⁻¹ ^ k * R⁻¹ * M) := h
    _ = M * R⁻¹ ^ k := by field_simp

theorem circleCoefficient_power_apply (R : ℝ) (f : ℂ → ℂ) (k : ℕ) (w : ℂ) :
    cauchyPowerSeries f 0 R k (fun _ => w) = circleCoefficient R f k * w ^ k := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, sub_zero, circleCoefficient, smul_eq_mul]
  ring

theorem hasSum_circleCoefficient {R : ℝ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) {w : ℂ} (hw : ‖w‖ < R) :
    HasSum (fun k : ℕ => circleCoefficient R f k * w ^ k) (f w) := by
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  have hc := (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hs := hasSum_cauchyPowerSeries_integral hc hw
  rw [zero_add, hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
    (by simpa only [mem_ball_zero_iff] using hw)] at hs
  simpa only [circleCoefficient_power_apply] using hs





theorem polydiscCoefficient_norm_le (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (F : (Fin n → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc n R, ‖F z‖ ≤ M) (k : Fin n → ℕ) :
    ‖polydiscCoefficient n R F k‖ ≤ M * ∏ j, R⁻¹ ^ k j := by
  induction n with
  | zero =>
    simpa only [polydiscCoefficient, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      using hF Fin.elim0 (by intro j; exact Fin.elim0 j)
  | succ n ih =>
    have htail : 0 ≤ M * ∏ j : Fin n, R⁻¹ ^ k j.succ := by positivity
    have hbound : ∀ z : ℂ, ‖z‖ = R →
        ‖polydiscCoefficient n R (fun w => F (Fin.cons z w))
          (fun j => k j.succ)‖ ≤ M * ∏ j : Fin n, R⁻¹ ^ k j.succ := by
      intro z hz
      apply ih
      intro w hw
      apply hF (Fin.cons z w)
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa only [Fin.cons_zero] using hz.le
      · simpa only [Fin.cons_succ] using hw i
    have hc := circleCoefficient_norm_le hR
      (fun z => polydiscCoefficient n R (fun w => F (Fin.cons z w))
        (fun j => k j.succ)) hbound (k 0)
    simpa only [polydiscCoefficient, Fin.prod_univ_succ, mul_left_comm,
      mul_assoc, mul_comm] using hc

end VacuumBellSeparation.Gaussian
