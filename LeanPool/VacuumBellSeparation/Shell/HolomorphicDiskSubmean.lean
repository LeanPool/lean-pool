/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ComplexDiskPolar
public import LeanPool.VacuumBellSeparation.Shell.HolomorphicCircleSubmean
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The genuine complex disk squared-norm submean

The circle inequality is integrated over actual radii with the true
Jacobian. The statement uses extended integrals, so no totalized Bochner
integral can hide a convergence failure.
-/

@[expose] public section

namespace VacuumBellSeparation

open Complex MeasureTheory Metric Real Set
open scoped ENNReal

theorem holomorphic_circle_lintegral_submean_sq {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball 0 r)) :
    ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (‖f 0‖ ^ 2) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖f (circleMap 0 r θ)‖ ^ 2) := by
  have hc : Continuous (fun θ => ‖f (circleMap 0 r θ)‖ ^ 2) := by
    apply (hf.continuousOn_ball.norm.pow 2).comp_continuous (continuous_circleMap _ _)
    intro θ
    simp only [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos hr, le_refl]
  have hi : IntegrableOn (fun θ => ‖f (circleMap 0 r θ)‖ ^ 2) (Ioo (-Real.pi) Real.pi) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hm := holomorphic_circle_submean_sq hr hf
  rw [circleAverage_eq_integral_neg_pi] at hm
  have hreal : 2 * Real.pi * ‖f 0‖ ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, ‖f (circleMap 0 r θ)‖ ^ 2 := by
    calc
      _ ≤ (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
          ∫ θ in Ioo (-Real.pi) Real.pi, ‖f (circleMap 0 r θ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hm two_pi_pos.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul]
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul two_pi_pos.le,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)] at h
  exact h

theorem holomorphic_disk_lintegral_submean_sq {f : ℂ → ℂ} {R : ℝ}
    (hm : Measurable f) (hf : DiffContOnCl ℂ f (ball 0 R)) :
    ENNReal.ofReal (‖f 0‖ ^ 2) * volume (ball (0 : ℂ) R) ≤
      ∫⁻ z in ball (0 : ℂ) R, ENNReal.ofReal (‖f z‖ ^ 2) := by
  have hangular (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) :
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal r * ENNReal.ofReal (‖f 0‖ ^ 2)) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal r *
        ENNReal.ofReal (‖f (circleMap 0 r θ)‖ ^ 2) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply mul_le_mul_right
    have h := holomorphic_circle_lintegral_submean_sq hr.1
      (hf.mono (ball_subset_ball hr.2.le))
    simpa only [setLIntegral_const, Real.volume_Ioo,
      show Real.pi - -Real.pi = 2 * Real.pi by ring, mul_comm] using h
  calc
    _ = ∫⁻ z in ball (0 : ℂ) R, ENNReal.ofReal (‖f 0‖ ^ 2) :=
      (setLIntegral_const _ _).symm
    _ = ∫⁻ r in Ioo (0 : ℝ) R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * ENNReal.ofReal (‖f 0‖ ^ 2) :=
      complexDisk_lintegral_polar (R := R) _ measurable_const
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * ENNReal.ofReal (‖f (circleMap 0 r θ)‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hangular r hr
    _ = _ := (complexDisk_lintegral_polar (R := R) _
      (ENNReal.measurable_ofReal.comp (hm.norm.pow_const 2))).symm

/-- The area normalization is the actual complex Lebesgue area Real.pi R². -/
theorem holomorphic_disk_lintegral_submean_sq_area {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hm : Measurable f) (hf : DiffContOnCl ℂ f (ball 0 R)) :
    ENNReal.ofReal (Real.pi * R ^ 2 * ‖f 0‖ ^ 2) ≤
      ∫⁻ z in ball (0 : ℂ) R, ENNReal.ofReal (‖f z‖ ^ 2) := by
  have h := holomorphic_disk_lintegral_submean_sq hm hf
  rw [Complex.volume_ball] at h
  rw [ENNReal.ofReal_mul (mul_nonneg Real.pi_pos.le (sq_nonneg R)),
    ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hR.le]
  have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [hpi]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end VacuumBellSeparation
