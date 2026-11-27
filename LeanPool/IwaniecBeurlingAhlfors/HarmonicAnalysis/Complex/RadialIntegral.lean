/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Integrals of radial functions on `ℂ`

* `HarmonicAnalysis.lintegral_comp_norm`: `∫⁻_ℂ g (|z|) dz = 2π ∫⁻_0^∞ g (r) r dr` (polar
  coordinates).
* `HarmonicAnalysis.lintegral_ball_norm_rpow`: `∫_{|z| < 1} |z|^{−s} dz = 2π / (2 − s)` for
  `s < 2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real

namespace HarmonicAnalysis

/-- Integrals of radial functions: `∫⁻_ℂ g (|z|) dz = 2π ∫⁻_0^∞ g (r) r dr`. -/
theorem lintegral_comp_norm {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : ℂ, g ‖z‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun hmeas (g := fun p => ENNReal.ofReal p.1 * g p.1 * 1)
    (fun p hp => by
      dsimp only
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul, mul_one])]
  have h := lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioo (-π) π)) (f := fun r => ENNReal.ofReal r * g r)
    (g := fun _ => (1 : ℝ≥0∞)) (by fun_prop) aemeasurable_const
  beta_reduce at h
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, h, setLIntegral_const, one_mul,
    Real.volume_Ioo, mul_comm]
  congr 2
  ring

/-- `∫_{|z| < 1} |z|^{−s} dz = 2π / (2 − s)` for `s < 2`. -/
theorem lintegral_ball_norm_rpow {s : ℝ} (hs : s < 2) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖z‖ ^ (-s)) =
      ENNReal.ofReal (2 * π / (2 - s)) := by
  set h : ℝ → ℝ≥0∞ := (Iio (1 : ℝ)).indicator fun r => ENNReal.ofReal (r ^ (-s)) with h_def
  have hh : Measurable h :=
    (by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (-s))).indicator measurableSet_Iio
  have hball : (Metric.ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal (‖z‖ ^ (-s))) =
      fun z => h ‖z‖ := by
    funext z
    by_cases hz : ‖z‖ < 1
    · rw [h_def, indicator_of_mem (mem_ball_zero_iff.2 hz), indicator_of_mem (mem_Iio.2 hz)]
    · rw [h_def, indicator_of_notMem (mt mem_ball_zero_iff.1 hz),
        indicator_of_notMem (mt mem_Iio.1 hz)]
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet, hball, lintegral_comp_norm hh]
  have hmul : (fun r => ENNReal.ofReal r * h r) =
      (Iio (1 : ℝ)).indicator fun r => ENNReal.ofReal r * ENNReal.ofReal (r ^ (-s)) := by
    funext r
    simp only [h_def, indicator_apply]
    split_ifs <;> simp
  have hint : IntegrableOn (fun r : ℝ => r ^ (1 - s)) (Ioo 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by linarith : -1 < 1 - s)).1.mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun r : ℝ => r ^ (1 - s) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => Real.rpow_nonneg hr.1.le _
  rw [hmul, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    inter_comm, Ioi_inter_Iio,
    setLIntegral_congr_fun measurableSet_Ioo (g := fun r => ENNReal.ofReal (r ^ (1 - s)))
      (fun r hr => by
        dsimp only
        rw [← ENNReal.ofReal_mul hr.1.le, sub_eq_add_neg, Real.rpow_add hr.1, Real.rpow_one]),
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith)),
    Real.one_rpow, Real.zero_rpow (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end HarmonicAnalysis
