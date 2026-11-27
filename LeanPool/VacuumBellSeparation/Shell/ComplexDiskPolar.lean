/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Actual complex disk volume in polar coordinates

This is complex Lebesgue measure, with its genuine radial Jacobian.
The nonnegative formula retains infinite integrals and requires no
integrability assumption. The angular interval is explicitly (-pi,pi).
-/

@[expose] public section

namespace VacuumBellSeparation

open Complex MeasureTheory Metric Real Set
open scoped ENNReal

theorem complex_polar_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp only [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.ofReal_sin]

theorem complexDisk_lintegral_polar {R : ℝ}
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in ball (0 : ℂ) R, f z) =
      ∫⁻ r in Ioo (0 : ℝ) R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap 0 r θ) := by
  let g : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * f (circleMap 0 p.1 p.2)
  have hg : Measurable g := by
    apply Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst)
    apply hf.comp
    exact (by unfold circleMap; fun_prop : Continuous (fun p : ℝ × ℝ =>
      circleMap 0 p.1 p.2)).measurable
  have heq : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 * (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) =
        (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi).indicator g p := by
    intro p hp
    have hr : 0 < p.1 := hp.1
    have hθ : p.2 ∈ Ioo (-Real.pi) Real.pi := hp.2
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    by_cases h : p.1 < R
    · have hz : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R := by
        simpa only [mem_ball_zero_iff, hn] using h
      have hmem : p ∈ Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := ⟨⟨hr, h⟩, hθ⟩
      rw [indicator_of_mem hz, indicator_of_mem hmem]
      simp only [g, complex_polar_symm_eq_circleMap]
    · have hz : Complex.polarCoord.symm p ∉ ball (0 : ℂ) R := by
        simpa only [mem_ball_zero_iff, hn] using h
      have hp' : p ∉ Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := fun hmem => h hmem.1.2
      rw [indicator_of_notMem hz, mul_zero, indicator_of_notMem hp']
  have hsub : Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi ⊆ polarCoord.target :=
    fun _ hp => ⟨hp.1.1, hp.2⟩
  calc
    _ = ∫⁻ z, (ball (0 : ℂ) R).indicator f z :=
      (lintegral_indicator measurableSet_ball f).symm
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) :=
      (Complex.lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, g p := by
      calc
        _ = ∫⁻ p in polarCoord.target,
            (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi).indicator g p :=
          setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) heq
        _ = _ := by
          rw [setLIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
            inter_eq_left.mpr hsub]
    _ = _ := by
      rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod g hg.aemeasurable]

theorem circleAverage_eq_integral_neg_pi (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    circleAverage f c R = (2 * Real.pi)⁻¹ *
      ∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap c R θ) := by
  rw [circleAverage_eq_integral_add (-Real.pi), smul_eq_mul,
    intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c R θ)) (-Real.pi)]
  have hπ : (2 : ℝ) * Real.pi + -Real.pi = Real.pi := by ring
  rw [zero_add, hπ, intervalIntegral.integral_of_le (by linarith [pi_pos]),
    integral_Ioc_eq_integral_Ioo]

end VacuumBellSeparation
