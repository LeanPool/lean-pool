/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.UniformShellSubmeanCharts
public import LeanPool.VacuumBellSeparation.Shell.HolomorphicInducedMeasureSubmean

/-!
# Uniform genuine induced-volume submean on the normalized target

Only an actual ambient open neighbourhood of the compact target is
given. The common chart radius and positive density bound are derived
by finite covering. This supplies one finite constant, independent of
the mass and of the entire function, for the original induced volume.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set
open scoped ENNReal

theorem normalizedTarget_uniform_holomorphic_submean
    {V : Set (ℝ × ComplexSpacetime)} (hV : IsOpen V) (hcover : normalizedTarget ⊆ V) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧
      ∀ t z, (t, z) ∈ normalizedTarget →
        ∀ F : ComplexSpacetime → ℂ, Differentiable ℂ F →
          ENNReal.ofReal (‖F z‖ ^ 2) ≤ C *
            ∫⁻ w in {w : complexShell t | (t, w.1) ∈ V},
              ENNReal.ofReal (‖F w.1‖ ^ 2) ∂inducedRegularShellVolume t := by
  obtain ⟨R, d, hR, hd, hcharts⟩ := normalizedTarget_uniform_submean_charts hV hcover
  let K : ℝ≥0∞ := ENNReal.ofReal d * volume (ball (0 : ℂ) R) ^ 3
  have hK : 0 < K := by
    dsimp [K]
    exact bot_lt_iff_ne_bot.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr hd).ne'
      (pow_ne_zero 3 (measure_ball_pos volume (0 : ℂ) hR).ne'))
  have hKt : K ≠ ∞ := by
    dsimp [K]
    rw [Complex.volume_ball]
    finiteness
  refine ⟨K⁻¹, ENNReal.inv_pos.mpr hKt, ENNReal.inv_lt_top.mpr hK, ?_⟩
  intro t z hz F hF
  obtain ⟨Λ, c, hΛ, him, hball⟩ := hcharts t z hz
  let B : Set (complexShell t) := {w | (t, w.1) ∈ V}
  let S : Set (complexShell t) := B ∩ inducedShellPatch t Λ
  have hB : MeasurableSet B :=
    (hV.preimage (continuous_const.prodMk continuous_subtype_val)).measurableSet
  have hS : MeasurableSet S := hB.inter (isOpen_inducedShellPatch t Λ).measurableSet
  have hsub : ball c (2 * R) ⊆ euclideanShellChartDomain t := fun w hw => (hball w hw).1
  have hj : ∀ w ∈ ball c (2 * R), d ≤ inducedShellChartDensity t Λ w :=
    fun w hw => (hball w hw).2.1
  have himage : ∀ w ∈ ball c (2 * R), shellPatchPoint t Λ hΛ w ∈ S := by
    intro w hw
    exact ⟨(hball w hw).2.2, shellPatchPoint_mem Λ hΛ (hsub hw)⟩
  have hlower : ENNReal.ofReal (1 : ℝ) • (inducedRegularShellVolume t).restrict S ≤
      (inducedRegularShellVolume t).restrict B := by
    rw [ENNReal.ofReal_one, one_smul]
    exact Measure.restrict_mono (show S ⊆ B from fun _ hw => hw.1) le_rfl
  have h := holomorphicShellWave_measure_submean
    (fun w : complexShell t => F w.1)
    (hF.continuous.comp continuous_subtype_val).measurable Λ hΛ
    (fun w hw => (hF _).comp w
      ((differentiableAt_lorentzComplexShellChart Λ hw).comp w
        shellEuclideanCoordinates.differentiableAt))
    c hR hsub hj hS (fun _ hw => hw.2) himage
    ((inducedRegularShellVolume t).restrict B) hlower
  simp only [ENNReal.ofReal_one, one_mul, shellPatchPoint, him] at h
  have hmul : K * ENNReal.ofReal (‖F z‖ ^ 2) ≤
      ∫⁻ w in B, ENNReal.ofReal (‖F w.1‖ ^ 2) ∂inducedRegularShellVolume t := by
    simpa only [K, mul_assoc, mul_comm, mul_left_comm] using h
  calc
    _ = K⁻¹ * (K * ENNReal.ofReal (‖F z‖ ^ 2)) :=
      (ENNReal.inv_mul_cancel_left hK.ne' hKt).symm
    _ ≤ _ := _root_.mul_le_mul_right hmul _

end VacuumBellSeparation
