/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationMeasure

/-!
# Local induced-volume submean for a holomorphic shell function

This is the measure-theoretic interface for scaled physical waves.
The shell function is measurable and genuinely holomorphic in the
specified actual chart. The lower measure comparison is a separate,
explicit geometric hypothesis.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set
open scoped ENNReal

theorem holomorphicShellWave_measure_submean {m R d δ : ℝ}
    (F : complexShell m → ℂ) (hm : Measurable F)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hd : ∀ w ∈ euclideanShellChartDomain m,
      DifferentiableAt ℂ (fun w => F (shellPatchPoint m Λ hΛ w)) w)
    (c : ShellEuclideanDomain) (hR : 0 < R)
    (hsub : ball c (2 * R) ⊆ euclideanShellChartDomain m)
    (hJ : ∀ w ∈ ball c (2 * R), d ≤ inducedShellChartDensity m Λ w)
    {S : Set (complexShell m)} (hS : MeasurableSet S)
    (hpatch : S ⊆ inducedShellPatch m Λ)
    (himage : ∀ w ∈ ball c (2 * R), shellPatchPoint m Λ hΛ w ∈ S)
    (ν : Measure (complexShell m))
    (hlower : ENNReal.ofReal δ • (inducedRegularShellVolume m).restrict S ≤ ν) :
    ENNReal.ofReal δ * (ENNReal.ofReal d *
        (ENNReal.ofReal (‖F (shellPatchPoint m Λ hΛ c)‖ ^ 2) *
          volume (ball (0 : ℂ) R) ^ 3)) ≤
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂ν := by
  let g : complexShell m → ℝ≥0∞ := fun z => ENNReal.ofReal (‖F z‖ ^ 2)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (hm.norm.pow_const 2)
  have hlocal := local_shellEuclidean_submean_sq (isOpen_euclideanShellChartDomain m)
    (fun w => F (shellPatchPoint m Λ hΛ w)) hd hR hsub
  have hcoord : ENNReal.ofReal d *
      (ENNReal.ofReal (‖F (shellPatchPoint m Λ hΛ c)‖ ^ 2) *
        volume (ball (0 : ℂ) R) ^ 3) ≤
      ∫⁻ w in ball c (2 * R), g (shellPatchPoint m Λ hΛ w)
        ∂inducedShellCoordinateVolume m Λ := by
    apply (_root_.mul_le_mul_right hlocal (ENNReal.ofReal d)).trans
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      inducedShellCoordinateVolume_lintegral Λ measurableSet_ball hsub]
    apply setLIntegral_mono' measurableSet_ball
    intro w hw
    exact _root_.mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ w hw)) _
  have hrestrict : (inducedRegularShellVolume m).restrict S =
      (inducedShellPatchVolume m Λ hΛ).restrict S := by
    rw [← inducedRegularShellVolume_restrict_chart m Λ hΛ,
      Measure.restrict_restrict hS, inter_eq_left.mpr hpatch]
  have hpatchbound : ENNReal.ofReal d *
      (ENNReal.ofReal (‖F (shellPatchPoint m Λ hΛ c)‖ ^ 2) *
        volume (ball (0 : ℂ) R) ^ 3) ≤
      ∫⁻ z in S, g z ∂inducedRegularShellVolume m := by
    calc
      _ ≤ ∫⁻ w in ball c (2 * R), g (shellPatchPoint m Λ hΛ w)
          ∂inducedShellCoordinateVolume m Λ := hcoord
      _ = ∫⁻ w in ball c (2 * R), S.indicator g (shellPatchPoint m Λ hΛ w)
          ∂inducedShellCoordinateVolume m Λ := by
        apply setLIntegral_congr_fun measurableSet_ball
        intro w hw
        dsimp only
        rw [indicator_of_mem (himage w hw)]
      _ ≤ ∫⁻ w, S.indicator g (shellPatchPoint m Λ hΛ w)
          ∂inducedShellCoordinateVolume m Λ :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ z, S.indicator g z ∂inducedShellPatchVolume m Λ hΛ :=
        (lintegral_map' (hg.indicator hS).aemeasurable
          (aemeasurable_shellPatchPoint m Λ hΛ)).symm
      _ = ∫⁻ z in S, g z ∂inducedRegularShellVolume m := by
        rw [lintegral_indicator hS, hrestrict]
  apply (_root_.mul_le_mul_right hpatchbound (ENNReal.ofReal δ)).trans
  rw [← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' hlower le_rfl

end VacuumBellSeparation
