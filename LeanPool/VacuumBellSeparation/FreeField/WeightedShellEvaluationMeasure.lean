/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationSubmean
public import LeanPool.VacuumBellSeparation.Shell.InducedRegularShellVolume

/-!
# From actual local induced volume to a shell-measure evaluation bound

The regular-shell measure and the literal source wave are fixed. A
quantitative lower bound for another actual measure on a specified
patch is an explicit geometric premise. No final contour lower bound
is assumed in the definition of a measure or a source space.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set
open scoped ENNReal

/-- Complex test shell wave given by `complexSourceWave u z.1 + Complex.I * complexSourceWave v
z.1`. -/
noncomputable def complexTestShellWave (m : ℝ) (u v : TimeZeroSource)
    (z : complexShell m) : ℂ := complexSourceWave u z.1 + Complex.I * complexSourceWave v z.1

theorem continuous_complexTestShellWave (m : ℝ) (u v : TimeZeroSource) :
    Continuous (complexTestShellWave m u v) :=
  ((differentiable_complexSourceWave u).continuous.comp continuous_subtype_val).add
    (((differentiable_complexSourceWave v).continuous.comp continuous_subtype_val).const_mul
      Complex.I)

theorem complexTestShellChartWave_patch_submean {m R d : ℝ}
    (u v : TimeZeroSource) (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (c : ShellEuclideanDomain) (hR : 0 < R)
    (hsub : ball c (2 * R) ⊆ euclideanShellChartDomain m)
    (hJ : ∀ w ∈ ball c (2 * R), d ≤ inducedShellChartDensity m Λ w)
    {S : Set (complexShell m)} (hS : MeasurableSet S)
    (hpatch : S ⊆ inducedShellPatch m Λ)
    (himage : ∀ w ∈ ball c (2 * R), shellPatchPoint m Λ hΛ w ∈ S) :
    ENNReal.ofReal d * (ENNReal.ofReal (‖complexTestShellChartWave u v m Λ c‖ ^ 2) *
        volume (ball (0 : ℂ) R) ^ 3) ≤
      ∫⁻ z in S, ENNReal.ofReal (‖complexTestShellWave m u v z‖ ^ 2)
        ∂inducedRegularShellVolume m := by
  let g : complexShell m → ℝ≥0∞ := fun z => ENNReal.ofReal (‖complexTestShellWave m u v z‖ ^ 2)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((continuous_complexTestShellWave m u v).measurable.norm.pow_const 2)
  have hrestrict : (inducedRegularShellVolume m).restrict S =
      (inducedShellPatchVolume m Λ hΛ).restrict S := by
    rw [← inducedRegularShellVolume_restrict_chart m Λ hΛ,
      Measure.restrict_restrict hS, inter_eq_left.mpr hpatch]
  have hmap : (∫⁻ z in S, g z ∂inducedShellPatchVolume m Λ hΛ) =
      ∫⁻ w, S.indicator g (shellPatchPoint m Λ hΛ w) ∂inducedShellCoordinateVolume m Λ := by
    rw [← lintegral_indicator hS g, inducedShellPatchVolume]
    exact lintegral_map' (hg.indicator hS).aemeasurable
      (aemeasurable_shellPatchPoint m Λ hΛ)
  calc
    _ ≤ ∫⁻ w in ball c (2 * R),
        ENNReal.ofReal (‖complexTestShellChartWave u v m Λ w‖ ^ 2)
          ∂inducedShellCoordinateVolume m Λ :=
      complexTestShellChartWave_induced_submean u v Λ c hR hsub hJ
    _ = ∫⁻ w in ball c (2 * R), S.indicator g (shellPatchPoint m Λ hΛ w)
        ∂inducedShellCoordinateVolume m Λ := by
      apply setLIntegral_congr_fun measurableSet_ball
      intro w hw
      dsimp only
      rw [indicator_of_mem (himage w hw)]
      rfl
    _ ≤ ∫⁻ w, S.indicator g (shellPatchPoint m Λ hΛ w)
        ∂inducedShellCoordinateVolume m Λ :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z in S, g z ∂inducedShellPatchVolume m Λ hΛ := hmap.symm
    _ = _ := by rw [hrestrict]

theorem complexTestShellWave_measure_bound {m R d δ : ℝ}
    (u v : TimeZeroSource) (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (c : ShellEuclideanDomain) (hR : 0 < R)
    (hsub : ball c (2 * R) ⊆ euclideanShellChartDomain m)
    (hJ : ∀ w ∈ ball c (2 * R), d ≤ inducedShellChartDensity m Λ w)
    {S : Set (complexShell m)} (hS : MeasurableSet S)
    (hpatch : S ⊆ inducedShellPatch m Λ)
    (himage : ∀ w ∈ ball c (2 * R), shellPatchPoint m Λ hΛ w ∈ S)
    (ν : Measure (complexShell m))
    (hlower : ENNReal.ofReal δ • (inducedRegularShellVolume m).restrict S ≤ ν) :
    ENNReal.ofReal δ * (ENNReal.ofReal d *
        (ENNReal.ofReal (‖complexTestShellChartWave u v m Λ c‖ ^ 2) *
          volume (ball (0 : ℂ) R) ^ 3)) ≤
      ∫⁻ z, ENNReal.ofReal (‖complexTestShellWave m u v z‖ ^ 2) ∂ν := by
  apply (_root_.mul_le_mul_right
    (complexTestShellChartWave_patch_submean u v Λ hΛ c hR hsub hJ hS hpatch himage) _).trans
  rw [← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' hlower le_rfl

end VacuumBellSeparation
