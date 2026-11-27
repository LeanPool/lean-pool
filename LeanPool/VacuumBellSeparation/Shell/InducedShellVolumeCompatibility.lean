/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellChartOverlap
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of coordinates for the Euclidean induced shell volume

The actual positive Gram density defines a coordinate measure on each
regular shell chart. The pinned real change-of-variables theorem proves
compatibility of all nonnegative weighted integrals on the literal
overlap. Thus this is a coordinate-independent Riemannian-volume
construction at the chart level, without assuming a nonlinear ambient
Hausdorff area formula.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

/-- Induced shell coordinate volume. -/
noncomputable def inducedShellCoordinateVolume (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) : Measure ShellEuclideanDomain :=
  (volume.withDensity (fun w => ENNReal.ofReal (inducedShellChartDensity m Λ w))).restrict
    (euclideanShellChartDomain m)

theorem inducedShellCoordinateVolume_apply {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {s : Set ShellEuclideanDomain}
    (hs : MeasurableSet s) (hsub : s ⊆ euclideanShellChartDomain m) :
    inducedShellCoordinateVolume m Λ s =
      ∫⁻ w in s, ENNReal.ofReal (inducedShellChartDensity m Λ w) := by
  rw [inducedShellCoordinateVolume, Measure.restrict_apply hs,
    Set.inter_eq_left.mpr hsub, withDensity_apply _ hs]

theorem inducedShellCoordinateVolume_bounds {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) {s : Set ShellEuclideanDomain}
    (hs : MeasurableSet s) (hsub : s ⊆ euclideanShellChartDomain m)
    {c C : ℝ} (hb : ∀ w ∈ s,
      c ≤ inducedShellChartDensity m Λ w ∧ inducedShellChartDensity m Λ w ≤ C) :
    ENNReal.ofReal c * volume s ≤ inducedShellCoordinateVolume m Λ s ∧
      inducedShellCoordinateVolume m Λ s ≤ ENNReal.ofReal C * volume s := by
  rw [inducedShellCoordinateVolume_apply Λ hs hsub]
  constructor
  · have h := setLIntegral_mono' (μ := volume) hs
      (fun w hw => ENNReal.ofReal_le_ofReal (hb w hw).1)
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h
  · have h := setLIntegral_mono' (μ := volume) hs
      (fun w hw => ENNReal.ofReal_le_ofReal (hb w hw).2)
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h

/-- All nonnegative ambient weights have equal integrals in the two
actual coordinates of an overlap; no measurability or finiteness of
the weight is needed by the pinned change-of-variables theorem. -/
theorem inducedShellChart_weighted_overlap {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ)
    {s : Set ShellEuclideanDomain} (hs : MeasurableSet s)
    (hsub : s ⊆ euclideanShellChartOverlap m Λ Γ) (g : ShellEuclideanAmbient → ℝ≥0∞) :
    (∫⁻ y in euclideanShellChartTransition m Λ Γ '' s,
      ENNReal.ofReal (inducedShellChartDensity m Γ y) * g (euclideanLorentzShellChart m Γ y)) =
      ∫⁻ x in s, ENNReal.ofReal (inducedShellChartDensity m Λ x) *
        g (euclideanLorentzShellChart m Λ x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x hx => (differentiableAt_euclideanShellChartTransition Λ Γ
      (hsub hx).1).hasFDerivAt.hasFDerivWithinAt)
    ((euclideanShellChartTransition_injOn Λ Γ hΛ hΓ).mono hsub)]
  apply setLIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [euclideanShellChartTransition_reconstruct Λ Γ hΛ hΓ (hsub hx),
    inducedShellChartDensity_transition Λ Γ hΛ hΓ (hsub hx),
    ENNReal.ofReal_mul' (abs_nonneg _)]
  ac_rfl

theorem inducedShellCoordinateVolume_overlap {m : ℝ}
    (Λ Γ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) (hΓ : IsLorentzMap Γ)
    {s : Set ShellEuclideanDomain} (hs : MeasurableSet s)
    (hsub : s ⊆ euclideanShellChartOverlap m Λ Γ) :
    inducedShellCoordinateVolume m Γ (euclideanShellChartTransition m Λ Γ '' s) =
      inducedShellCoordinateVolume m Λ s := by
  have him : MeasurableSet (euclideanShellChartTransition m Λ Γ '' s) :=
    measurable_image_of_fderivWithin hs
      (fun x hx => (differentiableAt_euclideanShellChartTransition Λ Γ
        (hsub hx).1).hasFDerivAt.hasFDerivWithinAt)
      ((euclideanShellChartTransition_injOn Λ Γ hΛ hΓ).mono hsub)
  have hi : euclideanShellChartTransition m Λ Γ '' s ⊆ euclideanShellChartDomain m := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2.1
  rw [inducedShellCoordinateVolume_apply Γ him hi,
    inducedShellCoordinateVolume_apply Λ hs (fun x hx => (hsub hx).1)]
  simpa only [mul_one] using inducedShellChart_weighted_overlap Λ Γ hΛ hΓ hs hsub (fun _ => 1)

end VacuumBellSeparation
