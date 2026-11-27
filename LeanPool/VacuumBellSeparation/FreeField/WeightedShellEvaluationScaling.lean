/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.HolomorphicInducedMeasureSubmean

/-!
# Literal scaled source waves on the normalized shell

The test functions are unchanged. Scaling acts on the actual complex
four-vector before evaluation, so all u/i v cross terms are retained.
The chart-measure estimate therefore applies at normalized mass m/E
without replacing the source by a surrogate kernel.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Metric Set
open scoped ENNReal

/-- Scaled complex test wave given by `complexSourceWave u ((E : ℂ) • z) + Complex.I *
complexSourceWave v ((E : ℂ) • z)`. -/
noncomputable def scaledComplexTestWave (E : ℝ) (u v : TimeZeroSource)
    (z : ComplexSpacetime) : ℂ :=
  complexSourceWave u ((E : ℂ) • z) + Complex.I * complexSourceWave v ((E : ℂ) • z)

theorem differentiable_scaledComplexTestWave (E : ℝ) (u v : TimeZeroSource) :
    Differentiable ℂ (scaledComplexTestWave E u v) := by
  have hs : Differentiable ℂ (fun z : ComplexSpacetime => (E : ℂ) • z) :=
    differentiable_id.const_smul (E : ℂ)
  exact ((differentiable_complexSourceWave u).comp hs).add
    (((differentiable_complexSourceWave v).comp hs).const_mul Complex.I)

theorem scaledComplexTestWave_measure_submean {t E R d δ : ℝ}
    (u v : TimeZeroSource) (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (c : ShellEuclideanDomain) (hR : 0 < R)
    (hsub : ball c (2 * R) ⊆ euclideanShellChartDomain t)
    (hJ : ∀ w ∈ ball c (2 * R), d ≤ inducedShellChartDensity t Λ w)
    {S : Set (complexShell t)} (hS : MeasurableSet S)
    (hpatch : S ⊆ inducedShellPatch t Λ)
    (himage : ∀ w ∈ ball c (2 * R), shellPatchPoint t Λ hΛ w ∈ S)
    (ν : Measure (complexShell t))
    (hlower : ENNReal.ofReal δ • (inducedRegularShellVolume t).restrict S ≤ ν) :
    ENNReal.ofReal δ * (ENNReal.ofReal d *
        (ENNReal.ofReal (‖scaledComplexTestWave E u v
          (lorentzComplexShellChart t Λ (shellEuclideanCoordinates c))‖ ^ 2) *
          volume (ball (0 : ℂ) R) ^ 3)) ≤
      ∫⁻ z : complexShell t, ENNReal.ofReal (‖scaledComplexTestWave E u v z.1‖ ^ 2) ∂ν := by
  apply holomorphicShellWave_measure_submean
    (fun z : complexShell t => scaledComplexTestWave E u v z.1)
    (((differentiable_scaledComplexTestWave E u v).continuous.comp
      continuous_subtype_val).measurable) Λ hΛ ?_ c hR hsub hJ hS hpatch himage ν hlower
  intro w hw
  exact (differentiable_scaledComplexTestWave E u v _).comp w
    ((differentiableAt_lorentzComplexShellChart Λ hw).comp w
      shellEuclideanCoordinates.differentiableAt)

theorem scaledComplexTestWave_at_one (u v : TimeZeroSource) (z : ComplexSpacetime) :
    scaledComplexTestWave 1 u v z = complexSourceWave u z + Complex.I * complexSourceWave v z := by
  simp only [scaledComplexTestWave, Complex.ofReal_one, one_smul]

end VacuumBellSeparation
