/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSpacetime
public import LeanPool.VacuumBellSeparation.FreeField.SpatialTestParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Entire original source waves along actual complex spacetime curves

Compact support supplies a genuine local derivative majorant for the
original spatial Fourier integral. This applies to complexified Lorentz
boost curves and to affine null discs without assuming continuation of
the physical L2 representative.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

theorem hasDerivAt_complexSpatialFourier_curve (f : SpatialTestFunction)
    (q dq : ℂ → ComplexSpacetime) (hq : Continuous q) (hdq : Continuous dq)
    (hd : ∀ ζ, HasDerivAt q (dq ζ) ζ) (ζ : ℂ) :
    HasDerivAt (fun z => complexSpatialFourier f (q z).2)
      (∫ x : EuclideanSpace ℝ (Fin 3),
        ((-Complex.I) * complexSpatialPhase x (dq ζ)) *
          Complex.exp ((-Complex.I) * complexSpatialPhase x (q ζ)) * (f.1 x : ℂ)) ζ := by
  have h := hasDerivAt_spatialTest_integral f
    (fun z x => Complex.exp ((-Complex.I) * complexSpatialPhase x (q z)))
    (fun z x => ((-Complex.I) * complexSpatialPhase x (dq z)) *
      Complex.exp ((-Complex.I) * complexSpatialPhase x (q z)))
    (by simp only [complexSpatialPhase_apply, spatialDot]; fun_prop)
    (by simp only [complexSpatialPhase_apply, spatialDot]; fun_prop)
    (fun z x => by
      have hp := ((complexSpatialPhase x).hasFDerivAt.comp_hasDerivAt z (hd z)).const_mul
        (-Complex.I)
      convert! hp.cexp using 1; simp only [Function.comp_apply]; ring) ζ
  simpa only [complexSpatialFourier, complexSpatialPhase_apply, neg_mul] using h

theorem analyticOnNhd_complexSourceWave_curve (u : TimeZeroSource)
    (q dq : ℂ → ComplexSpacetime) (hq : Continuous q) (hdq : Continuous dq)
    (hd : ∀ ζ, HasDerivAt q (dq ζ) ζ) :
    AnalyticOnNhd ℂ (fun ζ => complexSourceWave u (q ζ)) Set.univ := by
  have hf : Differentiable ℂ (fun ζ => complexSpatialFourier u.1 (q ζ).2) :=
    fun ζ => (hasDerivAt_complexSpatialFourier_curve u.1 q dq hq hdq hd ζ).differentiableAt
  have hg : Differentiable ℂ (fun ζ => complexSpatialFourier u.2 (q ζ).2) :=
    fun ζ => (hasDerivAt_complexSpatialFourier_curve u.2 q dq hq hdq hd ζ).differentiableAt
  have he : Differentiable ℂ (fun ζ => (q ζ).1) := by
    intro ζ
    exact ((ContinuousLinearMap.fst ℂ ℂ (Fin 3 → ℂ)).hasFDerivAt.comp_hasDerivAt ζ
      (hd ζ)).differentiableAt
  have hi : Differentiable ℂ (fun _ : ℂ => Complex.I) := differentiable_const _
  have htotal := hf.add ((hi.mul he).mul hg)
  intro ζ _
  exact htotal.analyticAt ζ

/-- Complex shell boost derivative. -/
noncomputable def complexShellBoostDerivative (m : ℝ) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : ComplexSpacetime :=
  ((dispersion m p : ℂ) * Complex.sinh ζ + (p 0 : ℂ) * Complex.cosh ζ,
    ![(p 0 : ℂ) * Complex.sinh ζ + (dispersion m p : ℂ) * Complex.cosh ζ, 0, 0])

theorem hasDerivAt_complexShellBoost (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (ζ : ℂ) :
    HasDerivAt (fun z => complexShellBoost m z p) (complexShellBoostDerivative m ζ p) ζ := by
  apply HasDerivAt.prodMk
  · exact ((Complex.hasDerivAt_cosh ζ).const_mul (dispersion m p : ℂ)).add
      ((Complex.hasDerivAt_sinh ζ).const_mul (p 0 : ℂ))
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((Complex.hasDerivAt_cosh ζ).const_mul (p 0 : ℂ)).add
        ((Complex.hasDerivAt_sinh ζ).const_mul (dispersion m p : ℂ))
    · exact hasDerivAt_const ζ (p 1 : ℂ)
    · exact hasDerivAt_const ζ (p 2 : ℂ)

theorem analyticOnNhd_complexSourceWave_lorentzBoost (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (u : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) :
    AnalyticOnNhd ℂ (fun ζ => complexSourceWave u
      (complexifiedSpacetimeMap Λ (complexShellBoost m ζ p))) Set.univ := by
  apply analyticOnNhd_complexSourceWave_curve u
    (fun ζ => complexifiedSpacetimeMap Λ (complexShellBoost m ζ p))
    (fun ζ => complexifiedSpacetimeMap Λ (complexShellBoostDerivative m ζ p))
  · apply (complexifiedSpacetimeMap Λ).continuous.comp
    unfold complexShellBoost
    fun_prop
  · apply (complexifiedSpacetimeMap Λ).continuous.comp
    unfold complexShellBoostDerivative
    fun_prop
  · intro ζ
    exact (complexifiedSpacetimeMap Λ).hasFDerivAt.comp_hasDerivAt ζ
      (hasDerivAt_complexShellBoost m p ζ)

end VacuumBellSeparation
