/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryJointMollification.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryJointCauchyRiemann
public import LeanPool.GinibrePoincare.Analysis.WeakDerivativeMollification

/-!
# Correspondence auxiliary joint mollification

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `configurationComplexMollification_holomorphic`.
-/

@[expose] public section
open MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution
namespace GinibrePoincare
noncomputable section
variable {n : ℕ}

/-- Literal derivative-under-integral formula for real compact smoothing. -/
theorem configuration_scalar_convolution_derivative (u φ : Configuration n → ℝ) (v x : Configuration
    n)
    (hu : LocallyIntegrable u volume) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u) x v =
      ∫ y, fderiv ℝ φ (x - y) v * u y := by
  have hd := hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    (hφ.of_le (by simp)) hu x
  rw [hd.fderiv, convolution_eq_swap]
  have hi := ((hc.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL (Configuration n)) (hφ.continuous_fderiv (by simp)) hu x).integrable_swap
  rw [ContinuousLinearMap.integral_apply hi v]
  simp only [precompL_apply, lsmul_apply, smul_eq_mul]

private theorem configuration_component_locallyIntegrable (U : Configuration n → ℂ)
    (hu : LocallyIntegrable U volume) (T : ℂ →L[ℝ] ℝ) :
    LocallyIntegrable (fun z => T (U z)) volume := by
  intro x
  obtain ⟨s, hs, hi⟩ := hu x
  exact ⟨s, hs, T.integrable_comp hi⟩

/-- Literal smooth complex mollification, formed from the two real components. -/
def configurationComplexMollification (φ : Configuration n → ℝ) (U : Configuration n → ℂ) (x :
    Configuration n) : ℂ :=
  ((φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)) x : ℂ) +
    Complex.I * ((φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)) x : ℂ)

/-- Distributional Cauchy–Riemann equations pass to the actual smooth
convolution as classical pointwise Cauchy–Riemann equations. -/
theorem configuration_cauchyRiemann_convolution (U : Configuration n → ℂ)
    (hu : LocallyIntegrable U volume)
    (htest : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → ∀ j : Fin n,
      (∫ y, (U y).re * fderiv ℝ θ y (realCoordinateDirection j) - (U y).im * fderiv ℝ θ y
          (imaginaryCoordinateDirection j)) = 0 ∧
      (∫ y, (U y).im * fderiv ℝ θ y (realCoordinateDirection j) + (U y).re * fderiv ℝ θ y
          (imaginaryCoordinateDirection j)) = 0)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (x : Configuration n)
        (j : Fin n) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)) x (realCoordinateDirection j) -
      fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)) x (imaginaryCoordinateDirection j) = 0 ∧
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)) x (realCoordinateDirection j) +
      fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)) x (imaginaryCoordinateDirection j) = 0
          := by
  have hur := configuration_component_locallyIntegrable U hu Complex.reCLM
  have hui := configuration_component_locallyIntegrable U hu Complex.imCLM
  let θ := fun y : Configuration n => φ (x - y)
  have hθ : ContDiff ℝ ∞ θ := hφ.comp (contDiff_const.sub contDiff_id)
  have hθc : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hDθ (y v : Configuration n) : fderiv ℝ θ y v = -fderiv ℝ φ (x - y) v := by
    have hd := (hφ.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [show θ = φ ∘ (fun y : Configuration n => x - y) from rfl, hd.fderiv]
    simp
  have hi (v : Configuration n) (T : ℂ →L[ℝ] ℝ) :
      Integrable (fun y => fderiv ℝ φ (x - y) v * T (U y)) volume := by
    have hDc : HasCompactSupport (fun y => fderiv ℝ φ (x - y) v) :=
      (hc.fderiv_apply ℝ v).comp_homeomorph (Homeomorph.subLeft x)
    have hD : Continuous (fun y => fderiv ℝ φ (x - y) v) :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id)
    simpa only [smul_eq_mul] using
      (configuration_component_locallyIntegrable U hu T).integrable_smul_left_of_hasCompactSupport
          hD hDc
  obtain ⟨hx, hy⟩ := htest θ hθ hθc j
  have hpx (y : Configuration n) : (U y).re * fderiv ℝ θ y (realCoordinateDirection j) - (U y).im *
      fderiv ℝ θ y (imaginaryCoordinateDirection j) =
      -(fderiv ℝ φ (x - y) (realCoordinateDirection j) * (U y).re - fderiv ℝ φ (x - y)
          (imaginaryCoordinateDirection j) * (U y).im) := by
    rw [hDθ, hDθ]
    ring
  have hpy (y : Configuration n) : (U y).im * fderiv ℝ θ y (realCoordinateDirection j) + (U y).re *
      fderiv ℝ θ y (imaginaryCoordinateDirection j) =
      -(fderiv ℝ φ (x - y) (realCoordinateDirection j) * (U y).im + fderiv ℝ φ (x - y)
          (imaginaryCoordinateDirection j) * (U y).re) := by
    rw [hDθ, hDθ]
    ring
  simp_rw [hpx] at hx
  simp_rw [hpy] at hy
  rw [integral_neg, integral_sub
    (f := fun y => fderiv ℝ φ (x - y) (realCoordinateDirection j) * (U y).re)
    (g := fun y => fderiv ℝ φ (x - y) (imaginaryCoordinateDirection j) * (U y).im)
    (hi (realCoordinateDirection j) Complex.reCLM) (hi (imaginaryCoordinateDirection j)
        Complex.imCLM)] at hx
  rw [integral_neg, integral_add
    (f := fun y => fderiv ℝ φ (x - y) (realCoordinateDirection j) * (U y).im)
    (g := fun y => fderiv ℝ φ (x - y) (imaginaryCoordinateDirection j) * (U y).re)
    (hi (realCoordinateDirection j) Complex.imCLM) (hi (imaginaryCoordinateDirection j)
        Complex.reCLM)] at hy
  rw [configuration_scalar_convolution_derivative (fun y => (U y).re) φ (realCoordinateDirection j)
      x hur hφ hc,
    configuration_scalar_convolution_derivative (fun y => (U y).im) φ (imaginaryCoordinateDirection
        j) x hui hφ hc,
    configuration_scalar_convolution_derivative (fun y => (U y).im) φ (realCoordinateDirection j) x
        hui hφ hc,
    configuration_scalar_convolution_derivative (fun y => (U y).re) φ (imaginaryCoordinateDirection
        j) x hur hφ hc]
  constructor <;> linarith

/-- Every actual smooth compact mollification of a locally integrable joint
Cauchy–Riemann distribution is jointly entire. -/
theorem configurationComplexMollification_holomorphic (U : Configuration n → ℂ)
    (hu : LocallyIntegrable U volume)
    (htest : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ∀ j : Fin n,
      (∫ y, (U y).re * fderiv ℝ θ y (realCoordinateDirection j) -
        (U y).im * fderiv ℝ θ y (imaginaryCoordinateDirection j)) = 0 ∧
      (∫ y, (U y).im * fderiv ℝ θ y (realCoordinateDirection j) +
        (U y).re * fderiv ℝ θ y (imaginaryCoordinateDirection j)) = 0)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Differentiable ℂ (configurationComplexMollification φ U) := by
  let R := φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)
  let S := φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)
  have hur := configuration_component_locallyIntegrable U hu Complex.reCLM
  have hui := configuration_component_locallyIntegrable U hu Complex.imCLM
  have hR : ContDiff ℝ ∞ R := hc.contDiff_convolution_left (lsmul ℝ ℝ) hφ hur
  have hS : ContDiff ℝ ∞ S := hc.contDiff_convolution_left (lsmul ℝ ℝ) hφ hui
  have hF : ContDiff ℝ ∞ (configurationComplexMollification φ U) :=
    (Complex.ofRealCLM.contDiff.comp hR).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hS))
  intro x
  have hparts (v : Configuration n) :
      fderiv ℝ (configurationComplexMollification φ U) x v =
        (fderiv ℝ R x v : ℂ) + Complex.I*(fderiv ℝ S x v : ℂ) := by
    have h1 := Complex.ofRealCLM.hasFDerivAt.comp x
      (hR.differentiable (by simp) x).hasFDerivAt
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp x
      (hS.differentiable (by simp) x).hasFDerivAt).const_mul Complex.I
    have hh := congrArg (fun L : Configuration n →L[ℝ] ℂ => L v) (h1.add h2).fderiv
    have hfun : (Complex.ofRealCLM ∘ R + fun y => Complex.I*(Complex.ofRealCLM ∘ S) y) =
        (fun w => (R w : ℂ)+Complex.I*(S w : ℂ)) := by funext w; rfl
    rw [hfun] at hh
    change fderiv ℝ (fun w => (R w : ℂ)+Complex.I*(S w : ℂ)) x v = _
    simpa only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, Pi.add_apply,
          Function.comp_def] using hh
  apply (hasFDerivAt_complex_of_coordinate_CR (hF.differentiable (by simp) x).hasFDerivAt
      ?_).differentiableAt
  intro j
  have hCR := configuration_cauchyRiemann_convolution U hu htest φ hφ hc x j
  rw [hparts, hparts]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im]
    dsimp [R, S] at *
    linarith [hCR.2]
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im]
    dsimp [R, S] at *
    linarith [hCR.1]

end
end GinibrePoincare
