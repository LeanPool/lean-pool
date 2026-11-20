/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticDbarMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticDbarGauge
public import LeanPool.GinibrePoincare.Analysis.WeakDerivativeMollification

/-! # Holomorphic mollification of the concrete weak ∂bar kernel -/

@[expose] public section
open MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution
namespace GinibrePoincare
noncomputable section

/-- Vanishing actual ∂bar plus real differentiability implies complex
differentiability, by constructing the complex-linear derivative. -/
theorem differentiableAt_complex_of_planarDbar_zero (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) (hzero : planarDbar f z = 0) :
    DifferentiableAt ℂ f z := by
  let L := fderiv ℝ f z
  have hh : L 1 + Complex.I * L Complex.I = 0 := by
    unfold planarDbar at hzero
    change (1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I) = 0 at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  have hI : L Complex.I = Complex.I * L 1 := by
    have hII := Complex.I_mul_I
    linear_combination -Complex.I * hh + L Complex.I * hII
  apply (differentiableAt_iff_restrictScalars ℝ hf).mpr
  refine ⟨L 1 • ContinuousLinearMap.id ℂ ℂ, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change L 1 * v = L v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp [Complex.real_smul]
  have hLv : L v = (v.re : ℂ) * L 1 + (v.im : ℂ) * L Complex.I := by
    conv_lhs => rw [hv]
    rw [L.map_add, L.map_smul, L.map_smul]
    simp only [Complex.real_smul]
  rw [hLv, hI]
  calc
    _ = L 1 * ((v.re : ℂ) + (v.im : ℂ) * Complex.I) :=
      congrArg (fun w => L 1 * w) (Complex.re_add_im v).symm
    _ = _ := by ring

/-- Literal derivative-under-integral formula for real compact smoothing. -/
theorem planar_scalar_convolution_derivative (u φ : ℂ → ℝ) (v x : ℂ)
    (hu : LocallyIntegrable u volume) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u) x v =
      ∫ y, fderiv ℝ φ (x - y) v * u y := by
  have hd := hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    (hφ.of_le (by simp)) hu x
  rw [hd.fderiv, convolution_eq_swap]
  have hi := ((hc.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL ℂ) (hφ.continuous_fderiv (by simp)) hu x).integrable_swap
  rw [ContinuousLinearMap.integral_apply hi v]
  simp only [precompL_apply, lsmul_apply, smul_eq_mul]

private theorem planar_component_locallyIntegrable (U : ℂ → ℂ)
    (hu : LocallyIntegrable U volume) (T : ℂ →L[ℝ] ℝ) :
    LocallyIntegrable (fun z => T (U z)) volume := by
  intro x
  obtain ⟨s, hs, hi⟩ := hu x
  exact ⟨s, hs, T.integrable_comp hi⟩

/-- Literal smooth complex mollification, formed from the two real components. -/
def planarComplexMollification (φ : ℂ → ℝ) (U : ℂ → ℂ) (x : ℂ) : ℂ :=
  ((φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)) x : ℂ) +
    Complex.I * ((φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)) x : ℂ)

/-- Distributional Cauchy–Riemann equations pass to the actual smooth
convolution as classical pointwise Cauchy–Riemann equations. -/
theorem planar_cauchyRiemann_convolution (U : ℂ → ℂ)
    (hu : LocallyIntegrable U volume)
    (htest : ∀ θ : ℂ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y, (U y).re * fderiv ℝ θ y 1 - (U y).im * fderiv ℝ θ y Complex.I) = 0 ∧
      (∫ y, (U y).im * fderiv ℝ θ y 1 + (U y).re * fderiv ℝ θ y Complex.I) = 0)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (x : ℂ) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)) x 1 -
      fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)) x Complex.I = 0 ∧
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)) x 1 +
      fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)) x Complex.I = 0 := by
  have hur := planar_component_locallyIntegrable U hu Complex.reCLM
  have hui := planar_component_locallyIntegrable U hu Complex.imCLM
  let θ := fun y : ℂ => φ (x - y)
  have hθ : ContDiff ℝ ∞ θ := hφ.comp (contDiff_const.sub contDiff_id)
  have hθc : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hDθ (y v : ℂ) : fderiv ℝ θ y v = -fderiv ℝ φ (x - y) v := by
    have hd := (hφ.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [show θ = φ ∘ (fun y : ℂ => x - y) from rfl, hd.fderiv]
    simp
  have hi (v : ℂ) (T : ℂ →L[ℝ] ℝ) :
      Integrable (fun y => fderiv ℝ φ (x - y) v * T (U y)) volume := by
    have hDc : HasCompactSupport (fun y => fderiv ℝ φ (x - y) v) :=
      (hc.fderiv_apply ℝ v).comp_homeomorph (Homeomorph.subLeft x)
    have hD : Continuous (fun y => fderiv ℝ φ (x - y) v) :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id)
    simpa only [smul_eq_mul] using
      (planar_component_locallyIntegrable U hu T).integrable_smul_left_of_hasCompactSupport hD hDc
  obtain ⟨hx, hy⟩ := htest θ hθ hθc
  have hpx (y : ℂ) : (U y).re * fderiv ℝ θ y 1 - (U y).im * fderiv ℝ θ y Complex.I =
      -(fderiv ℝ φ (x - y) 1 * (U y).re - fderiv ℝ φ (x - y) Complex.I * (U y).im) := by
    rw [hDθ, hDθ]
    ring
  have hpy (y : ℂ) : (U y).im * fderiv ℝ θ y 1 + (U y).re * fderiv ℝ θ y Complex.I =
      -(fderiv ℝ φ (x - y) 1 * (U y).im + fderiv ℝ φ (x - y) Complex.I * (U y).re) := by
    rw [hDθ, hDθ]
    ring
  simp_rw [hpx] at hx
  simp_rw [hpy] at hy
  rw [integral_neg, integral_sub
    (f := fun y => fderiv ℝ φ (x - y) 1 * (U y).re)
    (g := fun y => fderiv ℝ φ (x - y) Complex.I * (U y).im)
    (hi 1 Complex.reCLM) (hi Complex.I Complex.imCLM)] at hx
  rw [integral_neg, integral_add
    (f := fun y => fderiv ℝ φ (x - y) 1 * (U y).im)
    (g := fun y => fderiv ℝ φ (x - y) Complex.I * (U y).re)
    (hi 1 Complex.imCLM) (hi Complex.I Complex.reCLM)] at hy
  rw [planar_scalar_convolution_derivative (fun y => (U y).re) φ 1 x hur hφ hc,
    planar_scalar_convolution_derivative (fun y => (U y).im) φ Complex.I x hui hφ hc,
    planar_scalar_convolution_derivative (fun y => (U y).im) φ 1 x hui hφ hc,
    planar_scalar_convolution_derivative (fun y => (U y).re) φ Complex.I x hur hφ hc]
  constructor <;> linarith

/-- A locally integrable CR distribution has genuinely entire smooth
mollifications, for every compact smooth real convolution kernel. -/
theorem planarComplexMollification_holomorphic (U : ℂ → ℂ)
    (hu : LocallyIntegrable U volume)
    (htest : ∀ θ : ℂ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y, (U y).re * fderiv ℝ θ y 1 - (U y).im * fderiv ℝ θ y Complex.I) = 0 ∧
      (∫ y, (U y).im * fderiv ℝ θ y 1 + (U y).re * fderiv ℝ θ y Complex.I) = 0)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Differentiable ℂ (planarComplexMollification φ U) := by
  let R := φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).re)
  let S := φ ⋆[lsmul ℝ ℝ, volume] (fun y => (U y).im)
  have hur := planar_component_locallyIntegrable U hu Complex.reCLM
  have hui := planar_component_locallyIntegrable U hu Complex.imCLM
  have hR : ContDiff ℝ ∞ R := hc.contDiff_convolution_left (lsmul ℝ ℝ) hφ hur
  have hS : ContDiff ℝ ∞ S := hc.contDiff_convolution_left (lsmul ℝ ℝ) hφ hui
  have hF : ContDiff ℝ ∞ (planarComplexMollification φ U) :=
    (Complex.ofRealCLM.contDiff.comp hR).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hS))
  have hre : (fun z => (planarComplexMollification φ U z).re) = R := by
    funext z
    simp [planarComplexMollification, R]
  have him : (fun z => (planarComplexMollification φ U z).im) = S := by
    funext z
    simp [planarComplexMollification, S]
  intro z
  apply differentiableAt_complex_of_planarDbar_zero _ z (hF.differentiable (by simp) z)
  have he := planarDbarOfParts_eq (planarComplexMollification φ U)
    (hF.differentiable (by simp)) z
  rw [hre, him] at he
  rw [← he]
  have hCR := planar_cauchyRiemann_convolution U hu htest φ hφ hc z
  apply Complex.ext
  · change (fderiv ℝ R z 1 - fderiv ℝ S z Complex.I) / 2 = 0
    rw [show fderiv ℝ R z 1 - fderiv ℝ S z Complex.I = 0 from hCR.1]
    simp
  · change (fderiv ℝ S z 1 + fderiv ℝ R z Complex.I) / 2 = 0
    rw [show fderiv ℝ S z 1 + fderiv ℝ R z Complex.I = 0 from hCR.2]
    simp

/-- Every smooth compact convolution of an actual weighted ∂bar-kernel
representative is genuinely holomorphic on the entire plane. -/
theorem planarWeakDbarKernel_holomorphic_mollification
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (u : PlanarLebesgueL2)
    (hu : u ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num)))
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Differentiable ℂ (planarComplexMollification φ (planarUngaugedL2Function n V u)) := by
  apply planarComplexMollification_holomorphic _
    (planarUngaugedL2Function_locallyIntegrable n V hV.continuous u) _ φ hφ hc
  intro θ hθ hθc
  exact planarWeakDbarKernel_cauchyRiemann_test_equations n V hV u hu θ
    (hθ.of_le (by decide)) hθc

end
end GinibrePoincare
