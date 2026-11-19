/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceLogRegularized.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenFundamental
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogIntegrability
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Correspondence log regularized

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `planarPartial_compact_integrationByParts`, `correspondenceLogRegularized_contDiff`,
`correspondenceLogRegularized_partial`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The Wirtinger derivative `∂f = (∂ₓf - i ∂_y f) / 2`, written with real directional
derivatives along `1` and `Complex.I`. -/
def planarPartial (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/2 : ℂ)*(fderiv ℝ f z 1 - Complex.I*fderiv ℝ f z Complex.I)

/-- Ordinary planar Wirtinger integration by parts with a compact test;
the differentiated function need not have compact support. -/
theorem planarPartial_compact_integrationByParts (f θ : ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, f z * planarPartial θ z) = -(∫ z : ℂ, planarPartial f z * θ z) := by
  have hdf (v : ℂ) : Continuous (fun z => fderiv ℝ f z v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdθ (v : ℂ) : Continuous (fun z => fderiv ℝ θ z v) :=
    (hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 (v : ℂ) : Integrable (fun z => f z * fderiv ℝ θ z v) volume :=
    (hf.continuous.mul (hdθ v)).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ v).mul_left)
  have hi2 (v : ℂ) : Integrable (fun z => fderiv ℝ f z v * θ z) volume :=
    ((hdf v).mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hibp (v : ℂ) : (∫ z : ℂ, f z * fderiv ℝ θ z v) =
      -(∫ z : ℂ, fderiv ℝ f z v * θ z) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (hi2 v) (hi1 v)
      ((hf.continuous.mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun z _ => (hf.differentiable (by norm_num)).differentiableAt)
      (fun z _ => (hθ.differentiable (by norm_num)).differentiableAt)
  have hleft : (∫ z : ℂ, f z * planarPartial θ z) =
      (1/2 : ℂ) * ((∫ z : ℂ, f z * fderiv ℝ θ z 1) -
        Complex.I*(∫ z : ℂ, f z * fderiv ℝ θ z Complex.I)) := by
    have he : (fun z : ℂ => f z * planarPartial θ z) =
        (fun z : ℂ => (1/2 : ℂ)*(f z*fderiv ℝ θ z 1 -
          Complex.I*(f z*fderiv ℝ θ z Complex.I))) := by
      funext z
      unfold planarPartial
      ring
    rw [he, integral_const_mul, integral_sub (hi1 1) ((hi1 Complex.I).const_mul Complex.I),
      integral_const_mul]
  have hright : (∫ z : ℂ, planarPartial f z * θ z) =
      (1/2 : ℂ) * ((∫ z : ℂ, fderiv ℝ f z 1 * θ z) -
        Complex.I*(∫ z : ℂ, fderiv ℝ f z Complex.I * θ z)) := by
    have he : (fun z : ℂ => planarPartial f z * θ z) =
        (fun z : ℂ => (1/2 : ℂ)*(fderiv ℝ f z 1*θ z -
          Complex.I*(fderiv ℝ f z Complex.I*θ z))) := by
      funext z
      unfold planarPartial
      ring
    rw [he, integral_const_mul, integral_sub (hi2 1) ((hi2 Complex.I).const_mul Complex.I),
      integral_const_mul]
  rw [hleft, hright, hibp 1, hibp Complex.I]
  ring

/-- The regularized logarithm `Real.log (Complex.normSq z + τ) / 2`. -/
def correspondenceLogRegularized (τ : ℝ) (z : ℂ) : ℝ :=
  (1/2 : ℝ)*Real.log (Complex.normSq z+τ)

private theorem normSq_hasFDerivAt (z : ℂ) :
    HasFDerivAt Complex.normSq
      ((2*z.re) • Complex.reCLM + (2*z.im) • Complex.imCLM) z := by
  have h := (Complex.reCLM.hasFDerivAt (x := z)).mul (Complex.reCLM.hasFDerivAt (x := z))
  have h' := (Complex.imCLM.hasFDerivAt (x := z)).mul (Complex.imCLM.hasFDerivAt (x := z))
  convert h.add h' using 1
  · exact funext Complex.normSq_apply
  · ext v
    simp
    ring

theorem correspondenceLogRegularized_contDiff (τ : ℝ) (hτ : 0 < τ) :
    ContDiff ℝ ∞ (correspondenceLogRegularized τ) := by
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    simpa only [Complex.normSq_apply] using!
      (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact contDiff_const.mul ((hn.add contDiff_const).log
    (fun z => ((Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ)).ne'))

theorem correspondenceLogRegularized_partial (τ : ℝ) (hτ : 0 < τ) (z : ℂ) :
    planarPartial (fun w => (correspondenceLogRegularized τ w : ℂ)) z =
      (Real.pi/2 : ℂ)*cauchyGreenRegularizedKernel τ z := by
  have hd : Complex.normSq z+τ ≠ 0 :=
    ((Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ)).ne'
  have h := (Complex.ofRealCLM.hasFDerivAt (x := correspondenceLogRegularized τ z)).comp z
    ((((normSq_hasFDerivAt z).add_const τ).log hd).const_mul (1/2 : ℝ))
  unfold planarPartial
  change (1/2 : ℂ)*(fderiv ℝ (Complex.ofRealCLM ∘ correspondenceLogRegularized τ) z 1 -
    Complex.I*fderiv ℝ (Complex.ofRealCLM ∘ correspondenceLogRegularized τ) z Complex.I) = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    add_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    smul_eq_mul, mul_one, mul_zero, zero_add, add_zero]
  unfold cauchyGreenRegularizedKernel
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.div_re, Complex.div_im, Complex.normSq_ofReal, Complex.conj_re, Complex.conj_im]
  all_goals field_simp [hd, Real.pi_ne_zero]
  all_goals norm_num
  all_goals ring

end
end GinibrePoincare
