/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryCauchyGreenIBP.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenLimit
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Correspondence auxiliary Cauchy Green IBP

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `cauchyGreenRegularizedKernel_test_identity`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Ordinary planar Wirtinger integration by parts with a compact test;
the differentiated function need not have compact support. -/
theorem planarDbar_compact_integrationByParts (f θ : ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, f z * planarDbar θ z) = -(∫ z : ℂ, planarDbar f z * θ z) := by
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
  have hleft : (∫ z : ℂ, f z * planarDbar θ z) =
      (1/2 : ℂ) * ((∫ z : ℂ, f z * fderiv ℝ θ z 1) +
        Complex.I*(∫ z : ℂ, f z * fderiv ℝ θ z Complex.I)) := by
    have he : (fun z : ℂ => f z * planarDbar θ z) =
        (fun z : ℂ => (1/2 : ℂ)*(f z*fderiv ℝ θ z 1 +
          Complex.I*(f z*fderiv ℝ θ z Complex.I))) := by
      funext z
      unfold planarDbar
      ring
    rw [he, integral_const_mul, integral_add (hi1 1) ((hi1 Complex.I).const_mul Complex.I),
      integral_const_mul]
  have hright : (∫ z : ℂ, planarDbar f z * θ z) =
      (1/2 : ℂ) * ((∫ z : ℂ, fderiv ℝ f z 1 * θ z) +
        Complex.I*(∫ z : ℂ, fderiv ℝ f z Complex.I * θ z)) := by
    have he : (fun z : ℂ => planarDbar f z * θ z) =
        (fun z : ℂ => (1/2 : ℂ)*(fderiv ℝ f z 1*θ z +
          Complex.I*(fderiv ℝ f z Complex.I*θ z))) := by
      funext z
      unfold planarDbar
      ring
    rw [he, integral_const_mul, integral_add (hi2 1) ((hi2 Complex.I).const_mul Complex.I),
      integral_const_mul]
  rw [hleft, hright, hibp 1, hibp Complex.I]
  ring

theorem cauchyGreenRegularizedKernel_test_identity (τ : ℝ) (hτ : 0 < τ)
    (θ : ℂ → ℂ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, cauchyGreenRegularizedKernel τ z * planarDbar θ z) =
      -(∫ z : ℂ, ((τ / (Real.pi*(Complex.normSq z+τ)^2) : ℝ) : ℂ) * θ z) := by
  rw [planarDbar_compact_integrationByParts _ _
    ((cauchyGreenRegularizedKernel_contDiff τ hτ).of_le (by simp)) hθ hc]
  simp_rw [cauchyGreenRegularizedKernel_dbar τ hτ]

end
end GinibrePoincare
