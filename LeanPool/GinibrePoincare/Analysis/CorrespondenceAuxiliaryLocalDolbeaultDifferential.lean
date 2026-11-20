/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultDifferential.lean.
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
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticFiniteDerivativeConvolution
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Correspondence auxiliary local Dolbeault differential

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `real_directional_fderiv`, `localDolbeault_smooth_residual_CR`.
-/

@[expose] public section
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_directional_fderiv (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd := ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) x).hasFDerivAt
  have h := ((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt).comp x hd
  have he : (fun y => fderiv ℝ f y v) =
      (ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ f := rfl
  rw [he, h.fderiv]
  rfl

theorem finiteComplexDbar_contDiff (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (v w : E) :
    ContDiff ℝ ∞ (finiteComplexDbar v w f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact contDiff_const.mul
    ((hd.clm_apply contDiff_const).add (contDiff_const.mul (hd.clm_apply contDiff_const)))

theorem finiteComplexDbar_fderiv (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x v w b : E) :
    fderiv ℝ (finiteComplexDbar v w f) x b =
      (1/2 : ℂ)*(fderiv ℝ (fderiv ℝ f) x b v +
        Complex.I*fderiv ℝ (fderiv ℝ f) x b w) := by
  have hd := ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hv := ((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt).comp x hd
  have hw := ((ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt).comp x hd
  have h := (hv.add (hw.const_mul Complex.I)).const_mul (1/2 : ℂ)
  have h' : HasFDerivAt (finiteComplexDbar v w f)
      ((1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ f) x) +
        Complex.I • (ContinuousLinearMap.apply ℝ ℂ w).comp (fderiv ℝ (fderiv ℝ f) x))) x := by
    simpa only [finiteComplexDbar, Function.comp_def, Pi.add_apply] using! h
  rw [h'.fderiv]
  simp
  ring

/-- Actual Wirtinger coordinate operators commute on smooth functions,
proved from real second-derivative symmetry. -/
theorem finiteComplexDbar_commute (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (v w a b x : E) :
    finiteComplexDbar v w (finiteComplexDbar a b f) x =
      finiteComplexDbar a b (finiteComplexDbar v w f) x := by
  have hsym : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  simp only [finiteComplexDbar]
  change (1/2 : ℂ)*(fderiv ℝ (finiteComplexDbar a b f) x v +
    Complex.I*fderiv ℝ (finiteComplexDbar a b f) x w) =
    (1/2 : ℂ)*(fderiv ℝ (finiteComplexDbar v w f) x a +
      Complex.I*fderiv ℝ (finiteComplexDbar v w f) x b)
  rw [finiteComplexDbar_fderiv f hf x a b v, finiteComplexDbar_fderiv f hf x a b w,
    finiteComplexDbar_fderiv f hf x v w a, finiteComplexDbar_fderiv f hf x v w b,
    hsym v a, hsym v b, hsym w a, hsym w b]
  ring

theorem finiteComplexDbar_sub (f g : E → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v w x : E) :
    finiteComplexDbar v w (f-g) x = finiteComplexDbar v w f x - finiteComplexDbar v w g x := by
  simp only [finiteComplexDbar, fderiv_sub (hf x) (hg x), sub_apply]
  ring

/-- Removing one genuinely solved component of a smooth closed form makes
every remaining component holomorphic in that coordinate. Closedness may
hold only on the neighborhood under consideration. -/
theorem localDolbeault_smooth_residual_CR (f g u : E → ℂ)
    (_ : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u)
    (v w a b x : E)
    (hsolve : finiteComplexDbar v w u = f)
    (hclosed : finiteComplexDbar a b f x = finiteComplexDbar v w g x) :
    finiteComplexDbar v w (g-finiteComplexDbar a b u) x = 0 := by
  rw [finiteComplexDbar_sub g _ (hg.differentiable (by simp))
    ((finiteComplexDbar_contDiff u hu a b).differentiable (by simp)),
    finiteComplexDbar_commute u hu v w a b x, hsolve,← hclosed, sub_self]

end
end GinibrePoincare
