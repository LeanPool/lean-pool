/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityRealDerivative.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityInterior
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ginibre transition analytic local regularity real derivative

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_complex_weak_derivative_real`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]

theorem ginibreLocalRegularity_complex_weak_derivative_real
    (u : E → ℝ) (hu : MemLp u 2 (volume : Measure E))
    (g : Lp ℂ 2 (volume : Measure E)) (v : E)
    (hg : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*(u x : ℂ))) :
    ∃ gr : E → ℝ, MemLp gr 2 (volume : Measure E) ∧
      ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ x, θ x*gr x) = -(∫ x, fderiv ℝ θ x v*u x) := by
  refine ⟨fun x => (g x).re, Complex.reCLM.comp_memLp g, ?_⟩
  intro θ hθ hc
  let ψ := fun x => (θ x : ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hθ
  have hψc : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
  have hd (x : E) : fderiv ℝ ψ x v = (fderiv ℝ θ x v : ℂ) := by
    have hh := Complex.ofRealCLM.hasFDerivAt.comp x ((hθ.differentiable (by
        simp)).differentiableAt.hasFDerivAt)
    exact congrArg (fun L => L v) hh.fderiv
  have he := congrArg Complex.re (hg ψ hψ hψc)
  have hi : Integrable (fun x => ψ x*g x) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      ((MeasureTheory.Lp.memLp g).locallyIntegrable (by
          norm_num)).integrable_smul_right_of_hasCompactSupport hψ.continuous hψc
  have hr : Integrable (fun x => fderiv ℝ ψ x v*(u x : ℂ)) volume := by
    have hq : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
      (hψ.fderiv_right (by simp)).clm_apply contDiff_const
    have hqc := hψc.fderiv_apply ℝ v
    have hh := ((hu.ofReal (K := ℂ)).locallyIntegrable (by
        norm_num)).integrable_smul_right_of_hasCompactSupport hq.continuous hqc
    apply hh.congr
    exact ae_of_all volume fun x => by dsimp only; simp only [smul_eq_mul]; exact mul_comm _ _
  have hil := Complex.reCLM.integral_comp_comm hi
  have hrl := Complex.reCLM.integral_comp_comm hr
  change (∫ x, (ψ x*g x).re) = (∫ x, ψ x*g x).re at hil
  change (∫ x, (fderiv ℝ ψ x v*(u x : ℂ)).re) = (∫ x, fderiv ℝ ψ x v*(u x : ℂ)).re at hrl
  rw [← hil, Complex.neg_re, ← hrl] at he
  simpa only [ψ, hd, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero] using he

end
end GinibrePoincare
