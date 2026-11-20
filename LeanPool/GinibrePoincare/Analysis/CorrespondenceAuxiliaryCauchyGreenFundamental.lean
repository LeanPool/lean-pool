/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryCauchyGreenFundamental.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenIBP
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogApproximation

/-!
# Correspondence auxiliary Cauchy Green fundamental

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `cauchyGreenKernel_fundamental_identity`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem planarDbar_continuous (θ : ℂ → ℂ) (hθ : ContDiff ℝ 1 θ) :
    Continuous (planarDbar θ) := by
  exact continuous_const.mul
    (((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      (continuous_const.mul ((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem planarDbar_compact (θ : ℂ → ℂ) (hc : HasCompactSupport θ) :
    HasCompactSupport (planarDbar θ) := by
  exact ((hc.fderiv_apply ℝ 1).add
    ((hc.fderiv_apply ℝ Complex.I).mul_left (f := fun _ => Complex.I))).mul_left
      (f := fun _ => (1/2 : ℂ))

/-- Literal ordinary-test fundamental solution identity ∂bar(1/(πz))=δ₀. -/
theorem cauchyGreenKernel_fundamental_identity (θ : ℂ → ℂ)
    (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, cauchyGreenKernel z * planarDbar θ z) = -θ 0 := by
  have hl := cauchyGreenRegularizedKernel_integral_tendsto (planarDbar θ)
    (planarDbar_continuous θ hθ) (planarDbar_compact θ hc)
  have hr := (correspondenceLogKernel_test_limit θ
    (hθ.continuous.integrable_of_hasCompactSupport hc) hθ.continuous.continuousAt).neg
  have he : (fun τ : ℝ => ∫ z : ℂ, cauchyGreenRegularizedKernel τ z * planarDbar θ z)
      =ᶠ[𝓝[>] 0] (fun τ : ℝ => -(∫ z : ℂ, correspondenceLogKernel τ z • θ z)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simpa only [correspondenceLogKernel, Complex.real_smul] using
      cauchyGreenRegularizedKernel_test_identity τ hτ θ hθ hc
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

end
end GinibrePoincare
