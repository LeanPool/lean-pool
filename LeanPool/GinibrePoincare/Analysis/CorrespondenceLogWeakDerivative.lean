/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceLogWeakDerivative.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogLimit

/-!
# Correspondence log weak derivative

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `correspondenceLogPotential_weak_partial`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem planarPartial_continuous (θ : ℂ → ℂ) (hθ : ContDiff ℝ 1 θ) :
    Continuous (planarPartial θ) := by
  exact continuous_const.mul
    (((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
      (continuous_const.mul ((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem planarPartial_compact (θ : ℂ → ℂ) (hc : HasCompactSupport θ) :
    HasCompactSupport (planarPartial θ) := by
  exact ((hc.fderiv_apply ℝ 1).sub
    ((hc.fderiv_apply ℝ Complex.I).mul_left (f := fun _ => Complex.I))).mul_left
      (f := fun _ => (1/2 : ℂ))

/-- Actual distributional holomorphic derivative of the locally integrable logarithm. -/
theorem correspondenceLogPotential_weak_partial (θ : ℂ → ℂ)
    (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, (correspondenceLogPotential z : ℂ)*planarPartial θ z) =
      -(Real.pi/2 : ℂ)*(∫ z : ℂ, cauchyGreenKernel z*θ z) := by
  have hl := correspondenceLogRegularized_integral_tendsto (planarPartial θ)
    (planarPartial_continuous θ hθ) (planarPartial_compact θ hc)
  have hr := (cauchyGreenRegularizedKernel_integral_tendsto θ hθ.continuous hc).const_mul
    (-(Real.pi/2 : ℂ))
  have he : (fun τ : ℝ => ∫ z : ℂ, (correspondenceLogRegularized τ z : ℂ)*planarPartial θ z)
      =ᶠ[𝓝[>] 0] (fun τ : ℝ => -(Real.pi/2 : ℂ)*
        (∫ z : ℂ, cauchyGreenRegularizedKernel τ z*θ z)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hf : ContDiff ℝ 1 (fun z => (correspondenceLogRegularized τ z : ℂ)) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        ((Complex.ofRealCLM.contDiff.comp (correspondenceLogRegularized_contDiff τ hτ)).of_le (by
            simp) : ContDiff ℝ 1 _)
    rw [planarPartial_compact_integrationByParts _ _
      hf hθ hc]
    simp_rw [correspondenceLogRegularized_partial τ hτ, mul_assoc]
    rw [integral_const_mul]
    ring
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

end
end GinibrePoincare
