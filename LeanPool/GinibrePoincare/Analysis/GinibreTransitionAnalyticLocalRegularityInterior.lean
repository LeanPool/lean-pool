/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityInterior.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityLocalizedData

/-!
# Ginibre transition analytic local regularity interior

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_cutoff_weak_derivative_interior`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual localized L² derivative represents the original unknown on every
compact test lying in the region where the cutoff equals one. -/
theorem ginibreLocalRegularity_cutoff_weak_derivative_interior
    (u η : E → ℂ) (g : Lp ℂ 2 (volume : Measure E)) (v : E)
    (hg : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*(η x*u x)))
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hone : ∀ x ∈ tsupport θ, η x = 1) :
    (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*u x) := by
  rw [hg θ hθ hc]
  congr 1
  apply integral_congr_ae
  exact ae_of_all volume fun x => by
    dsimp only
    by_cases hx : x ∈ tsupport θ
    · rw [hone x hx, one_mul]
    · have hzero : fderiv ℝ θ x v = 0 := by
        have he : θ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
        have hd := he.fderiv_eq (𝕜 := ℝ)
        simpa using congrArg (fun L => L v) hd
      simp [hzero]

end
end GinibrePoincare
