/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityWeakUniqueness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityDensityQuotient
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Ginibre transition analytic local regularity weak uniqueness

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_local_weak_derivative_unique`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]

theorem ginibreLocalRegularity_local_weak_derivative_unique
    (U : Set E) (hU : IsOpen U) (u g h : E → ℝ) (v : E)
    (hg : MemLp g 2 (volume : Measure E)) (hh : MemLp h 2 volume)
    (hgw : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*u x))
    (hhw : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, θ x*h x) = -(∫ x, fderiv ℝ θ x v*u x)) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ U → g x = h x := by
  have hl := (hg.sub hh).locallyIntegrable (by norm_num) |>.locallyIntegrableOn U
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hl (fun θ hθ hc hs => by
    have hgi := hg.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hθ.continuous hc
    have hhi := hh.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hθ.continuous hc
    have hge : Integrable (fun x => θ x*g x) volume := by
      apply hgi.congr
      exact ae_of_all volume fun x => by dsimp only; simp only [smul_eq_mul]; exact mul_comm _ _
    have hhe : Integrable (fun x => θ x*h x) volume := by
      apply hhi.congr
      exact ae_of_all volume fun x => by dsimp only; simp only [smul_eq_mul]; exact mul_comm _ _
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub hge hhe, hgw θ hθ hc hs, hhw θ hθ hc hs, sub_self])
  filter_upwards [hz] with x hx
  intro hu
  exact sub_eq_zero.mp (hx hu)

end
end GinibrePoincare
