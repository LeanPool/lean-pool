/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityRealIndicator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealTests
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Ginibre transition analytic local regularity real indicator

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_indicator_real_equation`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]

omit [BorelSpace E] in
theorem ginibreLocalRegularity_indicator_real_equation
    {ι : Type*} [Fintype ι] (v : ι → E) (U : Set E)
    (u h : E → ℝ) (F : ι → E → ℝ)
    (heq : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i))) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*fderiv ℝ θ x (v i)) :
    ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, U.indicator u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i))) =
        (∫ x, U.indicator h x*θ x)-∑ i, ∫ x, U.indicator (F i) x*fderiv ℝ θ x (v i) := by
  classical
  intro θ hθ hc hs
  have hd (x) (hx : x ∉ U) (i) : fderiv ℝ θ x (v i) = 0 := by
    exact congrArg (fun L => L (v i)) (fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun ht => hx (hs ht)))
  have hl (x) (hx : x ∉ U) : (∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact congrArg (fun L => L (v i)) (fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (fun ht => hx (hs ((tsupport_fderiv_apply_subset ℝ (v i)) ht))))
  have hz (x) (hx : x ∉ U) : θ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
  have hi (f q : E → ℝ) (hq : ∀ x, x ∉ U → q x = 0) :
      (∫ x, U.indicator f x*q x) = ∫ x, f x*q x := by
    apply integral_congr_ae
    exact ae_of_all volume fun x => by
      dsimp only
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, hq x hx, mul_zero]
  rw [hi u _ hl, hi h _ hz]
  simp_rw [hi (F _) _ (fun x hx => hd x hx _)]
  exact heq θ hθ hc hs

end
end GinibrePoincare
