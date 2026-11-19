/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityCompactData.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityTemperedEquation

/-! Actual compact L² data satisfying the elliptic compact-test equation have
actual L² weak derivatives. No distribution equation, derivative or Sobolev
regularity is assumed: they are all derived from that compact-test equation. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_compact_elliptic_exists_weak_derivatives
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (u h : E → ℂ) (F : ι → E → ℂ)
    (hu : HasCompactSupport u) (hh : HasCompactSupport h) (hF : ∀ i, HasCompactSupport (F i))
    (hui : MemLp u 2 (volume : Measure E)) (hhi : MemLp h 2 (volume : Measure E))
    (hFi : ∀ i, MemLp (F i) 2 (volume : Measure E))
    (heq : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (b i)) x (b i))) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*fderiv ℝ θ x (b i)) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), ∀ i (θ : E → ℂ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g i x) = -(∫ x, fderiv ℝ θ x (b i)*u x) := by
  have he := ginibreLocalRegularity_compact_tests_tempered_equation b u h F hu hh hF hui hhi hFi heq
  obtain ⟨g, hg⟩ := ginibreLocalRegularity_elliptic_exists_weak_derivatives
    (hui.toLp u) (hhi.toLp h) (fun i => (hFi i).toLp (F i)) (fun i => b i) he
  refine ⟨g,?_⟩
  intro i θ hθ hc
  have hh := hg i θ hθ hc
  have hi : (∫ x, fderiv ℝ θ x (b i)*(hui.toLp u) x) =
      ∫ x, fderiv ℝ θ x (b i)*u x := by
    apply integral_congr_ae
    filter_upwards [hui.coeFn_toLp] with x hx
    simp only [hx]
  rwa [hi] at hh

end
end GinibrePoincare
