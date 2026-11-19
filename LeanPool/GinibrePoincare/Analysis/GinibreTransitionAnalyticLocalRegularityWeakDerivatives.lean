/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityWeakDerivatives.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityBessel

/-! A genuine L² elliptic divergence equation produces actual ordinary L²
weak derivatives against every compact smooth test. -/

@[expose] public section
open TemperedDistribution FourierTransform MeasureTheory
open scoped SchwartzMap LineDeriv Laplacian ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_elliptic_exists_weak_derivatives
    {ι : Type*} [Fintype ι] (u h : Lp ℂ 2 (volume : Measure E))
    (F : ι → Lp ℂ 2 (volume : Measure E)) (v : ι → E)
    (heq : Δ (u : 𝓢'(E, ℂ)) = (h : 𝓢'(E, ℂ)) + ∑ i, ∂_{v i} (F i : 𝓢'(E, ℂ))) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), ∀ i (θ : E → ℂ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g i x) = -(∫ x, fderiv ℝ θ x (v i)*u x) := by
  have hu : MemSobolev 0 2 (u : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hh : MemSobolev 0 2 (h : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨h, rfl⟩
  have hF (i : ι) : MemSobolev 0 2 (F i : 𝓢'(E, ℂ)) := memSobolev_zero_iff.mpr ⟨F i, rfl⟩
  have hr := ginibreLocalRegularity_elliptic_divergence_memSobolev (u : 𝓢'(E, ℂ)) (h : 𝓢'(E, ℂ))
    (fun i => (F i : 𝓢'(E, ℂ))) v hu hh hF heq
  have hder (i : ι) : ∃ gi : Lp ℂ 2 (volume : Measure E),
      ∂_{v i} (u : 𝓢'(E, ℂ)) = (gi : 𝓢'(E, ℂ)) := by
    apply memSobolev_zero_iff.mp
    simpa using hr.lineDerivOp (m := v i)
  choose g hg using hder
  refine ⟨g,?_⟩
  intro i θ hθ hc
  have ht := congrArg (fun f : 𝓢'(E, ℂ) => f (hc.toSchwartzMap hθ)) (hg i)
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    smul_eq_mul, neg_mul, integral_neg] at ht
  exact ht.symm

end
end GinibrePoincare
