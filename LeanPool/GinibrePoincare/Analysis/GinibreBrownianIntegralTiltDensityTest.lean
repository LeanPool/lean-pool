/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltDensityTest.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltTestLimit

/-!
# Ginibre Brownian integral tilt density test

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualVaryingDensity_continuous_test_tendsto`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section

/-- Genuine L¹ changes of density and actual probability convergence of states
 preserve every bounded continuous weighted expectation. -/
theorem actualVaryingDensity_continuous_test_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω)
    (D : ℕ → Ω → ℝ) (d : Ω → ℝ) (hDi : ∀ n, Integrable (D n) P) (hdi : Integrable d P)
    (hL : Tendsto (fun n => eLpNorm (D n - d) 1 P) atTop (𝓝 0))
    (X : ℕ → Ω → E) (x : Ω → E) (hX : ∀ n, AEMeasurable (X n) P)
    (hx : AEMeasurable x P) (hl : TendstoInMeasure P X atTop x) (b : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, D n ω*b (X n ω) ∂P) atTop (𝓝 (∫ ω, d ω*b (x ω) ∂P)) := by
  have hbm (n : ℕ) : AEStronglyMeasurable (fun ω => b (X n ω)) P :=
    (b.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ ω ∂P, ‖b (X n ω)‖≤‖b‖ := Eventually.of_forall fun ω => b.norm_coe_le_norm _
  have hfixed := actualDensity_continuous_test_tendsto P d hdi X x hX hx hl b
  have herr := actualDensity_bounded_test_error_tendsto P D d hDi hdi hL
    (fun n ω => b (X n ω)) ‖b‖ (norm_nonneg _) (fun n ω => b.norm_coe_le_norm _)
  have he (n : ℕ) : (∫ ω, (D n ω-d ω)*b (X n ω) ∂P)+(∫ ω, d ω*b (X n ω) ∂P) =
      ∫ ω, D n ω*b (X n ω) ∂P := by
    change (∫ ω, (D n-d) ω*b (X n ω) ∂P)+(∫ ω, d ω*b (X n ω) ∂P)=_
    rw [← integral_add (((hDi n).sub hdi).mul_bdd (hbm n) (hb n))
      (hdi.mul_bdd (hbm n) (hb n))]
    congr 1
    funext ω
    simp only [Pi.sub_apply]
    ring
  simpa only [he, zero_add] using herr.add hfixed

end
end GinibrePoincare
