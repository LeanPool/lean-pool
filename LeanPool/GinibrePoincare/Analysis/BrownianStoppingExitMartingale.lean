/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitMartingale.lean.
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

public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Honest bounded optional sampling for countable-range continuous-time stops. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem martingale_integral_stoppedValue_of_countable_range
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hc : (Set.range τ).Countable) :
    ∫ ω, stoppedValue M τ ω ∂μ = ∫ ω, M 0 ω ∂μ := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hτT hc
  rw [integral_congr_ae he, integral_condExp (hτ.measurableSpace_le_of_le hτT)]
  have h0 := hM.condExp_ae_eq (show (0 : ℝ≥0) ≤ T from bot_le)
  exact (integral_condExp (ℱ.le 0)).symm.trans (integral_congr_ae h0)

theorem martingale_integrable_stoppedValue_of_countable_range
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hc : (Set.range τ).Countable) :
    Integrable (stoppedValue M τ) μ := by
  exact (integrable_condExp : Integrable (μ[M T | hτ.measurableSpace]) μ).congr
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hτT hc).symm

end
end GinibrePoincare
