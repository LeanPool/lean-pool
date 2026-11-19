/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroDriverRecovery.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiRecovery
public import Mathlib.Probability.Independence.Basic

/-! Whole-process independence transfers from the center path to its recovered
punctured Lamperti driver. The hypotheses are actual increment identities. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterPuncturedDriver_eq_recovery
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) (α : ℝ)
    (S : Ω → ℝ≥0 → ℂ) (β : ℝ≥0 → Ω → ℝ)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (h0 : ∀ᵐ ω ∂P, β 0 ω = 0)
    (hi : ∀ᵐ ω ∂P, ∀ k t, ginibreCenterPositiveStart k ≤ t →
      ginibreCenterPositiveStartLamperti n α k (S ω) t =
        β t ω - β (ginibreCenterPositiveStart k) ω) :
    (fun ω t => β t ω) =ᵐ[P] (fun ω => ginibreCenterPuncturedLampertiRecovery n α (S ω)) := by
  filter_upwards [hc, h0, hi] with ω hc h0 hi
  exact (ginibreCenterPuncturedLampertiRecovery_eq n α (S ω) _ hc h0 hi).symm

theorem ginibreCenterPuncturedDriver_independent
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (n : ℕ) (α : ℝ) (S : Ω → ℝ≥0 → ℂ)
    (β : ℝ≥0 → Ω → ℝ) (R : Ω → E)
    (hind : IndepFun S R P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (h0 : ∀ᵐ ω ∂P, β 0 ω = 0)
    (hi : ∀ᵐ ω ∂P, ∀ k t, ginibreCenterPositiveStart k ≤ t →
      ginibreCenterPositiveStartLamperti n α k (S ω) t =
        β t ω - β (ginibreCenterPositiveStart k) ω) :
    IndepFun (fun ω t => β t ω) R P := by
  exact (hind.comp (ginibreCenterPuncturedLampertiRecovery_measurable n α)
    measurable_id).congr
      (ginibreCenterPuncturedDriver_eq_recovery P n α S β hc h0 hi).symm
      Filter.EventuallyEq.rfl

end
end GinibrePoincare
