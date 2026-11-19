/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianLawLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianFiniteLaw
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Brownian integral Gaussian law limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUnitField_integral_limit_gaussian`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- An actual probability limit of variables with the same actual law keeps
that law, by genuine weak convergence and uniqueness. -/
theorem actualConstantLaw_of_tendstoInMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → E) (hS : ∀ n, HasLaw (S n) μ P) (L : Ω → E)
    (hL : TendstoInMeasure P S atTop L) : HasLaw L μ P := by
  have hd := hL.tendstoInDistribution (fun n => (hS n).aemeasurable)
  have hid : HasLaw (id : E → E) μ μ := ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hdid : TendstoInDistribution S atTop (id : E → E) (fun _ => P) μ :=
    tendstoInDistribution_of_identDistrib 0
    (fun n => (hS 0).identDistrib (hS n)) ((hS 0).identDistrib hid)
  have he := tendstoInDistribution_unique S hd hdid
  rw [Measure.map_id] at he
  exact ⟨hd.aemeasurable_limit, he⟩

/-- Gaussian endpoint law of a genuine probability limit of the actual
coordinate sums driven by an adapted unit field. -/
theorem brownianUnitField_integral_limit_gaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ s, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB s) _ (u s))
    (hunit : ∀ s ω, ‖u s ω‖ = 1) (i : ι) (T : ℝ≥0) (L : Ω → ℝ)
    (hL : TendstoInMeasure P (fun n ω =>
      ∑ j, brownianUniformLeftSum (B j) (fun s ω => u s ω j) T (n + 1) ω) atTop L) :
    HasLaw L (gaussianReal 0 T) P := by
  classical
  exact actualConstantLaw_of_tendstoInMeasure P (gaussianReal 0 T) _
    (fun n => brownianUnitField_uniform_sum_gaussian B P hB hind u hu hunit i T (n+1) (Nat.succ_pos
        n)) L hL

end
end GinibrePoincare
