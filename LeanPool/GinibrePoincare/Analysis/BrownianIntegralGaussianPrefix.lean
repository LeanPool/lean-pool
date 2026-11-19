/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianPrefix.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianGrid

/-!
# Brownian integral Gaussian prefix

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUnitGridPrefix_gaussian`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The sum of the first `n` unit-field innovations `brownianUnitGridInnovation B u τ k` along
the time grid `τ`. -/
def brownianUnitGridPrefix {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ℕ → Ω → EuclideanSpace ℝ ι)
    (τ : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, brownianUnitGridInnovation B u τ k ω

theorem brownianUnitGridPrefix_measurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (u : ℕ → Ω → EuclideanSpace ℝ ι) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hu : ∀ k, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (u k)) (n : ℕ) :
    @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ n)) _
      (brownianUnitGridPrefix B u τ n) := by
  have hm : ∀ k ∈ Finset.range n, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P hB (τ n)) _
      (brownianUnitGridInnovation B u τ k) := by
    intro k hk
    exact (brownianUnitGridInnovation_measurable_at_end B P hB u τ hτ hu k).mono
      ((ginibreBrownianAugmentedFiltration B P hB).mono
        (hτ (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))) le_rfl
  let : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB (τ n)
  exact Finset.measurable_sum (Finset.range n) hm

/-- Actual sums of chronological adaptive unit-vector innovations have the
original Gaussian law, with variance equal to the sum of actual interval lengths. -/
theorem brownianUnitGridPrefix_gaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℕ → Ω → EuclideanSpace ℝ ι) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hu : ∀ k, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (u k))
    (hunit : ∀ k ω, ‖u k ω‖ = 1) (i : ι) (n : ℕ) :
    HasLaw (brownianUnitGridPrefix B u τ n)
      (gaussianReal 0 (∑ k ∈ Finset.range n, (τ (k+1)-τ k))) P := by
  classical
  induction n with
  | zero =>
      have hz : brownianUnitGridPrefix B u τ 0 = (fun _ => 0) := by
        funext ω
        simp [brownianUnitGridPrefix]
      rw [hz]
      refine ⟨measurable_const.aemeasurable,?_⟩
      simp [Measure.map_const, gaussianReal_zero_var]
  | succ n hn =>
      obtain ⟨hl, hi⟩ := brownianUnitGridInnovation_gaussian_independent B P hB hind
        u τ hu hunit n (brownianUnitGridPrefix B u τ n)
        (brownianUnitGridPrefix_measurable B P hB u τ hτ hu n) i
      have hh := IndepFun.hasLaw_add hn hl hi
      have heq : brownianUnitGridPrefix B u τ (n+1) =
          brownianUnitGridPrefix B u τ n+brownianUnitGridInnovation B u τ n := by
        funext ω
        simp [brownianUnitGridPrefix, Finset.sum_range_succ, Pi.add_apply]
      rw [heq, Finset.sum_range_succ]
      simpa only [gaussianReal_conv_gaussianReal, zero_add] using hh

end
end GinibrePoincare
