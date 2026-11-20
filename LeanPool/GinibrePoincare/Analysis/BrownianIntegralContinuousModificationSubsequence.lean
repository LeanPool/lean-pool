/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationSubsequence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationLimit
public import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Brownian integral continuous modification subsequence

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `continuousProbabilityCauchy_exists_uniform_limit`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section

/-- Uniform probability Cauchy estimates select an actual deterministic
subsequence with summable excursion probabilities. -/
theorem uniformProbabilityCauchy_exists_subsequence
    {K Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Ω → K → ℝ)
    (h : ∀ ε > 0, Tendsto (fun q : ℕ × ℕ =>
      P {ω | ∃ t, ε < |F q.2 ω t - F q.1 ω t|}) atTop (𝓝 0))
    (d : ℕ → ℝ) (hd : ∀ n, 0 < d n)
    (p : ℕ → ℝ≥0∞) (hp : ∀ n, 0 < p n) (hpsum : (∑' n, p n) ≠ ⊤) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      (∑' n, P {ω | ∃ t, d n < |F (s (n+1)) ω t - F (s n) ω t|}) ≠ ⊤ := by
  have he : ∀ n, ∃ a, ∀ k l : ℕ, a ≤ k → a ≤ l →
      P {ω | ∃ t, d n < |F l ω t - F k ω t|} < p n := by
    intro n
    exact eventually_atTop_prod_self.mp ((h (d n) (hd n)).eventually (eventually_lt_nhds (hp n)))
  choose a ha using he
  let s : ℕ → ℕ := fun n => n + ∑ j ∈ Finset.range (n+1), a j
  have hs : StrictMono s := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [s]
    rw [Finset.sum_range_succ a (n+1)]
    omega
  have hsa : ∀ n, a n ≤ s n := by
    intro n
    have hh := Finset.single_le_sum (f := a) (s := Finset.range (n+1))
      (fun j hj => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    dsimp [s]
    omega
  refine ⟨s, hs,?_⟩
  apply ne_top_of_le_ne_top hpsum
  apply tsum_le_tsum
  intro n
  exact (ha n (s n) (s (n+1)) (hsa n) ((hsa n).trans (hs.monotone (Nat.le_succ n)))).le

/-- A uniformly probability-Cauchy family of continuous paths admits an actual
almost surely uniformly convergent deterministic subsequence. -/
theorem continuousProbabilityCauchy_exists_uniform_limit
    {K Ω : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → C(K, ℝ))
    (h : ∀ ε > 0, Tendsto (fun q : ℕ × ℕ =>
      P {ω | ∃ t, ε < |F q.2 ω t - F q.1 ω t|}) atTop (𝓝 0))
    (d : ℕ → ℝ) (hd0 : ∀ n, 0 < d n) (hd : Summable d)
    (p : ℕ → ℝ≥0∞) (hp : ∀ n, 0 < p n) (hpsum : (∑' n, p n) ≠ ⊤) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ᵐ ω ∂P, TendstoUniformly (fun n t => F (s n) ω t)
        (continuousMartingalePathLimit (fun n => F (s n)) ω) atTop := by
  obtain ⟨s, hs, he⟩ := uniformProbabilityCauchy_exists_subsequence P
    (fun n ω t => F n ω t) h d hd0 p hp hpsum
  exact ⟨s, hs, continuousMartingalePathLimit_uniform_ae P (fun n => F (s n))
    d (fun n => (hd0 n).le) hd he⟩

end
end GinibrePoincare
