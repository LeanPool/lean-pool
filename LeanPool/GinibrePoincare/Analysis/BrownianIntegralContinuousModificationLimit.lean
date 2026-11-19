/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationMaximal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Brownian integral continuous modification limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `continuousMartingalePathLimit_uniform_ae`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section

/-- The actual continuous limit of a uniformly Cauchy path sequence; zero on
paths where convergence fails. Every output is a continuous function. -/
def continuousMartingalePathLimit {K Ω : Type*} [TopologicalSpace K] [CompactSpace K]
    (F : ℕ → Ω → C(K, ℝ)) (ω : Ω) : C(K, ℝ) := by
  classical
  exact if h : CauchySeq (fun n => F n ω) then
    Classical.choose (cauchySeq_tendsto_of_complete h) else 0

/-- Summable actual excursion probabilities imply an actual almost surely
uniformly convergent continuous path sequence, by Borel–Cantelli. -/
theorem continuousMartingalePathLimit_tendsto_ae
    {K Ω : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → C(K, ℝ))
    (d : ℕ → ℝ) (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hp : (∑' n, P {ω | ∃ t, d n < |F (n+1) ω t - F n ω t|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (continuousMartingalePathLimit F ω)) := by
  filter_upwards [ae_eventually_notMem hp] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have hs : CauchySeq (fun n => F n ω) := by
    apply (cauchySeq_shift N).mp
    apply cauchySeq_of_dist_le_of_summable (fun n => d (n+N))
    · intro n
      apply (ContinuousMap.dist_le (hd0 (n+N))).mpr
      intro t
      have hn := hN (n+N) (by omega)
      have hh : |F (n+N+1) ω t - F (n+N) ω t| ≤ d (n+N) := by
        by_contra h
        exact hn ⟨t, lt_of_not_ge h⟩
      simpa [Real.dist_eq, abs_sub_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · exact (summable_nat_add_iff N).mpr hd
  simp only [continuousMartingalePathLimit, dite_eq_left hs]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete hs)

/-- The constructed limit is genuinely uniform on the whole compact time domain. -/
theorem continuousMartingalePathLimit_uniform_ae
    {K Ω : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → C(K, ℝ))
    (d : ℕ → ℝ) (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hp : (∑' n, P {ω | ∃ t, d n < |F (n+1) ω t - F n ω t|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, TendstoUniformly (fun n t => F n ω t)
      (continuousMartingalePathLimit F ω) atTop := by
  filter_upwards [continuousMartingalePathLimit_tendsto_ae P F d hd0 hd hp] with ω hω
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp hω

end
end GinibrePoincare
