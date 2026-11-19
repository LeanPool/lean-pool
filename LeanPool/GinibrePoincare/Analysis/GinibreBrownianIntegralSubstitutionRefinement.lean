/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralSubstitutionRefinement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoWeightedRefinement
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionFinite
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianGridIntegrability

/-!
# Ginibre Brownian integral substitution refinement

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianSubstitutionCoarseApproximation_refinement`,
`actualMeanSquareLimit_weighted_grid_increments`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem actualMeanSquareZero_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E F : ℕ → Ω → ℝ)
    (hE : ∀ n, MemLp (E n) 2 P) (hF : ∀ n, MemLp (F n) 2 P)
    (he : Tendsto (fun n => ∫ ω, (E n ω) ^ 2 ∂P) atTop (𝓝 0))
    (hf : Tendsto (fun n => ∫ ω, (F n ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (E n ω-F n ω)^2 ∂P) atTop (𝓝 0) := by
  have h := actualMeanSquareZero_finset_sum P (Finset.univ : Finset (Fin 2))
    (fun i n ω => if i=0 then E n ω else -F n ω)
    (fun i n => by
      by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false]
      · exact hE n
      · exact (hF n).neg)
    (fun i => by by_cases hi : i=0
                 · simpa only [hi, ite_true] using he
                 · simpa only [hi, ite_false, neg_sq] using hf)
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using h

/-- The sum over coordinates `i` of the frozen-step uniform partial sums
`brownianUniformPartialSum (B i) (u i) T K r`, evaluated at time `r`. -/
def brownianAggregatePartialSum {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ι → ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (K : ℕ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, brownianUniformPartialSum (B i) (u i) T K r ω

/-- The coarse left-point sum `∑ k < N, A (t k) * (S (t (k + 1)) - S (t k))` along the uniform
`N`-step grid `t`, where `S = brownianAggregatePartialSum B u T (N * M)` is the fine sum. -/
def brownianSubstitutionCoarseApproximation {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ι → ℝ≥0 → Ω → ℝ)
    (A : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N M : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, A (itoUniformNNTime T N k) ω*
    (brownianAggregatePartialSum B u T (N*M) (itoUniformNNTime T N (k+1)) ω-
      brownianAggregatePartialSum B u T (N*M) (itoUniformNNTime T N k) ω)

theorem brownianSubstitutionCoarseApproximation_refinement {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ι → ℝ≥0 → Ω → ℝ)
    (A : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N M : ℕ) (hM : 0 < M) (ω : Ω) :
    brownianSubstitutionCoarseApproximation B u A T N M ω =
    ∑ i, ∑ k ∈ Finset.range (N*M), A (itoUniformNNTime T N (k/M)) ω*
      (u i (itoUniformNNTime T (N*M) k) ω*
        (B i (itoUniformNNTime T (N*M) (k+1)) ω-B i (itoUniformNNTime T (N*M) k) ω)) := by
  classical
  unfold brownianSubstitutionCoarseApproximation brownianAggregatePartialSum
  simp_rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact brownianUniformPartialSum_weighted_coarse_refinement (B i) (u i) A T N M hM ω

/-- Finite actual path increments preserve mean-square convergence under
bounded random left weights. The weights need no independence. -/
theorem actualMeanSquareLimit_weighted_grid_increments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → ℝ≥0 → Ω → ℝ) (β A : ℝ≥0 → Ω → ℝ)
    (g : ℕ → ℝ≥0) (N : ℕ)
    (hS : ∀ k : Fin (N+1), ∀ m, MemLp (S m (g k)) 2 P)
    (hβ : ∀ k : Fin (N+1), MemLp (β (g k)) 2 P)
    (hA : ∀ k : Fin N, AEStronglyMeasurable (A (g k)) P)
    (C : ℝ) (hC : 0≤C) (hb : ∀ k : Fin N, ∀ ω, ‖A (g k) ω‖≤C)
    (hlim : ∀ k : Fin (N+1), Tendsto (fun m => ∫ ω,
      (S m (g k) ω-β (g k) ω)^2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω,
      ((∑ k ∈ Finset.range N, A (g k) ω*(S m (g (k+1)) ω-S m (g k) ω))-
        (∑ k ∈ Finset.range N, A (g k) ω*(β (g (k+1)) ω-β (g k) ω)))^2 ∂P)
      atTop (𝓝 0) := by
  have hi (k : Fin N) : Tendsto (fun m => ∫ ω,
      ((S m (g (k.val+1)) ω-S m (g k) ω)-
        (β (g (k.val+1)) ω-β (g k) ω))^2 ∂P) atTop (𝓝 0) := by
    have hh := actualMeanSquareZero_sub P
      (fun m ω => S m (g (k.val+1)) ω-β (g (k.val+1)) ω)
      (fun m ω => S m (g k) ω-β (g k) ω)
      (fun m => (hS k.succ m).sub (hβ k.succ))
      (fun m => (hS k.castSucc m).sub (hβ k.castSucc)) (hlim k.succ) (hlim k.castSucc)
    convert hh using 1
    funext m
    congr 1
    funext ω
    ring
  have hh := actualMeanSquareLimit_finite_bounded_weights P (Finset.univ : Finset (Fin N))
    (fun k m ω => S m (g (k.val+1)) ω-S m (g k) ω)
    (fun k ω => β (g (k.val+1)) ω-β (g k) ω) (fun k => A (g k))
    (fun k m => (hS k.succ m).sub (hS k.castSucc m))
    (fun k => (hβ k.succ).sub (hβ k.castSucc)) hA C hC hb hi
  simpa only [← Fin.sum_univ_eq_sum_range] using hh

end
end GinibrePoincare
