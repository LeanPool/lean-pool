/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoPartitionRemainder.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoTaylor
public import Mathlib.Topology.MetricSpace.Sequences

/-! # Taylor expansion along finite partitions

The exact chain identity telescopes the increment expansions into gradient,
quadratic Hessian and remainder sums. It is algebraic: the remainder is
defined by the expansion itself, so this identity needs no smoothness.

For convergence of remainder sums, C² regularity and compact convex
localization give a uniform bound of the form `ε / (C + 1) * ‖increment‖²`.
A vanishing increment mesh eventually makes every increment small enough;
summing and using the quadratic-sum bound `C` yields a total error below
`ε`. Stochastic applications establish their mesh and quadratic-sum controls
in separate modules. -/

@[expose] public section

open Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact discrete Taylor chain identity along an actual finite path. -/
theorem itoTaylor_partition_identity (f : E → ℝ) (z : ℕ → E) (N : ℕ) :
    f (z N) - f (z 0) =
      (∑ i ∈ Finset.range N, fderiv ℝ f (z i) (z (i+1)-z i)) +
      (1/2 : ℝ) * (∑ i ∈ Finset.range N,
        itoDirectionalHessian f (z i) (z (i+1)-z i)) +
      (∑ i ∈ Finset.range N, itoTaylorRemainder f (z i) (z (i+1)-z i)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    unfold itoTaylorRemainder
    simp only [add_sub_cancel]
    unfold itoTaylorRemainder at ih
    simp only [add_sub_cancel] at ih
    rw [← sub_eq_zero] at ih ⊢
    linear_combination ih

/-- The sum of genuine C² Taylor remainders vanishes when the increment mesh
vanishes and the actual quadratic increment sums stay bounded. -/
theorem itoTaylorRemainder_partition_tendsto (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (s : ℕ → Finset ℕ) (x y : ℕ → ℕ → E)
    (hx : ∀ k, ∀ i ∈ s k, x k i ∈ K) (hy : ∀ k, ∀ i ∈ s k, y k i ∈ K)
    (mesh : ℕ → ℝ) (hm : Tendsto mesh atTop (𝓝 0))
    (hi : ∀ k, ∀ i ∈ s k, ‖y k i - x k i‖ ≤ mesh k)
    (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ k, ∑ i ∈ s k, ‖y k i - x k i‖ ^ 2 ≤ C) :
    Tendsto (fun k => ∑ i ∈ s k, itoTaylorRemainder f (x k i) (y k i - x k i))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / (C+1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hd⟩ := itoTaylorRemainder_uniform_compact f hf K hK hconv
    (ε / (C+1)) he
  filter_upwards [hm.eventually (gt_mem_nhds hδ)] with k hk
  rw [dist_zero_right]
  calc
    ‖∑ i ∈ s k, itoTaylorRemainder f (x k i) (y k i-x k i)‖ ≤
        ∑ i ∈ s k, ‖itoTaylorRemainder f (x k i) (y k i-x k i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s k, (ε / (C+1)) * ‖y k i-x k i‖^2 :=
      Finset.sum_le_sum (fun i his => hd _ (hx k i his) _ (hy k i his)
        ((hi k i his).trans_lt hk))
    _ = (ε / (C+1)) * ∑ i ∈ s k, ‖y k i-x k i‖^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (ε / (C+1)) * C := mul_le_mul_of_nonneg_left (hq k) he.le
    _ < ε := by
      have h := mul_lt_mul_of_pos_left (show C < C+1 by linarith) he
      simpa only [div_mul_cancel₀ _ (show C+1 ≠ 0 by linarith)] using h

end
end GinibrePoincare
