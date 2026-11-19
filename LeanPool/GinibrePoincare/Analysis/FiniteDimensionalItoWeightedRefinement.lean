/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoWeightedRefinement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPartialGeometry

/-!
# Finite dimensional Ito weighted refinement

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUniformPartialSum_weighted_coarse_refinement`.
-/

@[expose] public section

open scoped NNReal BigOperators
namespace GinibrePoincare
noncomputable section

theorem brownianUniformPartialSum_grid_endpoint {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (N l : ℕ) (hl : l ≤ N) (ω : Ω) :
    brownianUniformPartialSum B F T N (itoUniformNNTime T N l) ω =
      ∑ k ∈ Finset.range l, F (itoUniformNNTime T N k) ω*
        (B (itoUniformNNTime T N (k+1)) ω-B (itoUniformNNTime T N k) ω) := by
  unfold brownianUniformPartialSum
  rw [show N=l+(N-l) by omega, Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range l,
      brownianFrozenStep B (F (itoUniformNNTime T (l+(N-l)) k))
        (itoUniformNNTime T (l+(N-l)) k) (itoUniformNNTime T (l+(N-l)) (k+1))
        (itoUniformNNTime T (l+(N-l)) l) ω) =
      ∑ k ∈ Finset.range l, F (itoUniformNNTime T N k) ω*
        (B (itoUniformNNTime T N (k+1)) ω-B (itoUniformNNTime T N k) ω) := by
    rw [Nat.add_sub_of_le hl]
    apply Finset.sum_congr rfl
    intro k hk
    have hkl : k+1 ≤ l := by have := Finset.mem_range.mp hk; omega
    simp only [brownianFrozenStep,
      min_eq_right (itoUniformNNTime_mono T N hkl),
      max_eq_right (itoUniformNNTime_mono T N (Nat.le_succ k))]
  rw [hfirst]
  have hzero : (∑ k ∈ Finset.range (N-l),
      brownianFrozenStep B (F (itoUniformNNTime T (l+(N-l)) (l+k)))
        (itoUniformNNTime T (l+(N-l)) (l+k))
        (itoUniformNNTime T (l+(N-l)) (l+k+1))
        (itoUniformNNTime T (l+(N-l)) l) ω)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkle : l ≤ l+k := Nat.le_add_right _ _
    have hnxt : l ≤ l+k+1 := by omega
    simp only [brownianFrozenStep,
      min_eq_left (itoUniformNNTime_mono T _ hnxt),
      max_eq_left (itoUniformNNTime_mono T _ hkle), sub_self, mul_zero]
  rw [hzero, add_zero, Nat.add_sub_of_le hl]

theorem brownianUniformPartialSum_grid_increment {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (N k : ℕ) (hk : k < N) (ω : Ω) :
    brownianUniformPartialSum B F T N (itoUniformNNTime T N (k+1)) ω-
      brownianUniformPartialSum B F T N (itoUniformNNTime T N k) ω =
    F (itoUniformNNTime T N k) ω*
      (B (itoUniformNNTime T N (k+1)) ω-B (itoUniformNNTime T N k) ω) := by
  rw [brownianUniformPartialSum_grid_endpoint B F T N (k+1) (by omega) ω,
    brownianUniformPartialSum_grid_endpoint B F T N k hk.le ω, Finset.sum_range_succ]
  ring

theorem brownianUniformPartialSum_weighted_coarse_refinement {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F A : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (N M : ℕ) (hM : 0 < M) (ω : Ω) :
    (∑ k ∈ Finset.range N, A (itoUniformNNTime T N k) ω*
      (brownianUniformPartialSum B F T (N*M) (itoUniformNNTime T N (k+1)) ω-
        brownianUniformPartialSum B F T (N*M) (itoUniformNNTime T N k) ω)) =
    ∑ k ∈ Finset.range (N*M), A (itoUniformNNTime T N (k/M)) ω*
      (F (itoUniformNNTime T (N*M) k) ω*
        (B (itoUniformNNTime T (N*M) (k+1)) ω-B (itoUniformNNTime T (N*M) k) ω)) := by
  rw [itoUniformNNWeightedSum_refinement (fun r => A r ω)
    (fun r => brownianUniformPartialSum B F T (N*M) r ω) T N M hM]
  apply Finset.sum_congr rfl
  intro k hk
  rw [brownianUniformPartialSum_grid_increment B F T (N*M) k (Finset.mem_range.mp hk) ω]

end
end GinibrePoincare
