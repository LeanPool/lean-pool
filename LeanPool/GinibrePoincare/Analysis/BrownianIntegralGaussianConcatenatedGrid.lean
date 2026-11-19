/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianConcatenatedGrid.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianGridComparison
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianShifted

/-!
# Brownian integral Gaussian concatenated grid

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoConcatenatedGrid_zero`, `itoConcatenatedGrid_end`, `itoConcatenatedGrid_step`,
`brownianActualLeftGridSum_concatenated`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The concatenation of the uniform `N`-step grid on `[0, s]` with the uniform `N`-step grid on
`[0, t]` shifted by `s`: index `k ≤ N` gives `itoUniformNNTime s N k`, and a larger index gives
`s + itoUniformNNTime t N (k - N)`. -/
def itoConcatenatedGrid (s t : ℝ≥0) (N k : ℕ) : ℝ≥0 :=
  if k ≤ N then itoUniformNNTime s N k else s + itoUniformNNTime t N (k-N)

theorem itoConcatenatedGrid_first (s t : ℝ≥0) (N k : ℕ) (hk : k ≤ N) :
    itoConcatenatedGrid s t N k=itoUniformNNTime s N k := by
  simp [itoConcatenatedGrid, hk]

theorem itoConcatenatedGrid_second (s t : ℝ≥0) (N k : ℕ) (hN : 0 < N) :
    itoConcatenatedGrid s t N (N+k)=s+itoUniformNNTime t N k := by
  by_cases hk : k=0
  · subst k
    simp only [itoConcatenatedGrid, add_zero, le_refl, ite_true, itoUniformNNTime_end s N hN]
    simp [itoUniformNNTime, itoUniformTime]
  · have h : ¬ N+k ≤ N := by omega
    simp [itoConcatenatedGrid, h]

theorem itoConcatenatedGrid_monotone (s t : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    Monotone (itoConcatenatedGrid s t N) := by
  intro k l hkl
  by_cases hk : k ≤ N
  · by_cases hl : l ≤ N
    · simpa only [itoConcatenatedGrid, ite_eq_left hk, ite_eq_left hl] using
        itoUniformNNTime_mono s N hkl
    · rw [itoConcatenatedGrid_first s t N k hk]
      have hs : itoUniformNNTime s N k ≤ s := by
        simpa only [itoUniformNNTime_end s N hN] using itoUniformNNTime_mono s N hk
      exact hs.trans (by simp [itoConcatenatedGrid, hl])
  · have hl : ¬ l ≤ N := by omega
    simp only [itoConcatenatedGrid, ite_eq_right hk, ite_eq_right hl]
    exact add_le_add_right (itoUniformNNTime_mono t N (Nat.sub_le_sub_right hkl N)) s

theorem itoConcatenatedGrid_zero (s t : ℝ≥0) (N : ℕ) :
    itoConcatenatedGrid s t N 0=0 := by
  simp [itoConcatenatedGrid, itoUniformNNTime, itoUniformTime]

theorem itoConcatenatedGrid_end (s t : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    itoConcatenatedGrid s t N (N+N)=s+t := by
  rw [itoConcatenatedGrid_second s t N N hN, itoUniformNNTime_end t N hN]

theorem itoConcatenatedGrid_step (s t : ℝ≥0) (N k : ℕ) (hN : 0 < N) :
    (itoConcatenatedGrid s t N (k+1) : ℝ)-itoConcatenatedGrid s t N k
      ≤ (s+t : ℝ≥0)/N := by
  by_cases hk : k<N
  · rw [itoConcatenatedGrid_first s t N (k+1) (by omega),
      itoConcatenatedGrid_first s t N k hk.le, itoUniformNNTime_increment_coe]
    push_cast
    exact div_le_div_of_nonneg_right (by linarith [s.coe_nonneg, t.coe_nonneg]) (Nat.cast_nonneg N)
  · have he : k=N+(k-N) := by omega
    have he' : k+1=N+(k-N+1) := by omega
    rw [he', itoConcatenatedGrid_second s t N (k-N+1) hN, he,
      itoConcatenatedGrid_second s t N (k-N) hN]
    simp only [Nat.add_sub_cancel_left, NNReal.coe_add]
    have hh := itoUniformNNTime_increment_coe t N (k-N)
    have hl : (t : ℝ)/N ≤ ((s : ℝ)+t)/N :=
      div_le_div_of_nonneg_right (by linarith [s.coe_nonneg, t.coe_nonneg]) (Nat.cast_nonneg N)
    linarith

theorem brownianActualLeftGridSum_concatenated {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (N : ℕ) (hN : 0 < N) (ω : Ω) :
    brownianActualLeftGridSum B F (itoConcatenatedGrid s t N) (N+N) ω =
      brownianUniformLeftSum B F s N ω +
        ∑ k ∈ Finset.range N, F (s+itoUniformNNTime t N k) ω*
          (B (s+itoUniformNNTime t N (k+1)) ω-B (s+itoUniformNNTime t N k) ω) := by
  unfold brownianActualLeftGridSum brownianUniformLeftSum
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [itoConcatenatedGrid_first s t N k hk'.le,
      itoConcatenatedGrid_first s t N (k+1) (by omega)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [itoConcatenatedGrid_second s t N k hN,
      show N+k+1=N+(k+1) by omega, itoConcatenatedGrid_second s t N (k+1) hN]

end
end GinibrePoincare
