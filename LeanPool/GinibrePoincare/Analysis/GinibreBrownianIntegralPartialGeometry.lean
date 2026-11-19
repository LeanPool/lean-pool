/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPartialGeometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralFrozenMartingale

/-! Exact stopped-grid identities for the actual continuous predictable sums. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem brownian_clipped_increment {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (a b t : ℝ≥0) (hab : a ≤ b) (ω : Ω) :
    B (min t b) ω-B (min t a) ω = B (a+(min t b-a)) ω-B a ω := by
  by_cases hta : t ≤ a
  · have hmin : min t b ≤ a := (min_le_left _ _).trans hta
    simp only [min_eq_left (hta.trans hab), min_eq_left hta, tsub_eq_zero_of_le hta, add_zero,
        sub_self]
  · have hat : a ≤ t := le_of_not_ge hta
    rw [min_eq_right hat, add_tsub_cancel_of_le (le_min hat hab)]

theorem brownianFrozenStep_eq_clipped_increment {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : Ω → ℝ) (a b t : ℝ≥0) (hab : a ≤ b) (ω : Ω) :
    brownianFrozenStep B F a b t ω = F ω*(B (min t b) ω-B (min t a) ω) := by
  by_cases hta : t ≤ a
  · simp only [brownianFrozenStep, 
      min_eq_left (hta.trans hab), min_eq_left hta, max_eq_left hta, sub_self, mul_zero]
  · have hat : a ≤ t := le_of_not_ge hta
    simp only [brownianFrozenStep, max_eq_right (le_min hat hab), min_eq_right hat]

theorem brownianUniformPartialSum_eq_stopped_leftsum {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    brownianUniformPartialSum B F T N t ω =
      brownianUniformLeftSum (fun s ω => B (min t s) ω) F T N ω := by
  unfold brownianUniformPartialSum brownianUniformLeftSum
  apply Finset.sum_congr rfl
  intro i hi
  exact brownianFrozenStep_eq_clipped_increment B (F (itoUniformNNTime T N i)) _ _ t
    (itoUniformNNTime_mono T N (Nat.le_succ i)) ω

theorem brownianUniformPartialSum_terminal {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (ω : Ω) :
    brownianUniformPartialSum B F T N T ω = brownianUniformLeftSum B F T N ω := by
  unfold brownianUniformPartialSum brownianUniformLeftSum
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  have hN : 0 < N := (Nat.zero_le i).trans_lt hiN
  have he := itoUniformNNTime_le_end T N (i+1) hN (Nat.succ_le_of_lt hiN)
  simp only [brownianFrozenStep, min_eq_right he,
    max_eq_right (itoUniformNNTime_mono T N (Nat.le_succ i))]

theorem brownianUniformPartialSum_zero {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (ω : Ω) :
    brownianUniformPartialSum B F T N 0 ω = 0 := by
  simp [brownianUniformPartialSum, brownianFrozenStep]

theorem brownianUniformPartialSum_continuous {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (ω : Ω)
    (hB : Continuous (fun t => B t ω)) :
    Continuous (fun t => brownianUniformPartialSum B F T N t ω) := by
  exact continuous_finsetSum _ (fun i hi => brownianFrozenStep_continuous B _ _ _ ω hB)

theorem brownianUniformPartialSum_time_cap {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    brownianUniformPartialSum B F T N (min t T) ω = brownianUniformPartialSum B F T N t ω := by
  unfold brownianUniformPartialSum
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  have hN : 0 < N := (Nat.zero_le i).trans_lt hiN
  have he := itoUniformNNTime_le_end T N (i+1) hN (Nat.succ_le_of_lt hiN)
  simp only [brownianFrozenStep, min_assoc, min_eq_right he]

end
end GinibrePoincare
