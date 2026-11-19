/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralFrozenMartingale.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralFrozenConditional
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralL2Limit

/-! Actual frozen steps, and their uniform finite sums, are continuous martingales. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem brownianFrozenStep_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : Ω → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB a) _ F)
    (hFi : MemLp F 2 P) :
    Martingale (brownianFrozenStep (B j) F a b) (ginibreBrownianAugmentedFiltration B P hB) P := by
  have := Fintype.ofFinite ι
  refine ⟨brownianFrozenStep_stronglyAdapted B P hB j F a b hF, ?_⟩
  intro s t hst
  have hs := brownianFrozenStep_conditional_terminal B P hB hind j F a b s hab hF hFi
  have ht := brownianFrozenStep_conditional_terminal B P hB hind j F a b t hab hF hFi
  have htw := condExp_condExp_of_le ((ginibreBrownianAugmentedFiltration B P hB).mono hst)
    ((ginibreBrownianAugmentedFiltration B P hB).le t)
    (f := fun ω => F ω*(B j b ω-B j a ω)) (μ := P)
  exact (condExp_congr_ae ht.symm).trans (htw.trans hs)

/-- The left-point stochastic sum of `F` against `B` over the uniform partition of `[0, T]` into
`N` steps, with every elementary step stopped at time `t`. -/
def brownianUniformPartialSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, brownianFrozenStep B (F (itoUniformNNTime T N i))
    (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1)) t ω

theorem brownianUniformPartialSum_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N : ℕ) :
    Martingale (brownianUniformPartialSum (B j) F T N) (ginibreBrownianAugmentedFiltration B P hB) P
        := by
  have := Fintype.ofFinite ι
  have hm (i : ℕ) := brownianFrozenStep_martingale B P hB hind j (F (itoUniformNNTime T N i))
    (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1))
    (itoUniformNNTime_mono T N (Nat.le_succ i)) (hF _) (hFi _)
  have hsum : Martingale (∑ i ∈ Finset.range N, brownianFrozenStep (B j) (F (itoUniformNNTime T N
      i))
      (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1))) (ginibreBrownianAugmentedFiltration B P
          hB) P := by
    have hall (S : Finset ℕ) : Martingale (∑ i ∈ S, brownianFrozenStep (B j) (F (itoUniformNNTime T
        N i))
        (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1))) (ginibreBrownianAugmentedFiltration B
            P hB) P := by
      induction S using Finset.induction_on with
      | empty => simpa using martingale_zero ℝ (ginibreBrownianAugmentedFiltration B P hB) P
      | @insert i S hi ih =>
        rw [Finset.sum_insert hi]
        exact (hm i).add ih
    exact hall (Finset.range N)
  have he : brownianUniformPartialSum (B j) F T N =
      ∑ i ∈ Finset.range N, brownianFrozenStep (B j) (F (itoUniformNNTime T N i))
        (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1)) := by
    funext t ω
    simp only [brownianUniformPartialSum, Finset.sum_apply]
  rw [he]
  exact hsum

end
end GinibrePoincare
