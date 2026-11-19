/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPuncturedPartialBound.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedContinuous

/-! Initial-cutoff error control for actual partial Brownian sums, obtained
from their genuine martingale terminal contraction. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianUniformPartialSum_initial_cutoff_error_bound {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hb : ∀ t ω, ‖F t ω‖ ≤ C)
    (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) (N : ℕ) (hN : 0 < N) :
    (∫ ω, (brownianUniformPartialSum (B j) F T N t ω-
      brownianUniformPartialSum (B j) (brownianInitialTimeCutoff F ε) T N t ω)^2 ∂P) ≤
      C^2*(2*ε+(T : ℝ)/(N : ℝ)) := by
  have := Fintype.ofFinite ι
  let ℱ := ginibreBrownianAugmentedFiltration B P hB
  let A := brownianInitialTimeCutoff F ε
  have ha := brownianInitialTimeCutoff_adapted F ε ℱ hF
  have hFi (r : ℝ≥0) : MemLp (F r) 2 P := MemLp.of_bound
    ((hF r).mono (ℱ.le r) le_rfl).aestronglyMeasurable C (ae_of_all P (hb r))
  have hAi (r : ℝ≥0) : MemLp (A r) 2 P := MemLp.of_bound
    ((ha r).mono (ℱ.le r) le_rfl).aestronglyMeasurable C
    (ae_of_all P fun ω => brownianInitialTimeCutoff_bound F ε C hb r ω)
  have hM := brownianUniformPartialSum_martingale B P hB hind j F hF hFi T N
  have hA := brownianUniformPartialSum_martingale B P hB hind j A ha hAi T N
  have hh := realMartingale_difference_secondMoment_le_terminal P ℱ _ _ hM hA T t ht
    (brownianUniformPartialSum_memLp_two B P hB hind j F hF hFi T N T)
    (brownianUniformPartialSum_memLp_two B P hB hind j A ha hAi T N T)
  simp only [brownianUniformPartialSum_terminal] at hh
  exact hh.trans (brownianUniformLeftSum_initial_cutoff_error_bound B P hB hind j F hF
    C ε hC hε hb T hT N hN)

end
end GinibrePoincare
