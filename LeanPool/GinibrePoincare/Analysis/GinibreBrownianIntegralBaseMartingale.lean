/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralBaseMartingale.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralConditional
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyMartingale

/-! Actual coordinate Brownian martingales in their completed joint filtration. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_augmented_coordinate_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (i : ι) : Martingale (B i) (ginibreBrownianAugmentedFiltration B P hB) P := by
  have := Fintype.ofFinite ι
  have hAdapt : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) (B i) :=
    fun t => (ginibreBrownian_augmented_coordinate_measurable_at B P hB t t le_rfl
        i).stronglyMeasurable
  refine ⟨hAdapt, ?_⟩
  intro s t hst
  have hs : Integrable (B i s) P := ((hB i).isGaussianProcess.hasGaussianLaw_eval
      s).memLp_two.integrable (by norm_num)
  have ht : Integrable (B i t) P := ((hB i).isGaussianProcess.hasGaussianLaw_eval
      t).memLp_two.integrable (by norm_num)
  have hCs := condExp_of_stronglyMeasurable ((ginibreBrownianAugmentedFiltration B P hB).le s)
      (hAdapt s) hs
  have hSub := condExp_sub ht hs (ginibreBrownianAugmentedFiltration B P hB s)
  rw [hCs] at hSub
  simp only [Pi.sub_def] at hSub
  have hZero := ginibreBrownian_augmented_increment_condExp_zero B P hB hind s (t-s) i
  simp only [add_tsub_cancel_of_le hst] at hZero
  filter_upwards [hSub, hZero] with ω hω hz
  change _ = 0 at hz
  linarith

end
end GinibrePoincare
