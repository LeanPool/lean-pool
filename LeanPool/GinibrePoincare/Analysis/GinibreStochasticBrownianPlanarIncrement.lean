/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianPlanarIncrement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticIndependentBlocks
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticInnovation

/-! Actual planar Brownian increments are independent of the entire joint past. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_planar_increment_independent_past {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P) (s t : ℝ≥0) :
    IndepFun (fun ω => (Br (s+t) ω-Br s ω, Bi (s+t) ω-Bi s ω))
      (fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))) P := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let F : (ℝ≥0 → ℝ) → ℝ × (Set.Iic s → ℝ) := fun p => (p (s+t)-p s, fun v => p v)
  have hmF : Measurable F := by fun_prop
  have hblocks := hind.comp hmF hmF
  have hmBr : Measurable (fun ω (v : Set.Iic s) => Br v ω) := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
  have hmBi : Measurable (fun ω (v : Set.Iic s) => Bi v ω) := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  let : IsProbabilityMeasure (P.map (fun ω (v : Set.Iic s) => Br v ω)) := by infer_instance
  let : IsProbabilityMeasure (P.map (fun ω (v : Set.Iic s) => Bi v ω)) := by infer_instance
  have hr : HasLaw (fun ω => Br (s+t) ω-Br s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Br P
        hBr.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hi : HasLaw (fun ω => Bi (s+t) ω-Bi s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Bi P
        hBi.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  exact ginibre_independent_blocks_recombine P hr ⟨hmBr.aemeasurable, rfl⟩ hi ⟨hmBi.aemeasurable,
      rfl⟩
    (ginibreBrownian_increment_whole_past_independent Br P hBr.toIsPreBrownianReal s t)
    (ginibreBrownian_increment_whole_past_independent Bi P hBi.toIsPreBrownianReal s t) hblocks

theorem ginibreBrownian_planar_increment_hasLaw {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P) (s t : ℝ≥0) :
    HasLaw (fun ω => (Br (s+t) ω-Br s ω, Bi (s+t) ω-Bi s ω))
      ((gaussianReal 0 t).prod (gaussianReal 0 t)) P := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun p : ℝ≥0 → ℝ => p (s+t)-p s) := by fun_prop
  apply (hind.comp hm hm).hasLaw_prod
  · change HasLaw (fun ω => Br (s+t) ω-Br s ω) (gaussianReal 0 t) P
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Br P
        hBr.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  · change HasLaw (fun ω => Bi (s+t) ω-Bi s ω) (gaussianReal 0 t) P
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Bi P
        hBi.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))

end
end GinibrePoincare
