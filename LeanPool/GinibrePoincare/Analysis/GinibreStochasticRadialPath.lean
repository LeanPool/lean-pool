/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticRadialPath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialDirection
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRGenerator

/-! # Positivity and continuity of the relative radius

The global original solution is adapted, continuous and collision-free almost
surely. Composing it with the smooth polynomial `pairwiseRadius` gives
adaptation and continuity. For `2 ≤ n`, collision-freeness implies that this
radius is strictly positive; the initial value follows from the initial
condition of the original solution. All path properties hold on one event of
full measure for every time, rather than separately almost surely at each time. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_radius_path_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun t ω => pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω))
        ∧
      (∀ t, 0 < pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      pairwiseRadius (ginibreBrownianMaximalProcess n α z B 0 ω)=pairwiseRadius z := by
  obtain ⟨hAdapt, hPath⟩ := ginibreBrownianMaximalProcess_global_original_solution
    (by omega) α z hz B P hB hind
  have hr := (ginibre_contDiff_pairwiseRadius n).continuous
  refine ⟨fun t => (hr.measurable.comp (hAdapt t).measurable).stronglyMeasurable,?_⟩
  filter_upwards [hPath] with ω hω
  have hX : Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B t ω) := by
    simpa only [Real.toNNReal_coe] using
      (show Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B (t : ℝ).toNNReal ω)
        from hω.1.comp NNReal.continuous_coe)
  refine ⟨hr.comp hX,?_,?_⟩
  · intro t
    apply pairwiseRadius_pos_of_collisionFree hn
    simpa only [Real.toNNReal_coe] using hω.2.2.1 t t.coe_nonneg
  · rw [hω.2.1]
end
end GinibrePoincare
