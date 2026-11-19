/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupWeakOrder.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupOrder
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup

/-! # Positivity of every actual weak backward Euler step -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Every positive-step inverse of the actual full real generator preserves positivity. -/
theorem ginibreFullGenerator_backward_nonneg (n : ℕ) (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n) (c : ℝ) (hc : 0 < c)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph)
    (hf : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ (u - c • v).val z) :
    ∀ᵐ z ∂ginibreMeasure n, 0 ≤ u.val z := by
  obtain ⟨g, hu, hs, he⟩ :=
    (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp hgraph
  apply ginibreFullWeak_backward_nonneg n hn c hc (u - c • v).val u.val g hf hu hs
  intro w h hw hsw
  have hg := he w h hw hsw
  change inner ℝ u.val w + (c / (n : ℝ)) * inner ℝ g h = inner ℝ (u.val - c • v.val) w
  rw [inner_sub_left, real_inner_smul_left]
  calc
    _ = inner ℝ u.val w + c * ((1 / (n : ℝ)) * inner ℝ g h) := by ring
    _ = _ := by rw [hg]; ring

end
end GinibrePoincare
