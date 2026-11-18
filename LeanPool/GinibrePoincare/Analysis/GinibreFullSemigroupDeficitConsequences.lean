/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorDeficit

/-! # Integrated curvature inequality and rigidity on the full generator graph -/

@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory

/-- The integrated Γ₂ inequality holds on the entire actual real generator domain. -/
theorem ginibreFullGenerator_integrated_curvature {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    2 * (-inner ℝ v.val (ginibreFullCenter n hn u.val)) ≤ ‖v.val‖ ^ 2 := by
  obtain ⟨g, -, -, he, -, -, hsecond⟩ :=
    ginibreFullGenerator_deficit_identities_with_dissipation hn u v hgraph
  have htail := modeTail_nonneg
    (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) (fun k => sq_nonneg _)
  nlinarith [sq_nonneg ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖,
    sq_nonneg ‖ginibreFullHolomorphicRemainder n hn u.val‖]

/-- Equality in the full integrated curvature bound is exactly the actual
spectral-gap generator equation. -/
theorem ginibreFullGenerator_integrated_curvature_eq_iff {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ‖v.val‖ ^ 2 = 2 * (-inner ℝ v.val (ginibreFullCenter n hn u.val)) ↔
      v.val = -((2 : ℝ) • ginibreFullCenter n hn u.val) := by
  obtain ⟨g, -, -, he, -, -, hsecond⟩ :=
    ginibreFullGenerator_deficit_identities_with_dissipation hn u v hgraph
  constructor
  · intro heq
    have htail := modeTail_nonneg
      (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) (fun k => sq_nonneg _)
    have hS : ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖,
        sq_nonneg ‖ginibreFullHolomorphicRemainder n hn u.val‖]
    exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hS))
  · intro hv
    rw [hv, norm_neg, norm_smul, Real.norm_eq_abs]
    norm_num
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring

end
end GinibrePoincare
