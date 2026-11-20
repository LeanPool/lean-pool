/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCollisionSupport.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCollisionProductRates

/-!
# Correspondence collision support

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `correspondenceCollisionProduct_compact_test`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped ContDiff

theorem correspondenceCollisionProduct_support_separated (n : ℕ) (ε : ℝ)
    (hε : 0 < ε) (p : VandermondePair n) :
    tsupport (correspondenceCollisionProduct n ε) ⊆
      {z | ε ≤ ‖z p.val.1-z p.val.2‖} := by
  classical
  apply closure_minimal
  · intro z hz
    by_contra h
    have he := correspondenceCollisionCutoff_zero p.val.1 p.val.2 hε z (le_of_not_ge h)
    have hp : correspondenceCollisionProduct n ε z = 0 := by
      unfold correspondenceCollisionProduct
      exact Finset.prod_eq_zero (Finset.mem_univ p) he
    exact hz hp
  · exact isClosed_le continuous_const
      ((continuous_apply p.val.1).sub (continuous_apply p.val.2)).norm

theorem correspondenceCollisionProduct_support_collisionFree (n : ℕ) (ε : ℝ)
    (hε : 0 < ε) : tsupport (correspondenceCollisionProduct n ε) ⊆
      {z | CollisionFree z} := by
  intro z hz j k he
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with h|h
  · have hb := correspondenceCollisionProduct_support_separated n ε hε ⟨(j, k), h⟩ hz
    simp only [Set.mem_ofPred_eq, he, sub_self, norm_zero] at hb
    linarith
  · have hb := correspondenceCollisionProduct_support_separated n ε hε ⟨(k, j), h⟩ hz
    simp only [Set.mem_ofPred_eq, he, sub_self, norm_zero] at hb
    linarith

/-- The literal product cutoff gives a smooth compact test supported away from collisions. -/
theorem correspondenceCollisionProduct_compact_test (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun z => f z*correspondenceCollisionProduct n ε z) ∧
    HasCompactSupport (fun z => f z*correspondenceCollisionProduct n ε z) ∧
    tsupport (fun z => f z*correspondenceCollisionProduct n ε z) ⊆ {z | CollisionFree z} := by
  refine ⟨hf.mul (correspondenceCollisionProduct_smooth n ε), hc.mul_right,?_⟩
  exact tsupport_mul_subset_right.trans
    (correspondenceCollisionProduct_support_collisionFree n ε hε)

end
end GinibrePoincare
