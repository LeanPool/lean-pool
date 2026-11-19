/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalGlobal
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOUUniqueness

/-! Actual autonomous projected canonical solutions and center OU identification. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem collisionFree_recentered {n : ℕ} {z : Configuration n} (hz : CollisionFree z) :
    CollisionFree (recenteredConfiguration n z) := by
  intro i j hij
  apply hz
  change z i-coordinateSum z/(n : ℂ) = z j-coordinateSum z/(n : ℂ) at hij
  simpa only [sub_add_cancel] using congrArg
    (fun v : ℂ => v+coordinateSum z/(n : ℂ)) hij

theorem ginibreDrivenPath_recentered_segment {n : ℕ} {α : ℝ}
    {N X : ℝ → Configuration n} (hX : Continuous X)
    (hFree : ∀ t : ℝ, 0 ≤ t → CollisionFree (X t))
    (hEq : IsGinibreDrivenPath n α N X) (T : ℝ≥0) :
    GinibreDrivenSegment n α (fun t => recenteredConfiguration n (N t))
      (recenteredConfiguration n (X 0)) T (fun t => recenteredConfiguration n (X t)) := by
  have hY : Continuous (fun t => recenteredConfiguration n (X t)) :=
    by simpa only [Function.comp_def, recenteredCLM_apply] using (recenteredCLM n).continuous.comp
         hX
  refine ⟨hY.continuousOn, rfl, ?_⟩
  intro t ht
  have hCF := collisionFree_recentered (hFree t ht.1)
  have hD : ContinuousOn (fun s => ginibreLangevinDrift n α (recenteredConfiguration n (X s)))
      (Icc 0 t) := by
    intro s hs
    exact (ginibreLangevinDrift_contDiffAt n α _ (collisionFree_recentered (hFree s
        hs.1))).continuousAt.comp_continuousWithinAt
      (f := fun u : ℝ => recenteredConfiguration n (X u)) (x := s)
      hY.continuousAt.continuousWithinAt
  exact ⟨hCF, hD.intervalIntegrable_of_Icc ht.1,
    ginibreDrivenPath_recentered_equation n α N X hEq t ht.1⟩

theorem ginibreDrivenPath_recentered_canonical_global {n : ℕ} {α : ℝ}
    {N X : ℝ → Configuration n} (hX : Continuous X)
    (hFree : ∀ t : ℝ, 0 ≤ t → CollisionFree (X t))
    (hEq : IsGinibreDrivenPath n α N X) :
    ginibreDrivenMaximalLifetime n α (fun t => recenteredConfiguration n (N t))
      (recenteredConfiguration n (X 0)) = ⊤ ∧
    ∀ t : ℝ≥0, ginibreDrivenMaximalValue n α (fun s => recenteredConfiguration n (N s))
      (recenteredConfiguration n (X 0)) t = recenteredConfiguration n (X t) := by
  have hSeg := ginibreDrivenPath_recentered_segment hX hFree hEq
  have hLife : ginibreDrivenMaximalLifetime n α (fun t => recenteredConfiguration n (N t))
      (recenteredConfiguration n (X 0)) = ⊤ := by
    by_contra hfin
    let L := ginibreDrivenMaximalLifetime n α (fun t => recenteredConfiguration n (N t))
      (recenteredConfiguration n (X 0))
    let T := L.toNNReal+1
    have hb := ginibreDrivenHorizons_le_lifetime (show T ∈ ginibreDrivenHorizons n α
      (fun t => recenteredConfiguration n (N t)) (recenteredConfiguration n (X 0)) from ⟨_, hSeg T⟩)
    change (T : ℝ≥0∞) ≤ L at hb
    have hfinL : L ≠ ⊤ := hfin
    rw [← ENNReal.coe_toNNReal hfinL] at hb
    have hbad := ENNReal.coe_le_coe.mp hb
    change L.toNNReal+1 ≤ L.toNNReal at hbad
    exact (not_le_of_gt (lt_add_of_pos_right L.toNNReal zero_lt_one)) hbad
  refine ⟨hLife, fun t => ?_⟩
  exact ginibreDrivenMaximalValue_eq_segment (hSeg t) t le_rfl (by simp [hLife])

theorem ginibreDrivenPath_center_eq_OU {n : ℕ} {α : ℝ}
    {N X : ℝ → Configuration n} (hN : Continuous N) (hX : Continuous X)
    (hEq : IsGinibreDrivenPath n α N X) (t : ℝ) (ht : 0 ≤ t) :
    coordinateSum (X t) = drivenOUPath (2*α/(n : ℝ)) (coordinateSum (X 0))
      (fun s => coordinateSum (N s)) t := by
  apply drivenOUPath_unique_nonneg
    (2*α/(n : ℝ)) (coordinateSum (X 0)) (fun s => coordinateSum (N s))
    (fun s => coordinateSum (X s))
    (by simpa only [Function.comp_def, coordinateSumCLM_apply] using (coordinateSumCLM
          n).continuous.comp hN)
    (by simpa only [Function.comp_def, coordinateSumCLM_apply] using (coordinateSumCLM
          n).continuous.comp hX)
    (fun s hs => ginibreDrivenPath_center_equation n α N X hEq s hs) t ht

end
end GinibrePoincare
