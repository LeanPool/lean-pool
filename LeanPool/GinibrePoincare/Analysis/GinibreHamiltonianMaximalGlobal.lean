/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianMaximalGlobal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalBlowup

/-! The constructed maximal path is an actual global solution when its lifespan is infinite. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenMaximalPath_global_of_lifetime_top {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n}
    (hglobal : ginibreDrivenMaximalLifetime n α N z = ⊤) :
    Continuous (ginibreDrivenMaximalPath n α N z) ∧
      ginibreDrivenMaximalPath n α N z 0 = z ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (ginibreDrivenMaximalPath n α N z t)) ∧
      IsGinibreDrivenPath n α N (ginibreDrivenMaximalPath n α N z) := by
  have hdom : ginibreDrivenMaximalDomain n α N z = Ici 0 := by
    ext t
    simp only [ginibreDrivenMaximalDomain, Set.mem_ofPred_eq, Set.mem_Ici, hglobal,
      ENNReal.ofReal_lt_top, and_true]
  have hcont : ContinuousOn (ginibreDrivenMaximalPath n α N z) (Ici 0) := by
    rw [← hdom]
    exact ginibreDrivenMaximalPath_continuousOn n α N z
  have hc := hcont.comp_continuous (continuous_id.max continuous_const)
    (fun t => le_max_right t (0 : ℝ))
  have hclip : (fun t => ginibreDrivenMaximalPath n α N z (max t 0)) =
      ginibreDrivenMaximalPath n α N z := by
    funext t
    simp only [ginibreDrivenMaximalPath]
    congr 1
    apply Subtype.ext
    simp [Real.coe_toNNReal']
  change Continuous (fun t => ginibreDrivenMaximalPath n α N z (max t 0)) at hc
  rw [hclip] at hc
  have h0 : ginibreDrivenMaximalPath n α N z 0 = z :=
    (ginibreDrivenMaximalPath_segment 0 (by simp [hglobal])).2.1
  have hp (t : ℝ) (ht : 0 ≤ t) :=
    ginibreDrivenMaximalPath_equation (n := n) (α := α) (N := N) (z := z)
      (by rw [hdom]; exact ht)
  refine ⟨hc, h0, fun t ht => (hp t ht).1, ?_⟩
  exact ⟨fun t ht => (hp t ht).2.1, fun t ht => by rw [h0]; exact (hp t ht).2.2⟩

end
end GinibrePoincare
