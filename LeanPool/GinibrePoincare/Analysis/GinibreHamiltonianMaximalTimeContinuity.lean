/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianMaximalTimeContinuity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalLifetime

/-! The actual canonical maximal evaluation is continuous in time wherever alive. -/

@[expose] public section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenMaximalValue_continuousAt_time {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    ContinuousAt (ginibreDrivenMaximalValue n α N z) t := by
  obtain ⟨b, htb, hb⟩ := exists_between ht
  have hbtop : b ≠ ⊤ := (hb.trans_le le_top).ne
  let B : ℝ≥0 := b.toNNReal
  have hB : (B : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
    simpa only [B, ENNReal.coe_toNNReal hbtop] using hb
  have htB : t < B := by
    apply ENNReal.coe_lt_coe.mp
    simpa only [B, ENNReal.coe_toNNReal hbtop] using htb
  have maps : MapsTo (fun u : ℝ≥0 => (u : ℝ)) (Iio B)
      (ginibreDrivenMaximalDomain n α N z) := by
    intro u hu
    refine ⟨u.coe_nonneg, ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.coe_lt_coe.mpr hu).trans hB
  have hc := (ginibreDrivenMaximalPath_continuousOn n α N z).comp
    NNReal.continuous_coe.continuousOn maps
  have hh := (hc t htB).continuousAt (isOpen_Iio.mem_nhds htB)
  simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe, Function.comp_def] using hh

end
end GinibrePoincare
