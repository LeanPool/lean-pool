/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianMaximalLifetime.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalPath

/-! Lifespan bounds and the actual local regularity of the glued maximal path. -/

@[expose] public section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenHorizons_le_lifetime {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} {T : ℝ≥0} (hT : T ∈ ginibreDrivenHorizons n α N z) :
    (T : ℝ≥0∞) ≤ ginibreDrivenMaximalLifetime n α N z :=
  le_iSup_of_le ⟨T, hT⟩ le_rfl

/-- The real times `t ≥ 0` strictly before the maximal lifetime of the driven Ginibre path. -/
def ginibreDrivenMaximalDomain (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < ginibreDrivenMaximalLifetime n α N z}

theorem ginibreDrivenMaximalPath_continuousOn (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n) :
    ContinuousOn (ginibreDrivenMaximalPath n α N z) (ginibreDrivenMaximalDomain n α N z) := by
  intro t ht
  obtain ⟨b, htb, hb⟩ := exists_between ht.2
  have hbtop : b ≠ ⊤ := (hb.trans_le le_top).ne
  let B : ℝ≥0 := b.toNNReal
  have hB : (B : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
    simpa only [B, ENNReal.coe_toNNReal hbtop] using hb
  have htB : t < (B : ℝ) := by
    apply (ENNReal.ofReal_lt_coe_iff ht.1).mp
    simpa only [B, ENNReal.coe_toNNReal hbtop] using htb
  have hs := ginibreDrivenMaximalPath_segment B hB
  apply (hs.1 t ⟨ht.1, htB.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htB)] with u hu huB
  exact ⟨hu.1, huB.le⟩

theorem ginibreDrivenMaximalPath_initial (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) (z : Configuration n) (hz : CollisionFree z) :
    ginibreDrivenMaximalPath n α N z 0 = z := by
  have hp := ginibreDrivenMaximalLifetime_pos n α N hN hN0 z hz
  exact (ginibreDrivenMaximalPath_segment 0 (by simpa using hp)).2.1

theorem ginibreDrivenMaximalPath_equation {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} {t : ℝ} (ht : t ∈ ginibreDrivenMaximalDomain n α N z) :
    CollisionFree (ginibreDrivenMaximalPath n α N z t) ∧
      IntervalIntegrable (fun u => ginibreLangevinDrift n α (ginibreDrivenMaximalPath n α N z u))
          volume 0 t ∧
      ginibreDrivenMaximalPath n α N z t = z+N t+
        ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (ginibreDrivenMaximalPath n α N z u) := by
  have hs := ginibreDrivenMaximalPath_segment (Real.toNNReal t) ht.2
  exact hs.2.2 t ⟨ht.1, by rw [Real.coe_toNNReal t ht.1]⟩

end
end GinibrePoincare
