/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathRestart.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathVolterraUniqueness
public import Mathlib.Topology.Order.IntermediateValue

/-! # Restarting the actual additive-noise Ginibre equation -/

@[expose] public section
open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_shift (n : ℕ) (α : ℝ) (N X : ℝ → Configuration n)
    (hX : IsGinibreDrivenPath n α N X) (s : ℝ) (hs : 0 ≤ s) :
    IsGinibreDrivenPath n α (fun t => N (s+t)-N s) (fun t => X (s+t)) := by
  have hi (t : ℝ) (ht : 0 ≤ t) :
      IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume s (s+t) :=
    (hX.1 s hs).symm.trans (hX.1 (s+t) (by linarith))
  constructor
  · intro t ht
    simpa only [sub_self, add_sub_cancel_left] using (hi t ht).comp_add_left s
  · intro t ht
    have hst := hX.2 (s+t) (by linarith)
    have h0 := hX.2 s hs
    have hadj := intervalIntegral.integral_add_adjacent_intervals (hX.1 s hs) (hi t ht)
    have htr : (∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X (s+u))) =
        ∫ u in s..(s+t), ginibreLangevinDrift n α (X u) := by
      simpa only [add_zero] using intervalIntegral.integral_comp_add_left
        (fun u => ginibreLangevinDrift n α (X u)) (a := (0 : ℝ)) (b := t) s
    dsimp only
    rw [htr]
    rw [← hadj] at hst
    simp only [add_zero]
    rw [hst, h0]
    abel

theorem ginibreDrivenPath_restart_local_unique (n : ℕ) (α : ℝ)
    (N X Z : ℝ → Configuration n) (hN : Continuous N) (hX : Continuous X) (hZ : Continuous Z)
    (hXN : IsGinibreDrivenPath n α N X) (hZN : IsGinibreDrivenPath n α N Z)
    (s : ℝ) (hs : 0 ≤ s) (heq : X s = Z s) (hz : CollisionFree (X s)) :
    ∃ T > (0 : ℝ), ∀ t ∈ Icc s (s+T), X t = Z t := by
  have hNs : Continuous (fun t => N (s+t)-N s) :=
    (hN.comp (continuous_const.add continuous_id)).sub continuous_const
  have hXs : Continuous (fun t => X (s+t)) := hX.comp (continuous_const.add continuous_id)
  have hZs : Continuous (fun t => Z (s+t)) := hZ.comp (continuous_const.add continuous_id)
  obtain ⟨T, hT, hTZ⟩ := ginibreDrivenPath_local_pathwise_unique n α _ _ _ hNs hXs hZs
    (ginibreDrivenPath_shift n α N X hXN s hs) (ginibreDrivenPath_shift n α N Z hZN s hs)
    (by simpa only [add_zero] using heq) (by simpa only [add_zero] using hz)
  refine ⟨T, hT, ?_⟩
  intro t ht
  have h := hTZ (show t-s ∈ Icc 0 T from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  simpa only [show s+(t-s)=t by ring] using h

theorem ginibreDrivenPath_unique_before_collision (n : ℕ) (α : ℝ)
    (N X Z : ℝ → Configuration n) (hN : Continuous N) (hX : Continuous X) (hZ : Continuous Z)
    (hXN : IsGinibreDrivenPath n α N X) (hZN : IsGinibreDrivenPath n α N Z)
    (h0 : X 0 = Z 0) (T : ℝ)
    (hcf : ∀ t ∈ Icc 0 T, CollisionFree (X t)) : EqOn X Z (Icc 0 T) := by
  have hc : IsClosed ({t | X t = Z t} ∩ Icc 0 T) := (isClosed_eq hX hZ).inter isClosed_Icc
  apply hc.Icc_subset_of_forall_mem_nhdsWithin h0
  intro s hs
  obtain ⟨δ, hδ, heq⟩ := ginibreDrivenPath_restart_local_unique n α N X Z hN hX hZ hXN hZN
    s hs.2.1 hs.1 (hcf s ⟨hs.2.1, hs.2.2.le⟩)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show s < s+δ by linarith))] with t hst htd
  exact heq t ⟨hst.le, htd.le⟩

end
end GinibrePoincare
