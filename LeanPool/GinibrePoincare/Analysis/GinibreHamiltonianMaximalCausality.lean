/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianMaximalCausality.lean.
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

/-! Causality of the actual uniquely glued maximal solution before either lifetime. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenMaximalPath_noise_causal {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z : Configuration n} (T : ℝ≥0)
    (hN : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z)
    (hM : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α M z)
    (hnoise : EqOn N M (Icc 0 (T : ℝ))) :
    EqOn (ginibreDrivenMaximalPath n α N z) (ginibreDrivenMaximalPath n α M z)
      (Icc 0 (T : ℝ)) := by
  have hX := ginibreDrivenMaximalPath_segment T hN
  have hY := ginibreDrivenMaximalPath_segment T hM
  apply ginibreDrivenPath_finite_interval_unique n α z N _ _ T T.property hX.1 hY.1
    (fun t ht => (hX.2.2 t ht).1) (fun t ht => (hY.2.2 t ht).1)
    (fun t ht => (hX.2.2 t ht).2.2)
  intro t ht
  rw [hnoise ht]
  exact (hY.2.2 t ht).2.2

theorem GinibreDrivenSegment.horizon_lt_lifetime {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} {T : ℝ≥0} {X : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hN : Continuous N) (hN0 : N 0 = 0) :
    (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
  by_cases hT : T = 0
  · subst T
    have hz : CollisionFree z := by rw [← hX.2.1]; exact (hX.2.2 0 (by simp)).1
    simpa using ginibreDrivenMaximalLifetime_pos n α N hN hN0 z hz
  · have ht : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
    let K := X '' Icc 0 (T : ℝ)
    have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hX.1
    have hcf : ∀ y ∈ K, CollisionFree y := by
      rintro y ⟨t, ht, rfl⟩
      exact (hX.2.2 t ht).1
    obtain ⟨δ, hδ, U, he, hc, hp⟩ := ginibreDrivenPath_compact_extend_beyond n α N X hN T ht
      (hX.1.mono Ico_subset_Icc_self) (fun t ht => (hX.2.2 t ⟨ht.1, ht.2.le⟩).2.1)
      (fun t ht => by rw [hX.2.1]; exact (hX.2.2 t ⟨ht.1, ht.2.le⟩).2.2)
      K hK hcf (fun t ht => ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)
    let S : ℝ≥0 := ⟨(T : ℝ)+δ, by positivity⟩
    have hU0 : U 0 = z := (he ⟨le_rfl, ht⟩).trans hX.2.1
    have hS : S ∈ ginibreDrivenHorizons n α N z := by
      refine ⟨U, hc, hU0, ?_⟩
      intro t ht
      have hu := hp t ht
      exact ⟨hu.1, hu.2.1, by simpa only [hU0] using hu.2.2⟩
    apply lt_of_lt_of_le _ (ginibreDrivenHorizons_le_lifetime hS)
    apply ENNReal.coe_lt_coe.mpr
    change T < ⟨(T : ℝ)+δ, _⟩
    exact_mod_cast (lt_add_of_pos_right (T : ℝ) hδ)

end
end GinibrePoincare
