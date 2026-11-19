/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathCompactRestart.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathCompactClosedEquation

/-! # Genuine extension beyond a finite compact collision-free endpoint -/

@[expose] public section
open Set Metric Filter MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_compact_extend_beyond (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (T : ℝ) (hT : 0 < T)
    (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0 + N t + ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (K : Set (Configuration n)) (hK : IsCompact K) (hKcf : ∀ z ∈ K, CollisionFree z)
    (hXK : ∀ t ∈ Ico 0 T, X t ∈ K) :
    ∃ δ > (0 : ℝ), ∃ U : ℝ → Configuration n, EqOn U X (Ico 0 T) ∧
      ContinuousOn U (Icc 0 (T+δ)) ∧
      ∀ t ∈ Icc 0 (T+δ), CollisionFree (U t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (U u)) volume 0 t ∧
        U t = U 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (U u) := by
  classical
  obtain ⟨W, hW, heW, hWEq⟩ := ginibreDrivenPath_compact_closed_equation n α N X hN T hT hX hInt hEq
      K hK hKcf hXK
  have hNT : Continuous (fun u => N (T+u)-N T) :=
    (hN.comp (continuous_const.add continuous_id)).sub continuous_const
  obtain ⟨δ, hδ, F, hF, hF0, hFEq⟩ := ginibreDrivenPath_continuous_noise_local_exists n α (W T)
    (hWEq T ⟨hT.le, le_rfl⟩).1 _ hNT (by simp)
  let U := (Iic T).piecewise W (fun t => F (t-T))
  have hUp (t : ℝ) (ht : t ≤ T) : U t = W t := by simp [U, ht]
  have hUf (t : ℝ) (ht : T ≤ t) : U t = F (t-T) := by
    by_cases hle : t ≤ T
    · have he : t = T := le_antisymm hle ht
      subst t
      simp [U, hF0]
    · simp [U, hle]
  have hU : ContinuousOn U (Icc 0 (T+δ)) := by
    apply ContinuousOn.piecewise
    · intro t ht
      have he : t = T := by simpa only [frontier_Iic, mem_inter_iff, mem_singleton_iff] using ht.2
      subst t
      simpa only [sub_self] using hF0.symm
    · exact hW.continuousOn
    · apply hF.comp (continuous_id.sub continuous_const).continuousOn
      intro t ht
      have hge : T ≤ t := by simpa only [compl_Iic, closure_Ioi, mem_Ici] using ht.2
      dsimp only [Pi.sub_apply, id_eq]
      exact ⟨by linarith, by linarith [ht.1.2]⟩
  have hcf (t : ℝ) (ht : t ∈ Icc 0 (T+δ)) : CollisionFree (U t) := by
    by_cases hle : t ≤ T
    · rw [hUp t hle]
      exact (hWEq t ⟨ht.1, hle⟩).1
    · rw [hUf t (le_of_not_ge hle)]
      exact (hFEq (t-T) ⟨by linarith, by linarith [ht.2]⟩).1
  have hD : ContinuousOn (fun t => ginibreLangevinDrift n α (U t)) (Icc 0 (T+δ)) :=
    fun t ht => (ginibreLangevinDrift_contDiffAt n α (U t) (hcf t
        ht)).continuousAt.comp_continuousWithinAt (hU t ht)
  have hi (t : ℝ) (ht : t ∈ Icc 0 (T+δ)) :
      IntervalIntegrable (fun u => ginibreLangevinDrift n α (U u)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hD.mono (Icc_subset_Icc_right ht.2)
  have hpI (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (U u)) =
      ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (W u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp only
    rw [hUp u (hu.2.trans ht.2)]
  refine ⟨δ, hδ, U, ?_, hU, ?_⟩
  · intro t ht
    rw [hUp t ht.2.le]
    exact heW ht
  · intro t ht
    refine ⟨hcf t ht, hi t ht, ?_⟩
    by_cases hle : t ≤ T
    · rw [hUp t hle, hUp 0 hT.le, hpI t ⟨ht.1, hle⟩]
      exact (hWEq t ⟨ht.1, hle⟩).2.2
    · have htT : T ≤ t := le_of_not_ge hle
      have hfuture := (hFEq (t-T) ⟨by linarith, by linarith [ht.2]⟩).2.2
      have hfi : (∫ u in (0 : ℝ)..(t-T), ginibreLangevinDrift n α (F u)) =
          ∫ u in T..t, ginibreLangevinDrift n α (U u) := by
        have htr := intervalIntegral.integral_comp_add_left (fun u => ginibreLangevinDrift n α (U
            u)) T (a := 0) (b := t-T)
        simp only [add_zero, show T+(t-T)=t by ring] at htr
        rw [← htr]
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le (sub_nonneg.mpr htT)] at hu
        dsimp only
        rw [hUf (T+u) (by linarith [hu.1]), add_sub_cancel_left]
      have hpast := (hWEq T ⟨hT.le, le_rfl⟩).2.2
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (hi T ⟨hT.le, by linarith⟩) ((hi T ⟨hT.le, by linarith⟩).symm.trans (hi t ht))
      rw [hUf t htT, hUp 0 hT.le, hfuture, show T+(t-T)=t by ring, hfi, hpast,
        ← hadj, hpI T ⟨hT.le, le_rfl⟩]
      abel

end
end GinibrePoincare
