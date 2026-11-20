/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathCompactExtension.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathRestart

/-! # Finite-time limits under the actual compact noncollision criterion -/

@[expose] public section
open Set Metric Filter MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_compact_continuous_extension (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (T : ℝ) (hT : 0 < T)
    (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0 + N t + ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (K : Set (Configuration n)) (hK : IsCompact K) (hKcf : ∀ z ∈ K, CollisionFree z)
    (hXK : ∀ t ∈ Ico 0 T, X t ∈ K) :
    ∃ W : ℝ → Configuration n, Continuous W ∧ EqOn W X (Ico 0 T) ∧
      W T ∈ K ∧ CollisionFree (W T) := by
  have hb : ContinuousOn (ginibreLangevinDrift n α) K :=
    fun z hz => (ginibreLangevinDrift_contDiffAt n α z (hKcf z hz)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (X 0) (hXK 0 ⟨le_rfl, hT⟩))
  let L : ℝ≥0 := ⟨C, hC0⟩
  have hD : ContinuousOn (fun t => ginibreLangevinDrift n α (X t)) (Ico 0 T) := hb.comp hX hXK
  have hDo : ContinuousOn (fun t => ginibreLangevinDrift n α (X t)) (Ioo 0 T) :=
    hD.mono Ioo_subset_Ico_self
  have hDeriv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun u => X u-N u) (ginibreLangevinDrift n α (X t)) t := by
    have hd := (intervalIntegral.integral_hasDerivAt_right (hInt t ⟨ht.1.le, ht.2⟩)
      (hDo.stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hDo.continuousAt (Ioo_mem_nhds ht.1 ht.2))).const_add (X 0)
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    rw [hEq u ⟨hu.1.le, hu.2⟩]
    abel
  have hLip : LipschitzOnWith L (fun u => X u-N u) (Ioo 0 T) :=
    (convex_Ioo (0 : ℝ) T).lipschitzOnWith_of_nnNorm_hasDerivWithin_le
      (fun t ht => (hDeriv t ht).hasDerivWithinAt)
      (fun t ht => by exact_mod_cast hC (X t) (hXK t ⟨ht.1.le, ht.2⟩))
  obtain ⟨Y, hY, heY⟩ := hLip.extend_finite_dimension
  have hlim : Tendsto (fun t => Y t+N t) (nhdsWithin T (Iio T)) (nhds (Y T+N T)) :=
    ((hY.continuous.add hN).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hevent : X =ᶠ[nhdsWithin T (Iio T)] (fun t => Y t+N t) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t ht h0
    have he := heY ⟨h0, ht⟩
    have h := congrArg (fun w => w+N t) he
    simpa only [sub_add_cancel] using h
  have hlimX : Tendsto X (nhdsWithin T (Iio T)) (nhds (Y T+N T)) := hlim.congr' hevent.symm
  have hm : Y T+N T ∈ K := hK.isClosed.mem_of_tendsto hlimX (by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t ht h0
    exact hXK t ⟨h0.le, ht⟩)
  have : (nhdsWithin (0 : ℝ) (Ioo 0 T)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo hT.ne]
    exact ⟨le_rfl, hT.le⟩
  have hOrig0 : Tendsto (fun t => X t-N t) (nhdsWithin 0 (Ioo 0 T)) (nhds (X 0-N 0)) :=
    ((hX.sub hN.continuousOn) 0 ⟨le_rfl, hT⟩).mono Ioo_subset_Ico_self
  have hY0lim : Tendsto Y (nhdsWithin 0 (Ioo 0 T)) (nhds (Y 0)) :=
    hY.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hExt0 : Tendsto (fun t => X t-N t) (nhdsWithin 0 (Ioo 0 T)) (nhds (Y 0)) := by
    apply hY0lim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heY ht).symm
  have he0 : X 0-N 0 = Y 0 := tendsto_nhds_unique hOrig0 hExt0
  refine ⟨fun t => Y t+N t, hY.continuous.add hN, ?_, hm, hKcf _ hm⟩
  intro t ht
  dsimp only
  by_cases ht0 : t = 0
  · subst t
    rw [← he0, sub_add_cancel]
  · have he := heY ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
    rw [← he, sub_add_cancel]

end
end GinibrePoincare
