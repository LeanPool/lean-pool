/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.ThresholdSort
public import Mathlib.Order.Interval.Finset.Fin

/-! Right-cut counts for binary threshold projections of a gap pass. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Among equally large subsets of an ordered ambient set, an initial segment
has the fewest points strictly to the right of any cut. -/
theorem prefix_right_filter_card_le {α : Type*} [LinearOrder α]
    (A B C : Finset α) (hB : B ⊆ A) (hcard : C.card = B.card)
    (hprefix : ∀ i ∈ C, ∀ j ∈ A, j < i → j ∈ C) (t : α) :
    (C.filter (fun i => t < i)).card ≤ (B.filter (fun i => t < i)).card := by
  by_cases hright : (C.filter (fun i => t < i)).Nonempty
  · obtain ⟨c, hc⟩ := hright
    obtain ⟨hcC, htc⟩ := Finset.mem_filter.mp hc
    have hleft : B.filter (fun i => ¬t < i) ⊆ C.filter (fun i => ¬t < i) := by
      intro j hj
      obtain ⟨hjB, htj⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨hprefix c hcC j (hB hjB) ?_, htj⟩
      exact lt_of_le_of_lt (le_of_not_gt htj) htc
    have hl := Finset.card_le_card hleft
    have hb := Finset.card_filter_add_card_filter_not (s := B) (fun i => t < i)
    have hc' := Finset.card_filter_add_card_filter_not (s := C) (fun i => t < i)
    omega
  · have he : C.filter (fun i => t < i) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hright
    simp only [he, Finset.card_empty, Nat.zero_le]

/-- The count of keys below t+1 that currently lie strictly to the right of t. -/
def rightCutCount {n : ℕ} (p : RankPlacement n) (t : Fin n) : ℕ :=
  ((thresholdSet p (t.val + 1)).filter (fun i => t < i)).card

open Finset in
/-- Sorting one residue chain does not move threshold keys farther to the right of the cut. -/
theorem gapSort_threshold_right_chain_le {n : ℕ} (p : RankPlacement n) (h T r : ℕ) (t : Fin n) :
    (((thresholdSet (gapSort p h) T).filter (fun i => i.val % h = r)).filter
      (fun i => t < i)).card ≤
    (((thresholdSet p T).filter (fun i => i.val % h = r)).filter (fun i => t < i)).card := by
  apply prefix_right_filter_card_le (chainPositions n h r)
  · intro i hi
    simpa only [chainPositions, mem_filter, mem_univ, true_and] using (mem_filter.mp hi).2
  · exact gapSort_threshold_chain_count p T h r
  · intro i hit j hj hji
    obtain ⟨hi, hr⟩ := mem_filter.mp hit
    have jr : j.val % h = r := by simpa [chainPositions] using hj
    exact mem_filter.mpr ⟨gapSort_threshold_prefix p T h i j hi (jr.trans hr.symm) hji, jr⟩

theorem gapSort_rightCut_chain_le {n : ℕ} (p : RankPlacement n) (k r : ℕ) (t : Fin n) :
    (((thresholdSet (gapSort p k) (t.val + 1)).filter
      (fun i => i.val % k = r)).filter (fun i => t < i)).card ≤
    (((thresholdSet p (t.val + 1)).filter
      (fun i => i.val % k = r)).filter (fun i => t < i)).card :=
  gapSort_threshold_right_chain_le p k (t.val + 1) r t

open Finset in
/-- A key threshold T and a physical cut t can be chosen independently. -/
theorem gapSort_threshold_right_le {n : ℕ} (p : RankPlacement n) (h T : ℕ) (t : Fin n) :
    ((thresholdSet (gapSort p h) T).filter (fun i => t < i)).card ≤
      ((thresholdSet p T).filter (fun i => t < i)).card := by
  let byResidue (q : RankPlacement n) (r : ℕ) :=
    (thresholdSet q T).filter (fun i => i.val % h = r)
  have partition (q : RankPlacement n) :
      ((thresholdSet q T).filter (fun i => t < i)).card =
      ∑ r ∈ range n, ((byResidue q r).filter (fun i => t < i)).card := by
    rw [card_eq_sum_card_fiberwise (f := fun i : Fin n => i.val % h) (t := range n)
      (fun i _ => mem_range.mpr (lt_of_le_of_lt (Nat.mod_le _ _) i.isLt))]
    apply sum_congr rfl
    intro r _
    congr 1
    ext i
    simp [byResidue, and_left_comm, and_comm]
  rw [partition, partition]
  exact sum_le_sum (fun r _ => gapSort_threshold_right_chain_le p h T r t)

/-- Actual gap sorting does not increase rightward crossings of any rank cut.
This also covers k=0, which is the already-defined no-op transition. -/
theorem gapSort_rightCut_le {n : ℕ} (p : RankPlacement n) (k : ℕ) (t : Fin n) :
    rightCutCount (gapSort p k) t ≤ rightCutCount p t :=
  gapSort_threshold_right_le p k (t.val + 1) t

theorem rightCutCount_indicator_sum {n : ℕ} (p : RankPlacement n) (t : Fin n) :
    rightCutCount p t = ∑ i : Fin n, if p.symm i ≤ t ∧ t < i then 1 else 0 := by
  unfold rightCutCount thresholdSet
  simp only [Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have he : (p.symm i).val < t.val + 1 ↔ p.symm i ≤ t := by
    change (p.symm i).val < t.val + 1 ↔ (p.symm i).val ≤ t.val
    omega
  simp only [he]

/-- Layer counting: summing cut crossings gives total positive displacement. -/
theorem sum_rightCutCount {n : ℕ} (p : RankPlacement n) :
    (∑ t : Fin n, rightCutCount p t) =
      ∑ i : Fin n, (i.val - (p.symm i).val) := by
  simp_rw [rightCutCount_indicator_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he : Finset.univ.filter (fun t : Fin n => p.symm i ≤ t ∧ t < i) =
      Finset.Ico (p.symm i) i := by
    ext t
    simp
  rw [Finset.sum_boole, he, Fin.card_Ico]
  simp

end Shellsort
end
