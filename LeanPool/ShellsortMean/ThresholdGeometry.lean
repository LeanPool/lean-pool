/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

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
    (A B C : Finset α) (hB : B ⊆ A) (_hC : C ⊆ A) (hcard : C.card = B.card)
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

theorem gapSort_rightCut_chain_le {n : ℕ} (p : RankPlacement n) (k r : ℕ) (t : Fin n) :
    (((thresholdSet (gapSort p k) (t.val + 1)).filter
      (fun i => i.val % k = r)).filter (fun i => t < i)).card ≤
    (((thresholdSet p (t.val + 1)).filter
      (fun i => i.val % k = r)).filter (fun i => t < i)).card := by
  apply prefix_right_filter_card_le (chainPositions n k r)
  · intro i hi
    simpa only [chainPositions, Finset.mem_filter, Finset.mem_univ, true_and]
      using (Finset.mem_filter.mp hi).2
  · intro i hi
    simpa only [chainPositions, Finset.mem_filter, Finset.mem_univ, true_and]
      using (Finset.mem_filter.mp hi).2
  · exact gapSort_threshold_chain_count p (t.val + 1) k r
  · intro i hi j hj hji
    obtain ⟨hiT, hiC⟩ := Finset.mem_filter.mp hi
    have hjC : j.val % k = r := by simpa only
      [chainPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    exact Finset.mem_filter.mpr
      ⟨gapSort_threshold_prefix p (t.val + 1) k i j hiT (hjC.trans hiC.symm) hji, hjC⟩

/-- Actual gap sorting does not increase rightward crossings of any rank cut.
This also covers k=0, which is the already-defined no-op transition. -/
theorem gapSort_rightCut_le {n : ℕ} (p : RankPlacement n) (k : ℕ) (t : Fin n) :
    rightCutCount (gapSort p k) t ≤ rightCutCount p t := by
  have hdecomp : ∀ q : RankPlacement n, rightCutCount q t =
      ∑ r ∈ Finset.range n, (((thresholdSet q (t.val + 1)).filter
        (fun i => i.val % k = r)).filter (fun i => t < i)).card := by
    intro q
    unfold rightCutCount
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i : Fin n => i.val % k)
      (t := Finset.range n) (fun i _ =>
        Finset.mem_range.mpr (lt_of_le_of_lt (Nat.mod_le _ _) i.isLt))]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    ext i
    simp only [Finset.mem_filter, and_left_comm, and_comm]
  rw [hdecomp, hdecomp]
  exact Finset.sum_le_sum (fun r _ => gapSort_rightCut_chain_le p k r t)

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
