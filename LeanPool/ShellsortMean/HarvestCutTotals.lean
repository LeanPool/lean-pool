/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapMonotone
public import LeanPool.ShellsortMean.RoughGapEndpoint

/-! Sum the cut masses and compare the true quadratic moment along any pass. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestCutTotals
open Finset RoughGapEndpoint RoughGapScaleAssembly

private theorem cut_abs {n : ℕ} (p : RankPlacement n) (t : Fin n) :
    (∑ i, |(slotError p (t.val + 1) i : ℝ)|) = 2 * (rightCutCount p t : ℝ) := by
  have each (i : Fin n) : |(slotError p (t.val + 1) i : ℝ)| =
      2 * (if p.symm i ≤ t ∧ t < i then (1 : ℝ) else 0) -
      (slotError p (t.val + 1) i : ℝ) := by
    simp only [slotError, threshold_mem, Nat.lt_succ_iff, ← Fin.le_def]
    by_cases a : p.symm i ≤ t <;> by_cases b : i ≤ t <;>
      norm_num [a, b, lt_iff_not_ge]
  have zero : (∑ i, (slotError p (t.val + 1) i : ℝ)) = 0 := by exact_mod_cast sum_slotError p _
  simp_rw [each]
  rw [sum_sub_distrib, ← mul_sum, zero, sub_zero, rightCutCount_indicator_sum]
  push_cast
  rfl

theorem total_cut_mass {n : ℕ} (p : RankPlacement n) :
    (∑ t ∈ range n, ∑ i, |(slotError p (t + 1) i : ℝ)|) = footrule p := by
  rw [← Fin.sum_univ_eq_sum_range, footrule_eq_two_sum_rightCuts]
  simp_rw [cut_abs]
  rw [mul_sum]

/-- A key threshold T and a physical cut t can be chosen independently. -/
theorem count_right_le {n : ℕ} (p : RankPlacement n) (h T : ℕ) (t : Fin n) :
    ((thresholdSet (gapSort p h) T).filter (fun i => t < i)).card ≤
      ((thresholdSet p T).filter (fun i => t < i)).card := by
  let byResidue (q : RankPlacement n) (r : ℕ) :=
    (thresholdSet q T).filter (fun i => i.val % h = r)
  have cell (r : ℕ) : ((byResidue (gapSort p h) r).filter (fun i => t < i)).card ≤
        ((byResidue p r).filter (fun i => t < i)).card := by
    apply prefix_right_filter_card_le (chainPositions n h r)
    · intro i hi
      simpa only [chainPositions, mem_filter, mem_univ, true_and] using (mem_filter.mp hi).2
    · intro i hi
      simpa only [chainPositions, mem_filter, mem_univ, true_and] using (mem_filter.mp hi).2
    · exact gapSort_threshold_chain_count p T h r
    · intro i hit j hj hji
      obtain ⟨hi, hr⟩ := mem_filter.mp hit
      have jr : j.val % h = r := by simpa [chainPositions] using hj
      exact mem_filter.mpr ⟨gapSort_threshold_prefix p T h i j hi (jr.trans hr.symm) hji, jr⟩
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
  exact sum_le_sum (fun r _ => cell r)

private theorem weighted_by_tails {n : ℕ} (S : Finset (Fin n)) :
    (∑ i ∈ S, (i.val : ℤ)) = ∑ t : Fin n, ((S.filter (fun i => t < i)).card : ℤ) := by
  have each (i : Fin n) :
      (∑ t : Fin n, if t < i then (1 : ℤ) else 0) = i.val := by
    rw [sum_boole]
    have eq : univ.filter (fun t : Fin n => t < i) = Iio i := by ext; simp
    simp [eq, Fin.card_Iio]
  calc
    _ = ∑ i ∈ S, ∑ t : Fin n, if t < i then (1 : ℤ) else 0 :=
      sum_congr rfl (fun i _ => (each i).symm)
    _ = _ := by rw [sum_comm]; simp only [sum_boole]

private theorem uncenter {n : ℕ} (p : RankPlacement n) (T : ℕ) :
    cutMoment p T =
      (∑ i ∈ thresholdSet p T, (i.val : ℤ)) -
      (∑ i : Fin n, if i.val < T then (i.val : ℤ) else 0) := by
  change (∑ i : Fin n, ((i.val : ℤ) - T) * slotError p T i) = _
  simp_rw [sub_mul]
  rw [sum_sub_distrib, ← mul_sum, sum_slotError, mul_zero, sub_zero]
  simp only [slotError, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib]
  rw [← sum_filter]
  simp

/-- Local sorting moves the lower-key prefix to the left within each chain,
so its total position sum, hence its centered moment, cannot increase. -/
theorem cut_moment_le {n : ℕ} (p : RankPlacement n) (h T : ℕ) :
    cutMoment (gapSort p h) T ≤ cutMoment p T := by
  rw [uncenter, uncenter, weighted_by_tails, weighted_by_tails]
  apply sub_le_sub_right
  apply sum_le_sum
  intro t _
  exact_mod_cast count_right_le p h T t

theorem square_le {n : ℕ} (p : RankPlacement n) (h : ℕ) :
    squareDisplacement (gapSort p h) ≤ squareDisplacement p := by
  rw [← twice_sum_thresholdMoment, ← twice_sum_thresholdMoment]
  apply mul_le_mul_of_nonneg_left _ (by decide)
  apply sum_le_sum
  intro t _
  simpa only [cutMoment_eq_thresholdMoment] using cut_moment_le p h (t + 1)

theorem total_cut_moment {n : ℕ} (p : RankPlacement n) :
    (∑ t ∈ range n, (cutMoment p (t + 1) : ℝ)) = (squareDisplacement p : ℝ) / 2 := by
  simp_rw [cutMoment_eq_thresholdMoment]
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  rw [mul_comm]
  exact_mod_cast twice_sum_thresholdMoment p




end Shellsort.HarvestCutTotals
