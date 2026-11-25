/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module
public import Mathlib.Tactic.Ring
public import LeanPool.ShellsortMean.ThresholdGeometry
public import LeanPool.ShellsortMean.TagThreshold

/-! The footrule does not increase under a gap pass, and controls transport. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

theorem abs_nat_sub_positive_part (a b : ℕ) :
    |(a : ℝ) - (b : ℝ)| =
      2 * ((a - b : ℕ) : ℝ) - ((a : ℝ) - (b : ℝ)) := by
  by_cases hab : b ≤ a
  · have hr : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hab
    rw [Nat.cast_sub hab, abs_of_nonneg (sub_nonneg.mpr hr)]
    ring
  · have hab' : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab'
    rw [Nat.sub_eq_zero_of_le hab', Nat.cast_zero, abs_of_nonpos (sub_nonpos.mpr hr)]
    ring

/-- Footrule can be indexed by physical positions as well as by global key ranks. -/
theorem footrule_by_positions {n : ℕ} (p : RankPlacement n) :
    footrule p = ∑ i : Fin n, |(i.val : ℝ) - ((p.symm i).val : ℝ)| := by
  unfold footrule transport
  have hs := p.symm.sum_comp (fun x => |((p x).val : ℝ) - (x.val : ℝ)|)
  simpa only [Equiv.refl_apply, Equiv.apply_symm_apply] using hs.symm

/-- The exact geometric layer-cake identity. Conservation of the sum of ranks
makes total leftward and rightward displacement equal. -/
theorem footrule_eq_two_sum_rightCuts {n : ℕ} (p : RankPlacement n) :
    footrule p = 2 * ∑ t : Fin n, (rightCutCount p t : ℝ) := by
  rw [footrule_by_positions]
  simp_rw [abs_nat_sub_positive_part]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hzero : (∑ i : Fin n, ((i.val : ℝ) - ((p.symm i).val : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (p.symm.sum_comp (fun i => (i.val : ℝ))).symm
  rw [hzero, sub_zero]
  congr 1
  have hs := congrArg (fun z : ℕ => (z : ℝ)) (sum_rightCutCount p)
  push_cast at hs
  exact hs.symm

/-- Every actual local sorting transition decreases global footrule.
No sortedness, monotonicity, or implementation-cost premise is supplied. -/
theorem gapSort_footrule_le {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    footrule (gapSort p k) ≤ footrule p := by
  rw [footrule_eq_two_sum_rightCuts, footrule_eq_two_sum_rightCuts]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro t _
  exact_mod_cast gapSort_rightCut_le p k t

/-- The physical transport of a real gap-sort transition is at most twice
the starting footrule. Transport is not an insertion-shift count. -/
theorem gapSort_transport_le_two_footrule {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    transport p (gapSort p k) ≤ 2 * footrule p := by
  have ht := transport_le_footrules p (gapSort p k)
  have hm := gapSort_footrule_le p k
  linarith

/-- The formerly conditional geometric lifting interface now applies to
the actual sorting operator with no external monotonicity hypothesis. -/
theorem gapSort_canonical_lift {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    (footrule (gapSort p k) + transport p (gapSort p k)) / 3 ≤ footrule p ∧
    footrule p ≤ footrule (gapSort p k) + transport p (gapSort p k) := by
  exact canonical_lift p (gapSort p k) (gapSort_footrule_le p k)

/-- Monotonicity composes for every finite fixed gap word, including repeated gaps. -/
theorem sortWord_footrule_le {n : ℕ} (p : RankPlacement n) (ks : List ℕ) :
    footrule (sortWord p ks) ≤ footrule p := by
  induction ks generalizing p with
  | nil => exact le_rfl
  | cons k ks ih =>
      exact (ih (gapSort p k)).trans (gapSort_footrule_le p k)

end Shellsort
end
