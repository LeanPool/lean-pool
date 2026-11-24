/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapMonotone
public import LeanPool.ShellsortMean.GapInsertionBridge
public import Mathlib.Order.Interval.Finset.Nat

/-! A direct finite charging proof of the classical inversion--footrule inequality.
An inverted pair `(i,j)` is charged to `(i,r j)` if `u i ≤ r j`, and otherwise
to `(j,u i)`. The two capacities are exactly the two directional displacements.
The generic lemma needs only injectivity of the two natural-valued coordinates;
it does not assume a cost bound or an external sorting algorithm.
-/
@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

theorem inversion_charge_left_le {α : Type*} [Fintype α]
    (u r : α → ℕ) (hr : Function.Injective r) (i : α) :
    (Finset.univ.filter (fun j => u i < u j ∧ r j < r i ∧ u i ≤ r j)).card ≤
      r i - u i := by
  rw [← Nat.card_Ico]
  apply Finset.card_le_card_of_injOn r
  · intro j hj
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hj).2.2.2,
      (Finset.mem_filter.mp hj).2.2.1⟩
  · intro j _ k _ h
    exact hr h

theorem inversion_charge_right_le {α : Type*} [Fintype α]
    (u r : α → ℕ) (hu : Function.Injective u) (j : α) :
    (Finset.univ.filter (fun i => u i < u j ∧ r j < r i ∧ r j < u i)).card ≤
      u j - r j := by
  rw [← Nat.card_Ico]
  apply Finset.card_le_card_of_injOn u
  · intro i hi
    exact Finset.mem_Ico.mpr ⟨le_of_lt (Finset.mem_filter.mp hi).2.2.2,
      (Finset.mem_filter.mp hi).2.1⟩
  · intro i _ k _ h
    exact hu h

/-- Two injective integer coordinates suffice; a common coordinate range is
not needed. Counts are ordinary inversions in their induced orders. -/
theorem coordinate_inversions_le_displacement {α : Type*}
    [Fintype α] (u r : α → ℕ)
    (hu : Function.Injective u) (hr : Function.Injective r) :
    (∑ j : α, ∑ i : α, if u i < u j ∧ r j < r i then 1 else 0) ≤
      ∑ i : α, ((r i - u i) + (u i - r i)) := by
  have split (i j : α) :
      (if u i < u j ∧ r j < r i then 1 else 0) =
      (if u i < u j ∧ r j < r i ∧ u i ≤ r j then 1 else 0) +
      (if u i < u j ∧ r j < r i ∧ r j < u i then 1 else 0) := by
    by_cases h : u i < u j ∧ r j < r i
    · by_cases ht : u i ≤ r j
      · simp [h.1, h.2, ht, not_lt_of_ge ht]
      · simp [h.1, h.2, ht, Nat.lt_of_not_ge ht]
    · rcases not_and_or.mp h with h | h <;> simp [h]
  simp_rw [split, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j i =>
    if u i < u j ∧ r j < r i ∧ u i ≤ r j then (1 : ℕ) else 0)]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using
      inversion_charge_left_le u r hr i
  · apply Finset.sum_le_sum
    intro j _
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using
      inversion_charge_right_le u r hu j

theorem nat_directional_displacement (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  by_cases hab : b ≤ a
  · have hreal : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hab
    rw [Nat.sub_eq_zero_of_le hab, add_zero, Nat.cast_sub hab,
      abs_of_nonneg (sub_nonneg.mpr hreal)]
  · have hba : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    have hreal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hba
    rw [Nat.sub_eq_zero_of_le hba, zero_add, Nat.cast_sub hba,
      abs_of_nonpos (sub_nonpos.mpr hreal)]
    ring

/-- Real-valued form, ready for geometric and expected-cost interfaces. -/
theorem coordinate_inversions_le_abs_displacement {α : Type*}
    [Fintype α] (u r : α → ℕ)
    (hu : Function.Injective u) (hr : Function.Injective r) :
    ((∑ j : α, ∑ i : α, if u i < u j ∧ r j < r i then 1 else 0 : ℕ) : ℝ) ≤
      ∑ i : α, |(r i : ℝ) - (u i : ℝ)| := by
  have hc := coordinate_inversions_le_displacement u r hu hr
  have hcast := Nat.cast_le (α := ℝ).mpr hc
  push_cast at hcast
  push_cast
  simpa only [← Nat.cast_add, nat_directional_displacement] using hcast

/-- The actual global inversion count is at most global footrule, for every
finite placement. This is a deterministic theorem, with no input-law premise. -/
theorem ordinaryInversions_le_footrule {n : ℕ} (p : RankPlacement n) :
    (gapInversions p 1 : ℝ) ≤ footrule p := by
  rw [gapInversions_nat_pair_sum, footrule_by_positions]
  have h := coordinate_inversions_le_abs_displacement
    (fun i : Fin n => i.val) (fun i => (p.symm i).val)
    Fin.val_injective (Fin.val_injective.comp p.symm.injective)
  simpa only [Nat.mod_one, and_true, Fin.val_fin_lt, abs_sub_comm] using h

/-- Consequently the executed gap-1 insertion right-shift counter has the
same deterministic upper bound. This does not count comparisons or writes. -/
theorem ordinaryInsertionCost_le_footrule {n : ℕ} (p : RankPlacement n) :
    (gapInsertionCost p 1 (by decide) : ℝ) ≤ footrule p := by
  rw [gapInsertionCost_eq_gapInversions]
  exact ordinaryInversions_le_footrule p

end Shellsort
end
