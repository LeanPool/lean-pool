/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# The lower bound as a function of the dimension and the cardinalities

The lower bound in Ruzsa's theorem for sets `A` and `B` with `|A| = n ≥ |B| = m` and `A + B` of
affine dimension `d` is `sumsetCardLowerBound d m n = n + ∑ t ∈ {1, …, m - 1}, min d (n - t)`, the
function `G_d(m, n)` of the paper. The induction in the proof removes one point from `A`, from
`B`, or from both, and the dimension stays the same or drops by one. This file proves the
inequality between the values of the bound that each of these cases needs.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open Finset

/-- The lower bound `G_d(m, n)` of Ruzsa's theorem for the size of a sumset of affine dimension `d`
of sets of sizes `m ≤ n`. -/
def sumsetCardLowerBound (d m n : ℕ) : ℕ :=
  n + ∑ t ∈ Icc 1 (m - 1), min d (n - t)

/-- The definition of `sumsetCardLowerBound`. -/
lemma sumsetCardLowerBound_eq (d m n : ℕ) :
    sumsetCardLowerBound d m n = n + ∑ t ∈ Icc 1 (m - 1), min d (n - t) := by
  rfl

private lemma sum_Icc_one_add_one (f : ℕ → ℕ) (k : ℕ) :
    ∑ t ∈ Icc 1 (k + 1), f t = f 1 + ∑ t ∈ Icc 1 k, f (t + 1) := by
  rw [← add_sum_Ioc_eq_sum_Icc (by grind), ← Icc_add_one_left_eq_Ioc, ← map_add_right_Icc,
    sum_map]
  rfl

private lemma sum_min_le_sum_min_sub_one_add (d n k : ℕ) :
    ∑ t ∈ Icc 1 k, min d (n - t) ≤ ∑ t ∈ Icc 1 k, min (d - 1) (n - 1 - t) + k := by
  refine (sum_le_sum (g := fun t ↦ min (d - 1) (n - 1 - t) + 1) ?_).trans ?_
  · grind
  · rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, mul_one, Nat.add_sub_cancel]

/-- `G_d(m, n) = G_d(m - 1, n - 1) + min (d + 1) n` for `m ≥ 2`. -/
lemma sumsetCardLowerBound_eq_add_min {d m n : ℕ} (hm : 2 ≤ m) :
    sumsetCardLowerBound d m n = sumsetCardLowerBound d (m - 1) (n - 1) + min (d + 1) n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, (by grind : k + 2 - 1 = k + 1),
    (by grind : k + 1 - 1 = k), sum_Icc_one_add_one]
  simp only [Nat.sub_add_eq, Nat.sub_right_comm _ _ 1]
  grind

private lemma sumsetCardLowerBound_le_large_deletion {d m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    sumsetCardLowerBound d m n ≤ n + sumsetCardLowerBound (d - 1) (m - 1) (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, (by grind : k + 2 - 1 = k + 1),
    (by grind : k + 1 - 1 = k), sum_Icc_succ_top (by grind)]
  grind [sum_min_le_sum_min_sub_one_add d n k]

private lemma sumsetCardLowerBound_mono_right (d m : ℕ) : Monotone (sumsetCardLowerBound d m) := by
  intro a b hab
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq]
  gcongr

/-- The case in which one point is removed from each set and the dimension does not change: the
sumset loses at least `d + 1` points. -/
lemma sumsetCardLowerBound_of_full_case {d m n p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound d (m - 1) (n - 1) ≤ p) (hcard : p + d + 1 ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  grind [sumsetCardLowerBound_eq_add_min (d := d) (n := n) hm]

/-- The case in which one point is removed from each set and the dimension drops by one: the
sumset loses at least `n` points. -/
lemma sumsetCardLowerBound_of_large_case {d m n p s : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) (n - 1) ≤ p) (hcard : n + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  grind [sumsetCardLowerBound_le_large_deletion (d := d) hm hmn]

/-- The case in which one point is removed from the smaller set and the dimension drops by one:
the sumset loses at least `n` points. -/
lemma sumsetCardLowerBound_of_small_case {d m n p s : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) n ≤ p) (hcard : n + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  grind [sumsetCardLowerBound_le_large_deletion (d := d) hm hmn,
    sumsetCardLowerBound_mono_right (d - 1) (m - 1) (n.sub_le 1)]

/-- The case in which the sets have the same size `m`, one point is removed from one of them and
the dimension drops by one: the sumset loses at least `m` points. -/
lemma sumsetCardLowerBound_of_equal_right_case {d m p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) m ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m m ≤ s :=
  sumsetCardLowerBound_of_small_case hm le_rfl hrec hcard

/-- The case in which one point is removed from the strictly larger set and the dimension drops
by one: the sumset loses at least `m` points. -/
lemma sumsetCardLowerBound_of_strict_right_case {d m n p s : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (hrec : sumsetCardLowerBound (d - 1) m (n - 1) ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  rw [sumsetCardLowerBound_eq] at hrec ⊢
  grind [sum_min_le_sum_min_sub_one_add d n (m - 1)]

end SumOfSetsInSeveralDimensions
