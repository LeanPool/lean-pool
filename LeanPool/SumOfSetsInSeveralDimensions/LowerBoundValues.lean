/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.LowerBoundFunction
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The values of the lower bound

The formulas (1.5), (1.6) and (1.7) of Ruzsa's paper for `G_d(m, n) = sumsetCardLowerBound d m n`
when `m ≤ n`. Write `t = n - m`.

* `sumsetCardLowerBound_of_add_le`: if `t ≥ d - 1`, then `G_d(m, n) = n + d * (m - 1)`. The paper
  states this for `t ≥ d`.
* `two_mul_sumsetCardLowerBound_add_add`, `two_mul_sumsetCardLowerBound_add`: if `t < d < n`,
  then `2 * G_d(m, n) = 2 * n * (d + 1) - d * (d + 1) - t * (t + 1)` and
  `2 * G_d(m, n) = 2 * (n + d * (m - 1)) - (d - t) * (d - t - 1)`.
* `two_mul_sumsetCardLowerBound_of_le`: if `1 ≤ m ≤ n ≤ d`, then
  `2 * G_d(m, n) = 2 * n + (m - 1) * (2 * n - m)`.
-/

public section

namespace SumOfSetsInSeveralDimensions

open Finset

variable {d m n : ℕ}

/-- `G_d(m + 1, n) = G_d(m, n) + min d (n - m)` for `m ≥ 1`. -/
lemma sumsetCardLowerBound_add_one (hm : 1 ≤ m) :
    sumsetCardLowerBound d (m + 1) n = sumsetCardLowerBound d m n + min d (n - m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, Nat.add_sub_cancel, Nat.add_sub_cancel,
    sum_Icc_succ_top (by grind)]
  grind

/-- **Formula (1.5).** If `m + d ≤ n + 1`, then `G_d(m, n) = n + d * (m - 1)`. -/
lemma sumsetCardLowerBound_of_add_le (h : m + d ≤ n + 1) :
    sumsetCardLowerBound d m n = n + d * (m - 1) := by
  rw [sumsetCardLowerBound_eq, sum_const_nat (m := d) (by grind), Nat.card_Icc]
  grind

/-- **Formula (1.6).** If `m ≤ n < m + d` and `d < n`, then
`2 * G_d(m, n) + d * (d + 1) + (n - m) * (n - m + 1) = 2 * n * (d + 1)`. -/
lemma two_mul_sumsetCardLowerBound_add_add (hmn : m ≤ n) (hnm : n < m + d) (hdn : d < n) :
    2 * sumsetCardLowerBound d m n + d * (d + 1) + (n - m) * (n - m + 1) = 2 * n * (d + 1) := by
  induction m, (by grind : n + 1 - d ≤ m) using Nat.le_induction with
  | base =>
    rw [sumsetCardLowerBound_of_add_le (by grind)]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hdn
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' (by grind : 1 ≤ d)
    rw [(by grind : e + 1 + c + 1 + 1 - (e + 1) - 1 = c + 1),
      (by grind : e + 1 + c + 1 - (e + 1 + c + 1 + 1 - (e + 1)) = e)]
    ring
  | succ m hm ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [sumsetCardLowerBound_add_one (by grind), (by grind : m + t + 1 - (m + 1) = t),
      (by grind : min d (m + t + 1 - m) = t + 1)]
    rw [(by grind : m + t + 1 - m = t + 1)] at ih
    nlinarith [ih (by grind) (by grind)]

/-- **Formula (1.6), first form.** If `m ≤ n < m + d` and `d < n`, then
`2 * G_d(m, n) + (d - t) * (d - t - 1) = 2 * (n + d * (m - 1))`, where `t = n - m`. -/
lemma two_mul_sumsetCardLowerBound_add (hmn : m ≤ n) (hnm : n < m + d) (hdn : d < n) :
    2 * sumsetCardLowerBound d m n + (d - (n - m)) * (d - (n - m) - 1) =
      2 * (n + d * (m - 1)) := by
  have h := two_mul_sumsetCardLowerBound_add_add hmn hnm hdn
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (by grind : t < d)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by grind : 1 ≤ m)
  rw [Nat.add_sub_cancel_left] at h
  rw [Nat.add_sub_cancel_left, (by grind : t + k + 1 - t = k + 1), Nat.add_sub_cancel,
    Nat.add_sub_cancel]
  nlinarith [h]

/-- **Formula (1.7).** If `1 ≤ m ≤ n ≤ d`, then `2 * G_d(m, n) = 2 * n + (m - 1) * (2 * n - m)`. -/
lemma two_mul_sumsetCardLowerBound_of_le (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : n ≤ d) :
    2 * sumsetCardLowerBound d m n = 2 * n + (m - 1) * (2 * n - m) := by
  induction m, hm using Nat.le_induction with
  | base => simp [sumsetCardLowerBound_eq]
  | succ m hm ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [sumsetCardLowerBound_add_one hm, (by grind : min d (m + t + 1 - m) = t + 1),
      Nat.add_sub_cancel, (by grind : 2 * (m + t + 1) - (m + 1) = m + 2 * t + 1)]
    rw [(by grind : 2 * (m + t + 1) - m = m + 2 * t + 2)] at ih
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rw [Nat.add_sub_cancel] at ih
    nlinarith [ih (by grind)]

end SumOfSetsInSeveralDimensions
