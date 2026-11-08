/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import LeanPool.SumOfSetsInSeveralDimensions.LowerBound
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The closed form of Ruzsa's bound

For `1 ≤ m ≤ n` the sum `∑ t ∈ {1, …, m - 1}, min d (n - t)` is at least
`d * m - d * (d + 1) / 2`. With Ruzsa's theorem this gives the asymmetric form of Freiman's lemma:
if `A, B ⊆ ℝ^D` are finite sets with `B` nonempty and `|B| ≤ |A|`, and `d` is at most the affine
dimension of `A + B`, then `|A + B| ≥ |A| + d * |B| - d * (d + 1) / 2`.

## Main statements

* `card_add_mul_card_le_card_add_add`: the bound, as `|A| + d * |B| ≤ |A + B| + d * (d + 1) / 2`
  in `ℕ`.
* `card_add_mul_card_le_card_add_add_of_le_finrank_span_sub`: the same bound, with the affine
  dimension written as the dimension of the span of `(A + B) - (A + B)`.
* `two_mul_card_add_mul_card_le`: the same bound multiplied by two, without division.
* `card_add_mul_card_sub_le_card_add`: the same bound in `ℝ`.
* `max_card_add_mul_min_card_le_card_add_add`: the bound without the assumption `|B| ≤ |A|`, with
  the larger and the smaller of `|A|` and `|B|` in place of `|A|` and `|B|`.
-/

public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

private lemma sum_min_add_le {d k n : ℕ} (hkn : k + 2 ≤ n) :
    ∑ t ∈ Icc 1 k, min d (n - 1 - t) + (k + 1) ≤ ∑ t ∈ Icc 1 (k + 1), min (d + 1) (n - t) := by
  have h : ∑ t ∈ Icc 1 k, (min d (n - 1 - t) + 1) ≤ ∑ t ∈ Icc 1 k, min (d + 1) (n - t) := by
    apply sum_le_sum
    grind
  rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul] at h
  rw [sum_Icc_succ_top (by grind)]
  grind

private lemma two_mul_mul_succ_le {k d n : ℕ} (hn : k + 1 ≤ n) :
    2 * (d * (k + 1)) ≤ 2 * ∑ t ∈ Icc 1 k, min d (n - t) + d * (d + 1) := by
  induction k generalizing d n with
  | zero => grind [Nat.le_mul_self d]
  | succ k ih =>
    obtain _ | d := d
    · simp
    · grind [ih (d := d) (n := n - 1) (by grind), sum_min_add_le (d := d) hn]

/-- For `1 ≤ m ≤ n`, twice the sum `∑ t ∈ {1, …, m - 1}, min d (n - t)` is at least
`2 * d * m - d * (d + 1)`. -/
lemma two_mul_mul_le_two_mul_sum_min_add (d : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    2 * (d * m) ≤ 2 * ∑ t ∈ Icc 1 (m - 1), min d (n - t) + d * (d + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.2 hm
  exact two_mul_mul_succ_le hmn

variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}

/-- The closed form of Ruzsa's bound, multiplied by two: `2 * (|A| + d * |B|)` is at most
`2 * |A + B| + d * (d + 1)`. -/
lemma two_mul_card_add_mul_card_le (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) : 2 * (#A + d * #B) ≤ 2 * #(A + B) + d * (d + 1) := by
  grind [card_add_sum_min_le_card_add_of_le hB hBA hd,
    two_mul_mul_le_two_mul_sum_min_add d hB.card_pos hBA]

/-- **The asymmetric form of Freiman's lemma.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty,
`|B| ≤ |A|` and `A + B` has affine dimension at least `d`, then
`|A| + d * |B| ≤ |A + B| + d * (d + 1) / 2`. -/
theorem card_add_mul_card_le_card_add_add (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 := by
  grind [two_mul_card_add_mul_card_le hB hBA hd]

/-- The asymmetric form of Freiman's lemma, with the affine dimension of `A + B` written as the
dimension of the span of `(A + B) - (A + B)`. -/
theorem card_add_mul_card_le_card_add_add_of_le_finrank_span_sub (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ)))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 :=
  card_add_mul_card_le_card_add_add hB hBA
    (hd.trans_eq (affineDim_eq_finrank_span_sub _).symm)

/-- The asymmetric form of Freiman's lemma in `ℝ`: `|A| + d * |B| - d * (d + 1) / 2 ≤ |A + B|`. -/
lemma card_add_mul_card_sub_le_card_add (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) :
    (#A : ℝ) + d * #B - d * (d + 1) / 2 ≤ #(A + B) := by
  have h : (2 * (#A + d * #B) : ℝ) ≤ 2 * #(A + B) + d * (d + 1) :=
    mod_cast two_mul_card_add_mul_card_le hB hBA hd
  linarith

/-- The asymmetric form of Freiman's lemma without an assumption on which set is larger. -/
lemma max_card_add_mul_min_card_le_card_add_add (hA : A.Nonempty) (hB : B.Nonempty)
    (hd : d ≤ (A + B).affineDim) :
    max #A #B + d * min #A #B ≤ #(A + B) + d * (d + 1) / 2 := by
  rcases le_total #B #A with h | h
  · rw [max_eq_left h, min_eq_right h]
    exact card_add_mul_card_le_card_add_add hB h hd
  · rw [max_eq_right h, min_eq_left h, add_comm A B]
    exact card_add_mul_card_le_card_add_add hA h (add_comm A B ▸ hd)

end SumOfSetsInSeveralDimensions
