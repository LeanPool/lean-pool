/-
Copyright (c) 2026 Yujie Sun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yujie Sun, Claude Opus 5.5 (AI)
-/
module

public import LeanPool.RowlandPrimes.Basic
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Rowland's prime-generating sequence

Rowland's sequence (OEIS A106108) is `a 1 = 7` and `a n = a (n - 1) + gcd n (a (n - 1))` for
`n ≥ 2`. Its increments `d n = a n - a (n - 1)` are `1` or prime (Rowland 2008). The definitions
`RowlandPrimes.rowlandSeq` and `RowlandPrimes.rowlandDiff` and the statement of
`RowlandPrimes.rowland_diff_eq_one_or_prime` are copied verbatim (apart from the namespace, which
is `RowlandSequence` there) from [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f9b3868d5ca994a7bf95039bcec05338c0c21e2f/FormalConjectures/Wikipedia/RowlandSequence.lean), where the theorem is stated without a proof.

Copyright 2026 The Formal Conjectures Authors.

The sequence `rowlandSeqFrom s` has the same recurrence with an arbitrary first term `s`; it is
used to show that the first term matters: with `a 1 = 532` the increment at `n = 18` is `9`.

## Main results

* `RowlandPrimes.rowland_diff_eq_one_or_prime`: Rowland's theorem, as stated in
  Formal Conjectures.
* `RowlandPrimes.rowlandDiff_ne_two`: no increment equals `2`.
* `RowlandPrimes.exists_prime_rowlandDiff_ge`: prime increments occur arbitrarily late.
* `RowlandPrimes.rowlandSeq_eq`: between consecutive checkpoints `N ≤ n < next N`,
  `rowlandSeq n = n + 2 * N`.
* `RowlandPrimes.rowlandSeqFrom_532_composite`: with first term `532`, the increment at `18`
  is the composite number `9`.
-/

@[expose] public section

namespace RowlandPrimes



/-- Rowland's sequence (`OEIS A106108`), starting at $a(1) = 7$ with recurrence
$a(n) = a(n - 1) + \gcd(n, a(n - 1))$ for $n \ge 2$ (and $a(0) = 0$). -/
def rowlandSeq : ℕ → ℕ
  | 0 => 0
  | 1 => 7
  | n + 2 =>
    let prev := rowlandSeq (n + 1)
    prev + Nat.gcd (n + 2) prev

/-- Step increment $d(n) = a(n) - a(n - 1)$ of `rowlandSeq` (meaningful for $n \ge 2$; shifted by
one from `OEIS A132199`, where `A132199(n) = rowlandDiff (n + 1)`). -/
def rowlandDiff (n : ℕ) : ℕ :=
  rowlandSeq n - rowlandSeq (n - 1)

/-- Rowland's recurrence with an arbitrary first term `s = a 1` (and `a 0 = 0`). -/
def rowlandSeqFrom (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => s
  | n + 2 => rowlandSeqFrom s (n + 1) + Nat.gcd (n + 2) (rowlandSeqFrom s (n + 1))

theorem rowlandSeqFrom_seven : rowlandSeqFrom 7 = rowlandSeq := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      simp only [rowlandSeqFrom, rowlandSeq, ih (n + 1) (by omega)]

/-- Every `rowlandSeqFrom s` satisfies Rowland's recurrence from index `1` on. -/
theorem satisfiesRecurrence_rowlandSeqFrom (s : ℕ) :
    SatisfiesRecurrence (rowlandSeqFrom s) 1 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem satisfiesRecurrence_rowlandSeq : SatisfiesRecurrence rowlandSeq 1 := by
  rw [← rowlandSeqFrom_seven]
  exact satisfiesRecurrence_rowlandSeqFrom 7

/-- `6` is a checkpoint of Rowland's sequence: `a 6 = 18`. -/
theorem isCheckpoint_six : IsCheckpoint rowlandSeq 6 :=
  ⟨by omega, by decide⟩

theorem rowlandDiff_eq (n : ℕ) : rowlandDiff (n + 1) = rowlandSeq (n + 1) - rowlandSeq n := rfl

/-- The increments `d 2, …, d 6` are `1, 1, 1, 5, 3`. -/
theorem rowlandDiff_two_to_six :
    rowlandDiff 2 = 1 ∧ rowlandDiff 3 = 1 ∧ rowlandDiff 4 = 1 ∧ rowlandDiff 5 = 5 ∧
      rowlandDiff 6 = 3 := by
  decide

/-- Rowland's theorem (2008): for every $n \ge 2$, the step $d(n) = a(n) - a(n - 1)$ equals
$1$ or is prime. -/
theorem rowland_diff_eq_one_or_prime {n : ℕ} (hn : 2 ≤ n) :
    rowlandDiff n = 1 ∨ (rowlandDiff n).Prime := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [rowlandDiff_eq]
  by_cases hm : 6 ≤ m
  · exact increment_eq_one_or_prime satisfiesRecurrence_rowlandSeq (by omega)
      isCheckpoint_six hm
  · have h := rowlandDiff_two_to_six
    rw [rowlandDiff_eq, rowlandDiff_eq, rowlandDiff_eq, rowlandDiff_eq, rowlandDiff_eq] at h
    obtain ⟨h2, h3, h4, h5, h6⟩ := h
    obtain rfl | rfl | rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    · exact Or.inl h2
    · exact Or.inl h3
    · exact Or.inl h4
    · exact Or.inr (h5 ▸ by decide)
    · exact Or.inr (h6 ▸ by decide)

/-- No increment of Rowland's sequence equals `2` (for `n ≥ 2`). -/
theorem rowlandDiff_ne_two {n : ℕ} (hn : 2 ≤ n) : rowlandDiff n ≠ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [rowlandDiff_eq]
  by_cases hm : 6 ≤ m
  · exact increment_ne_two satisfiesRecurrence_rowlandSeq (by omega) isCheckpoint_six hm
  · have h := rowlandDiff_two_to_six
    rw [rowlandDiff_eq, rowlandDiff_eq, rowlandDiff_eq, rowlandDiff_eq, rowlandDiff_eq] at h
    obtain ⟨h2, h3, h4, h5, h6⟩ := h
    obtain rfl | rfl | rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    all_goals omega

/-- Prime increments of Rowland's sequence occur arbitrarily late: for every `m` there is
`n ≥ m` with `rowlandDiff n` prime. -/
theorem exists_prime_rowlandDiff_ge (m : ℕ) : ∃ n, m ≤ n ∧ (rowlandDiff n).Prime := by
  obtain ⟨n, hn, hp⟩ :=
    exists_prime_increment_ge satisfiesRecurrence_rowlandSeq (by omega) isCheckpoint_six m
  exact ⟨n + 1, by omega, by rw [rowlandDiff_eq]; exact hp⟩

/-- The set of `n` with `rowlandDiff n` prime is infinite. -/
theorem infinite_setOf_prime_rowlandDiff : {n | (rowlandDiff n).Prime}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨b, hb⟩ => ?_
  obtain ⟨n, hn, hp⟩ := exists_prime_rowlandDiff_ge (b + 1)
  have := hb hp
  omega

/-- Every iterate of `next` starting at `6` is a checkpoint of Rowland's sequence. -/
theorem isCheckpoint_iterate (k : ℕ) : IsCheckpoint rowlandSeq (next^[k] 6) :=
  (isCheckpoint_iterate_next satisfiesRecurrence_rowlandSeq (by omega) isCheckpoint_six k).2

/-- Closed form of Rowland's sequence between consecutive checkpoints: if `N = next^[k] 6` and
`N ≤ n < next N`, then `rowlandSeq n = n + 2 * N`. -/
theorem rowlandSeq_eq (k : ℕ) {n : ℕ} (h₁ : next^[k] 6 ≤ n) (h₂ : n < next (next^[k] 6)) :
    rowlandSeq n = n + 2 * next^[k] 6 := by
  obtain ⟨h₀, hc⟩ :=
    isCheckpoint_iterate_next satisfiesRecurrence_rowlandSeq (by omega) isCheckpoint_six k
  exact eq_add_two_mul_of_le_of_lt satisfiesRecurrence_rowlandSeq h₀ hc h₁ h₂

/-- The first term matters: starting from `a 1 = 532`, the increment at `n = 18` is
`a 18 - a 17 = 9`, which is not prime. -/
theorem rowlandSeqFrom_532_composite :
    rowlandSeqFrom 532 18 - rowlandSeqFrom 532 17 = 9 ∧
      ¬ (rowlandSeqFrom 532 18 - rowlandSeqFrom 532 17).Prime := by
  have h : rowlandSeqFrom 532 18 - rowlandSeqFrom 532 17 = 9 := by decide
  exact ⟨h, by rw [h]; decide⟩

end RowlandPrimes
