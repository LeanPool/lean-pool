/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Zify

/-!
# NAF 4073, view 42: the triangular number of a square

The modernised reading `transcripts/naf-4073/naf-4073.modern.tex` of germain-project
(« La seule mathématique du volume : le triangulaire d'un carré ») reads the one line of
mathematics of the volume, on the address leaf of the unsigned letter of 13 March 1814
(view 42):
`((n² − n)/2)² + ((n² + n)/2)² = (n⁴ + n²)/2`, « le triangulaire d'un quarré est la somme des
quarrés des deux Triangulaires consécutifs », that is `T_{n−1}² + T_n² = T_{n²}` with
`T_k = k(k + 1)/2`. This is finding `naf-4073-triangular-note` of germain-project
(`src/content/findings.ts`), a codicological finding: the identity itself is classical.

* `leaf_identity`: the leaf's formula, over any field of characteristic `≠ 2`.
* `two_mul_T`, `T_eq_choose`: `2 T_k = k(k + 1)` and `T_k = C(k + 1, 2)`.
* `T_add_T`, `T_succ_sub_T`: the two triangular numbers sum to the square and differ by its
  root.
* `triangular_of_square`: `T_n² + T_{n+1}² = T_{(n+1)²}` in `ℕ`, for every `n` (the reading's
  `T_{n−1}² + T_n² = T_{n²}` with `n + 1` for `n`, which avoids truncated subtraction);
  `triangular_of_square_choose`: `C(n, 2)² + C(n + 1, 2)² = C(n² + 1, 2)`.
* `nicomachus`, `triangular_of_square_cubes`: `∑_{i ≤ n} i³ = T_n²`, hence
  `T_{n²} = 2 T_n² − n³` (stated as `T_{(n+1)²} + (n + 1)³ = 2 T_{n+1}²`).
* `sq_T_succ`, `square_step`: `T_{n+1}² = T_n² + (n + 1)³`, hence
  `T_{(n+2)²} = T_{(n+1)²} + (n + 1)³ + (n + 2)³`.
* `line_189`: the line `1 + 64 … 189` (re-read on 25 November 2026; first read `1 + 64 + 49`):
  `189 = 4³ + 5³ = T_25 − T_16`, and `189` is neither triangular nor a square.

Not formalised: anything about the hand or the date of the note.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Naf4073

open Finset

/-- The leaf's formula. -/
theorem leaf_identity {K : Type*} [Field K] [NeZero (2 : K)] (n : K) :
    ((n ^ 2 - n) / 2) ^ 2 + ((n ^ 2 + n) / 2) ^ 2 = (n ^ 4 + n ^ 2) / 2 := by
  field_simp
  ring

/-- The `k`-th triangular number `k(k + 1)/2`. -/
def T (k : ℕ) : ℕ := k * (k + 1) / 2

lemma two_mul_T (k : ℕ) : 2 * T k = k * (k + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

lemma T_eq_choose (k : ℕ) : T k = (k + 1).choose 2 := by
  rw [Nat.choose_two_right, T, Nat.add_sub_cancel, mul_comm]

/-- `T_n + T_{n+1} = (n + 1)²`: the two triangular numbers of the leaf sum to the square. -/
lemma T_add_T (n : ℕ) : T n + T (n + 1) = (n + 1) ^ 2 := by
  nlinarith [two_mul_T n, two_mul_T (n + 1)]

/-- `T_{n+1} = T_n + (n + 1)`: they differ by its root. -/
lemma T_succ_sub_T (n : ℕ) : T (n + 1) = T n + (n + 1) := by
  nlinarith [two_mul_T n, two_mul_T (n + 1)]

/-- **The note of NAF 4073**: `T_n² + T_{n+1}² = T_{(n+1)²}`, the triangular number of a
square is the sum of the squares of the two consecutive triangular numbers whose sum it is. -/
theorem triangular_of_square (n : ℕ) : T n ^ 2 + T (n + 1) ^ 2 = T ((n + 1) ^ 2) := by
  nlinarith [two_mul_T n, two_mul_T (n + 1), two_mul_T ((n + 1) ^ 2)]

/-- The binomial form: `C(n, 2)² + C(n + 1, 2)² = C(n² + 1, 2)`, for every `n ≥ 1`. -/
theorem triangular_of_square_choose (n : ℕ) (hn : 1 ≤ n) :
    n.choose 2 ^ 2 + (n + 1).choose 2 ^ 2 = (n ^ 2 + 1).choose 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← T_eq_choose, ← T_eq_choose, ← T_eq_choose]
  exact triangular_of_square m

/-- Nicomachus: `∑_{i ≤ n} i³ = T_n²`. -/
theorem nicomachus (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 3 = T n ^ 2 := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
    rw [sum_range_succ, ih]
    nlinarith [two_mul_T n, two_mul_T (n + 1)]

/-- **`T_{n²} = 2 T_n² − n³`**, twice the sum of the first `n` cubes less the last. -/
theorem triangular_of_square_cubes (n : ℕ) :
    T ((n + 1) ^ 2) + (n + 1) ^ 3 = 2 * T (n + 1) ^ 2 := by
  rw [← triangular_of_square]
  nlinarith [two_mul_T n, two_mul_T (n + 1)]

/-- `T_{n+1}² = T_n² + (n + 1)³`: Germain's difference. -/
lemma sq_T_succ (n : ℕ) : T (n + 1) ^ 2 = T n ^ 2 + (n + 1) ^ 3 := by
  nlinarith [two_mul_T n, two_mul_T (n + 1)]

/-- Consecutive terms of `T_{n²}` differ by the sum of two consecutive cubes. -/
theorem square_step (n : ℕ) :
    T ((n + 2) ^ 2) = T ((n + 1) ^ 2) + (n + 1) ^ 3 + (n + 2) ^ 3 := by
  rw [← triangular_of_square, ← triangular_of_square, sq_T_succ (n + 1), sq_T_succ]
  ring

/-- The line `1 + 64 … 189` of the leaf: `189 = 4³ + 5³ = T_25 − T_16`, the step of
`square_step` at `n = 3`; `189` itself is neither triangular nor a square. -/
theorem line_189 :
    189 = 4 ^ 3 + 5 ^ 3 ∧ T 25 = T 16 + 189 ∧ (∀ k, T k ≠ 189) ∧ (∀ m : ℕ, m ^ 2 ≠ 189) := by
  refine ⟨by norm_num, by norm_num [T], fun k hk => ?_, fun m hm => ?_⟩
  · have h := two_mul_T k
    rw [hk] at h
    have : k ≤ 19 := by nlinarith
    interval_cases k <;> omega
  · have : m ≤ 13 := by nlinarith
    interval_cases m <;> omega

end LeanPool.SophieGermainArchives.Naf4073
