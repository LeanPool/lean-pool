/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.SophieGermainArchives.NumberTheory.Naf4073Note
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Ring

/-!
# NAF 4073: triangular numbers of products, powers and steps

Adapted from `Germain/NumberTheory/Naf4073Triangular.lean` of
https://github.com/Commutator-IO/GermainArchivesProofs
at commit `a628a4f` (Apache-2.0, same author); the same proofs are under CC0 in
https://github.com/Commutator-IO/germain-project.

The general statements of the second part of the short article on the note of NAF 4073
(`docs/naf-4073/article.tex` of germain-project), which extend the computation on the archive
leaf of uncertain authorship: expand `((n² ± n)/2)²`, then compare the difference and the sum.

## Main results

* `T_mul`: `T (m n) = T m T n + T (m − 1) T (n − 1)`; the note is `m = n`.
* `T_pow_split`, `T_pow_even`, `T_pow_step`: the triangular number of a power of `n`.
* `T_sq_sub_T_sq`, `T_sq_sub_T_sq_closed`:
  `T (b²) − T (a²) = a³ + 2(a+1)³ + ⋯ + 2(b−1)³ + b³ = (b² − a²)(a² + b² + 1)/2`.
* `T_pow_sub`, `T_pow_add`: `T_{n+1}^k ∓ T_n^k = ((n+1)/2)^k ((n+2)^k ∓ n^k)`;
  `T_four_sub`: `k = 4` is Germain's difference times the note.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Naf4073

open Finset

/-- `T k = k(k + 1)/2`, in `ℚ`. -/
lemma T_cast (k : ℕ) : (T k : ℚ) = k * (k + 1) / 2 := by
  rw [eq_div_iff two_ne_zero]
  exact_mod_cast (mul_comm _ _).trans (two_mul_T k)

/-- The difference of two triangular numbers. -/
lemma T_sub (a b : ℕ) : (T a : ℚ) - T b = ((a : ℚ) - b) * (a + b + 1) / 2 := by
  rw [T_cast, T_cast]
  ring

/-! ## The triangular number of a product -/

/-- `T (m n) = T m T n + T (m − 1) T (n − 1)`; the note of NAF 4073 is `m = n`. -/
theorem T_mul (m n : ℕ) : T (m * n) = T m * T n + T (m - 1) * T (n - 1) := by
  rcases m with _ | a
  · simp [T]
  rcases n with _ | b
  · simp [T]
  qify
  simp only [Nat.add_sub_cancel, T_cast]
  push_cast
  ring

/-! ## The triangular number of a power of `n` -/

/-- `T (n^k) = T (n^j) T (n^(k−j)) + T (n^j − 1) T (n^(k−j) − 1)` for `j ≤ k`. -/
theorem T_pow_split (n k j : ℕ) (hj : j ≤ k) :
    T (n ^ k) = T (n ^ j) * T (n ^ (k - j)) + T (n ^ j - 1) * T (n ^ (k - j) - 1) := by
  rw [← T_mul, ← pow_add, Nat.add_sub_cancel' hj]

/-- An even power: `T (n^(2j)) = T (n^j)² + T (n^j − 1)²`. -/
theorem T_pow_even (n j : ℕ) : T (n ^ (2 * j)) = T (n ^ j) ^ 2 + T (n ^ j - 1) ^ 2 := by
  rw [show 2 * j = j + j by ring, pow_add, T_mul, sq, sq]

/-- The step between consecutive `k`-th powers:
`T ((n+1)^k) − T (n^k) = ((n+1)^k − n^k)((n+1)^k + n^k + 1)/2`. -/
theorem T_pow_step (n k : ℕ) :
    (T ((n + 1) ^ k) : ℚ) - T (n ^ k)
      = (((n : ℚ) + 1) ^ k - (n : ℚ) ^ k) * (((n : ℚ) + 1) ^ k + (n : ℚ) ^ k + 1) / 2 := by
  rw [T_sub]
  push_cast
  ring

/-! ## The steps of `T (n²)` -/

/-- `T ((a+1)²) = T (a²) + a³ + (a+1)³`, for every `a` (`square_step` starts at `a = 1`). -/
lemma step_sq (a : ℕ) : T ((a + 1) ^ 2) = T (a ^ 2) + a ^ 3 + (a + 1) ^ 3 := by
  qify
  simp only [T_cast]
  push_cast
  ring

/-- `T (b²) − T (a²) = a³ + 2(a+1)³ + ⋯ + 2(b−1)³ + b³`, with `b = a + d + 1`. -/
theorem T_sq_sub_T_sq (a d : ℕ) :
    T ((a + d + 1) ^ 2)
      = T (a ^ 2) + a ^ 3 + 2 * ∑ i ∈ Ico (a + 1) (a + d + 1), i ^ 3 + (a + d + 1) ^ 3 := by
  induction d with
  | zero => simpa using step_sq a
  | succ d ih =>
    rw [show a + (d + 1) + 1 = (a + d + 1) + 1 by ring, step_sq, ih,
      sum_Ico_succ_top (by omega : a + 1 ≤ a + d + 1)]
    ring

/-- The closed form: `2 (T (b²) − T (a²)) = (b² − a²)(a² + b² + 1)`. -/
theorem T_sq_sub_T_sq_closed (a b : ℕ) :
    2 * ((T (b ^ 2) : ℚ) - T (a ^ 2))
      = ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2 + 1) := by
  rw [T_sub]
  push_cast
  ring

/-! ## Differences and sums of powers of consecutive triangular numbers -/

lemma T_succ_cast (n : ℕ) : (T (n + 1) : ℚ) = ((n + 1) / 2) * (n + 2) := by
  rw [T_cast]; push_cast; ring

lemma T_cast' (n : ℕ) : (T n : ℚ) = ((n + 1) / 2) * n := by
  rw [T_cast]; ring

/-- `T_{n+1}^k − T_n^k = ((n+1)/2)^k ((n+2)^k − n^k)`. -/
theorem T_pow_sub (n k : ℕ) :
    (T (n + 1) : ℚ) ^ k - (T n : ℚ) ^ k
      = (((n : ℚ) + 1) / 2) ^ k * (((n : ℚ) + 2) ^ k - (n : ℚ) ^ k) := by
  rw [T_succ_cast, T_cast', mul_pow, mul_pow]
  ring

/-- `T_{n+1}^k + T_n^k = ((n+1)/2)^k ((n+2)^k + n^k)`: `k = 1` is `T_n + T_{n+1} = (n+1)²`,
`k = 2` is the note. -/
theorem T_pow_add (n k : ℕ) :
    (T (n + 1) : ℚ) ^ k + (T n : ℚ) ^ k
      = (((n : ℚ) + 1) / 2) ^ k * (((n : ℚ) + 2) ^ k + (n : ℚ) ^ k) := by
  rw [T_succ_cast, T_cast', mul_pow, mul_pow]
  ring

/-- `k = 4`: Germain's difference times the note, `T_{n+1}⁴ − T_n⁴ = (n+1)³ T ((n+1)²)`. -/
theorem T_four_sub (n : ℕ) :
    T (n + 1) ^ 4 - T n ^ 4 = (n + 1) ^ 3 * T ((n + 1) ^ 2) := by
  apply Nat.sub_eq_of_eq_add
  rw [← triangular_of_square, show T (n + 1) ^ 4 = (T (n + 1) ^ 2) ^ 2 by ring, sq_T_succ]
  ring

end LeanPool.SophieGermainArchives.Naf4073
