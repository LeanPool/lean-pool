/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.SophieGermainArchives.Algebra.BigOperators.Naf4073PowerSums
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

/-!
# NAF 4073: Lagrange's formula is the only one of its kind

Adapted from `Germain/NumberTheory/Naf4073Gersonides.lean` of
https://github.com/Commutator-IO/GermainArchivesProofs
at commit `a628a4f` (Apache-2.0, same author); the same proofs are under CC0 in
https://github.com/Commutator-IO/germain-project.

If `S_p = T_n^q` for every `n`, then `(p, q) = (1, 1)` or `(3, 2)`: already `n = 2` gives
`2^p + 1 = 3^q`, whose only solutions are those, by Levi ben Gershon's theorem (1343).

## Main results

* `gersonides`: `2^p + 1 = 3^q`, `p, q ≥ 1`, only for `(1, 1)` and `(3, 2)`.
* `lagrange_unique`.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Naf4073

open Finset

/-- Levi ben Gershon (1343): `2^p + 1 = 3^q` with `p, q ≥ 1` only for `(1, 1)` and `(3, 2)`. -/
theorem gersonides (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : 2 ^ p + 1 = 3 ^ q) :
    (p = 1 ∧ q = 1) ∨ (p = 3 ∧ q = 2) := by
  obtain rfl | hp2 : p = 1 ∨ 2 ≤ p := by omega
  · exact .inl ⟨rfl, (Nat.pow_eq_self_iff (by norm_num : 1 < 3)).1 (by simpa using h.symm)⟩
  have h4 : 4 ∣ 2 ^ p := by simpa using Nat.pow_dvd_pow 2 hp2
  -- `3^q ≡ 1 mod 4`, so `q = 2r`, and `3^r + 1` is a power of `2` dividing `2^p`
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' q
  swap
  · have : 3 ^ (2 * r + 1) % 4 = 3 := by simp [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    omega
  have hfac : 2 ^ p = (3 ^ r - 1) * (3 ^ r + 1) := by
    have := Nat.one_le_pow r 3 (by norm_num)
    rw [pow_mul'] at h
    zify [this] at h ⊢
    linear_combination h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hfac.symm)
  -- `3^r + 1 ≡ 2, 4 mod 8`, so `3^r + 1 = 4`
  have h8 : 3 ^ r % 8 = 1 ∨ 3 ^ r % 8 = 3 := by
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r <;>
      simp [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  have hr : 3 ≤ 3 ^ r := Nat.le_self_pow (by omega) 3
  obtain hj3 | hj3 : j ≤ 2 ∨ 3 ≤ j := by omega
  · interval_cases j <;> norm_num at hj
    all_goals try omega
    obtain rfl : r = 1 := (Nat.pow_eq_self_iff (by norm_num)).1 hj
    exact .inr ⟨(Nat.pow_right_inj (by norm_num : 1 < 2)).1 (by simpa using hfac), rfl⟩
  · have : 8 ∣ 2 ^ j := by simpa using Nat.pow_dvd_pow 2 hj3
    omega

/-- If `S_p = T^q` for every `n`, with `p, q ≥ 1`, then `(p, q) = (1, 1)` or `(3, 2)`:
`n = 2` gives `1 + 2^p = 3^q`. Both cases occur (`S_one`, `S_three`). -/
theorem lagrange_unique (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : ∀ n, S p n = T n ^ q) :
    (p = 1 ∧ q = 1) ∨ (p = 3 ∧ q = 2) := by
  have hS : S p 2 = 2 ^ p + 1 := by
    simp [S, sum_range_succ, zero_pow (by omega : p ≠ 0)]
    ring
  exact gersonides p q hp hq (by rw [← hS, h 2]; rfl)

end LeanPool.SophieGermainArchives.Naf4073
