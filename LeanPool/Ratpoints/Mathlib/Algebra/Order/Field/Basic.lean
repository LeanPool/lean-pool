/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Nat.Cast.Field

/-!
# Quotients of integers in a field

Candidates for `Mathlib.Algebra.Order.Field.Basic`: in a linearly ordered field the quotient of
two integers is at most the numerator in absolute value (`abs_intCast_div_intCast_le_abs`), also
for the denominator `0`, by which the quotient is `0`; the field form of `Int.abs_ediv_le_abs`. An
integer `a` with `a / b` above or below `n / q` lies above the quotient of `b n` by `q` rounded up,
or below it rounded down (`Int.neg_ediv_neg_le_of_div_le`, `Int.le_ediv_of_div_le`). A fraction
keeps its value when numerator and denominator are divided by their greatest common divisor
(`intCast_ediv_gcd_div_natCast_div_gcd`), and the dyadic `m 2 ^ e` is the fraction of
`m 2 ^ max e 0` and `2 ^ max (-e) 0` (`intCast_mul_two_pow_div_two_pow`).

## Main statements

* `abs_intCast_div_intCast_le_abs`: `|x / z| ≤ |x|` for integers `x` and `z`, and
  `abs_intCast_div_natCast_le` the bound by `H` that follows from `|x| ≤ H`.
* `Int.le_ediv_of_div_le`, `Int.neg_ediv_neg_le_of_div_le`: the bounds of `a` from `a / b`.
-/

@[expose] public section

theorem abs_intCast_div_intCast_le_abs {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (x z : ℤ) : |(x : α) / z| ≤ |(x : α)| := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [abs_div, ← Int.cast_abs (a := z)]
  exact div_le_self (abs_nonneg _) (mod_cast Int.one_le_abs hz)

theorem abs_intCast_div_natCast_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : ℤ} {H : ℕ} (ha : |a| ≤ H) (b : ℕ) : |(a : α) / b| ≤ H := by
  have := abs_intCast_div_intCast_le_abs (α := α) a b
  rw [Int.cast_natCast, ← Int.cast_abs] at this
  exact this.trans (mod_cast ha)

/-- `a ≤ ⌊b n / q⌋` for an integer `a` with `a / b ≤ n / q`, the floor written as the integer
division `b n / q`; also for `q = 0`, by which both quotients are `0`. -/
theorem Int.le_ediv_of_div_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n a : ℤ} {q b : ℕ} (hb : 0 < b) (h : (a : K) / b ≤ n / q) : a ≤ b * n / (q : ℤ) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simpa [div_nonpos_iff, hb.ne'] using h
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hb) (Nat.cast_pos.mpr hq)] at h
  exact (Int.le_ediv_iff_mul_le (by lia)).mpr (by lia [(mod_cast h : a * q ≤ n * b)])

/-- `⌈b n / q⌉ ≤ a` for an integer `a` with `n / q ≤ a / b`, the ceiling written as
`-(-(b n) / q)` (`Int.le_ediv_of_div_le` for `-a` and `-n`). -/
theorem Int.neg_ediv_neg_le_of_div_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n a : ℤ} {q b : ℕ} (hb : 0 < b) (h : (n : K) / q ≤ a / b) :
    -(-(b * n) / (q : ℤ)) ≤ a := by
  have := Int.le_ediv_of_div_le (n := -n) (a := -a) hb
    (by push_cast; rw [neg_div, neg_div]; exact neg_le_neg h : ((-a : ℤ) : K) / b ≤ (-n : ℤ) / q)
  rw [mul_neg] at this
  lia

/-- Dividing the numerator `n` and the denominator `q` of a fraction by their greatest common
divisor does not change its value, also for `q = 0`. -/
theorem intCast_ediv_gcd_div_natCast_div_gcd {K : Type*} [DivisionRing K] [CharZero K] (n : ℤ)
    (q : ℕ) :
    ((n / (Nat.gcd n.natAbs q : ℤ) : ℤ) : K) / ((q / Nat.gcd n.natAbs q : ℕ) : K) = n / q := by
  rcases Nat.eq_zero_or_pos (Nat.gcd n.natAbs q) with h | h
  · obtain ⟨hn, rfl⟩ := Nat.gcd_eq_zero_iff.mp h
    simp [Int.natAbs_eq_zero.mp hn]
  have hg : (Nat.gcd n.natAbs q : K) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
  rw [Int.cast_div (Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)) (by rwa [Int.cast_natCast]),
    Nat.cast_div (Nat.gcd_dvd_right _ _) hg, Int.cast_natCast, div_div_div_cancel_right₀ hg]

theorem intCast_mul_two_pow_div_two_pow {K : Type*} [DivisionRing K] (m e : ℤ) :
    ((m * 2 ^ e.toNat : ℤ) : K) / ((2 ^ (-e).toNat : ℕ) : K) = m * 2 ^ e := by
  rcases le_or_gt 0 e with he | he
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he
    simp
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat he.le
    simp [zpow_neg, div_eq_mul_inv]

end
