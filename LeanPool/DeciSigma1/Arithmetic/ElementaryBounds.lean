/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Iterate
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Elementary bounds on natural numbers

Powers of two and their fixed-height iterates absorb polynomial factors, sums, and products.
The estimates use natural-number arithmetic and include zero arguments.

## Main declarations

- `exp2`, `iterate_exp2_mono`, `le_iterate_exp2`: iterated powers of two.
- `succ_pow_le_exp2_mul`, `double_exp2_pow_le`: polynomial absorption.
- `iterate_exp2_add_le`, `iterate_exp2_mul_le`: arithmetic at a fixed positive height.
- `quadratic_step_le_exp2`: a quadratic recurrence estimate.
-/

@[expose] public section


namespace DeciSigma1.Arithmetic

/-- The base-two exponential on natural numbers, iterated using `exp2^[h]`. -/
def exp2 (x : ℕ) : ℕ := 2 ^ x

/-- The base-two exponential is strictly increasing. -/
theorem exp2_strictMono : StrictMono exp2 := by
  intro a b h
  exact Nat.pow_lt_pow_right (by decide) h

/-- The base-two exponential is increasing. -/
theorem exp2_mono : Monotone exp2 := exp2_strictMono.monotone

/-- Every natural number is smaller than its base-two exponential. -/
theorem succ_le_exp2 (x : ℕ) : x + 1 ≤ exp2 x := Nat.lt_two_pow_self

/-- Every natural number is bounded by its base-two exponential. -/
theorem le_exp2 (x : ℕ) : x ≤ exp2 x := (Nat.le_succ x).trans (succ_le_exp2 x)

/-- Every fixed-height iterate is increasing in its argument. -/
theorem iterate_exp2_mono (h : ℕ) : Monotone (exp2^[h]) := exp2_mono.iterate h

/-- Iterating the base-two exponential increases the argument. -/
theorem le_iterate_exp2 (h x : ℕ) : x ≤ exp2^[h] x := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_exp2 _)

/-- Increasing the height increases an iterated exponential. -/
theorem iterate_exp2_mono_height (x : ℕ) : Monotone (fun h => exp2^[h] x) :=
  exp2_mono.monotone_iterate_of_le_map (le_exp2 x)

/-- Multiplication of powers of two adds their exponents. -/
theorem exp2_add (a b : ℕ) : exp2 (a + b) = exp2 a * exp2 b := pow_add _ _ _

/-- A power of a power of two multiplies the exponent. -/
theorem exp2_mul (a b : ℕ) : exp2 (a * b) = exp2 a ^ b := pow_mul _ _ _

/-- A sum of two powers of two is absorbed with one additional exponent unit. -/
theorem exp2_add_le (a b : ℕ) : exp2 a + exp2 b ≤ exp2 (a + b + 1) := by
  have ha := exp2_mono (Nat.le_add_right a b)
  have hb := exp2_mono (Nat.le_add_left b a)
  rw [exp2_add (a + b) 1]
  change exp2 a + exp2 b ≤ exp2 (a + b) * 2
  omega

/-- A polynomial in `x + 1` is bounded by a single exponential. -/
theorem succ_pow_le_exp2_mul (x d : ℕ) : (x + 1) ^ d ≤ exp2 (d * x) := by
  calc
    _ ≤ exp2 x ^ d := Nat.pow_le_pow_left (succ_le_exp2 x) d
    _ = exp2 (d * x) := by rw [← exp2_mul, Nat.mul_comm]

/-- A power of a double exponential is absorbed in its inner argument. -/
theorem double_exp2_pow_le (a c : ℕ) : (exp2 (exp2 a)) ^ c ≤
    exp2 (exp2 (a + c)) := by
  rw [← exp2_mul, exp2_add a c]
  exact exp2_mono (Nat.mul_le_mul_left _ (le_exp2 c))

/-- Increasing the argument by one at least doubles a positive-height iterate. -/
theorem two_mul_iterate_exp2_le (h x : ℕ) (hh : 1 ≤ h) :
    2 * exp2^[h] x ≤ exp2^[h] (x + 1) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  have hi := (exp2_strictMono.iterate h) (Nat.lt_succ_self x)
  calc
    2 * exp2 (exp2^[h] x) = exp2 (exp2^[h] x + 1) := by
      rw [exp2_add]; simp [exp2, Nat.mul_comm]
    _ ≤ exp2 (exp2^[h] (x + 1)) := exp2_mono hi

/-- Sums at a fixed positive height are absorbed by summing the arguments. -/
theorem iterate_exp2_add_le (h a b : ℕ) (hh : 1 ≤ h) :
    exp2^[h] a + exp2^[h] b ≤ exp2^[h] (a + b + 1) := by
  calc
    _ ≤ 2 * exp2^[h] (a + b) := by
      have ha := iterate_exp2_mono h (Nat.le_add_right a b)
      have hb := iterate_exp2_mono h (Nat.le_add_left b a)
      omega
    _ ≤ _ := two_mul_iterate_exp2_le h (a + b) hh

/-- Products at a fixed positive height are absorbed by summing the arguments. -/
theorem iterate_exp2_mul_le (h a b : ℕ) (hh : 1 ≤ h) :
    exp2^[h] a * exp2^[h] b ≤ exp2^[h] (a + b + 1) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_succ_apply', ← exp2_add]
  apply exp2_mono
  cases h with
  | zero => simp
  | succ h => exact iterate_exp2_add_le _ _ _ (by omega)

/-- A factorial is bounded by a single exponential with quadratic exponent. -/
theorem factorial_le_exp2_sq (n : ℕ) : n.factorial ≤ exp2 (n * n) := by
  calc
    _ ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ exp2 n ^ n := Nat.pow_le_pow_left (le_exp2 n) n
    _ = _ := (exp2_mul n n).symm

/-- A quadratic step with exponentially bounded coefficients has a linear exponent bound. -/
theorem quadratic_step_le_exp2 {t a e q L : ℕ}
    (ht : t ≤ exp2 L) (ha : a ≤ exp2 q) (he : e ≤ exp2 q) :
    t + (t * a) * ((t * a + 2) * e) ≤ exp2 (2 * L + 3 * q + 3) := by
  have hta : t * a ≤ exp2 (L + q) := by
    rw [exp2_add]; exact Nat.mul_le_mul ht ha
  have hplus : t * a + 2 ≤ exp2 (L + q + 2) :=
    (Nat.add_le_add hta (le_refl 2)).trans (exp2_add_le (L + q) 1)
  calc
    _ ≤ exp2 L + exp2 (L + q) * (exp2 (L + q + 2) * exp2 q) :=
      Nat.add_le_add ht (Nat.mul_le_mul hta (Nat.mul_le_mul hplus he))
    _ = exp2 L + exp2 (2 * L + 3 * q + 2) := by
      rw [← exp2_add, ← exp2_add]; congr 2; omega
    _ ≤ exp2 (2 * L + 3 * q + 2) + exp2 (2 * L + 3 * q + 2) :=
      Nat.add_le_add_right (exp2_mono (by omega)) _
    _ = _ := by
      rw [show 2 * L + 3 * q + 3 = (2 * L + 3 * q + 2) + 1 by omega,
        exp2_add (2 * L + 3 * q + 2) 1]
      change exp2 (2 * L + 3 * q + 2) + exp2 (2 * L + 3 * q + 2) =
        exp2 (2 * L + 3 * q + 2) * 2
      omega

end DeciSigma1.Arithmetic
