/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Real.OfDigits

import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Rational numbers have eventually periodic digits

For a base `b > 1`, a nonnegative real number is rational if and only if the sequence of its
digits in base `b` (as given by `Real.digits`) is eventually periodic.

## Main statements

* `Nat.mul_div_mod_eq_mod_mul_div`: `a * b / n % b = a % n * b / n`.
* `Real.digits_fract`: the digits of `x ≥ 0` only depend on its fractional part.
* `Real.digits_ratCast_eventually_periodic`: the digits of a nonnegative rational are eventually
  periodic.
* `Real.exists_ratCast_eq_ofDigits_of_eventually_periodic`: an eventually periodic sequence of
  digits represents a rational number.
* `Real.exists_ratCast_eq_iff_digits_eventually_periodic`: a nonnegative real number is rational
  if and only if its digits are eventually periodic.
-/

public section

theorem Nat.mul_div_mod_eq_mod_mul_div (a b n : ℕ) : a * b / n % b = a % n * b / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  conv =>
    lhs
    rw [← Nat.mod_add_div a n, Nat.add_mul, Nat.mul_assoc, Nat.add_mul_div_left _ _ hn,
      Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt a hn) hb))

namespace Real

theorem digits_fract {b : ℕ} [NeZero b] {x : ℝ} (hx : 0 ≤ x) :
    digits (Int.fract x) b = digits x b := by
  ext i
  simp only [digits, Fin.val_ofNat]
  conv_rhs => rw [← Int.fract_add_floor x, ← natCast_floor_eq_intCast_floor hx]
  rw [add_mul, ← Nat.cast_pow, ← Nat.cast_mul,
    Nat.floor_add_natCast (mul_nonneg (Int.fract_nonneg x) (Nat.cast_nonneg _)),
    pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]

theorem val_digits_natCast_div {b : ℕ} [NeZero b] (r s n : ℕ) :
    (digits ((r : ℝ) / s) b n : ℕ) = r * b ^ n % s * b / s := by
  rw [digits, Fin.val_ofNat, ← Nat.mul_div_mod_eq_mod_mul_div]
  congr 1
  rw [div_mul_eq_mul_div, pow_succ, ← mul_assoc]
  exact_mod_cast Nat.floor_div_eq_div (K := ℝ) (r * b ^ n * b) s

private lemma exists_periodic_mod_pow (r s b : ℕ) (hs : 0 < s) :
    ∃ N c, 0 < c ∧ Function.Periodic (fun d ↦ r * b ^ (N + d) % s) c := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ (⟨r * b ^ n % s, Nat.mod_lt _ hs⟩ : Fin s))
  simp only [Fin.mk.injEq] at h
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm h.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
  refine ⟨i, j - i, by lia, fun d ↦ ?_⟩
  dsimp only
  rw [show i + (d + (j - i)) = j + d by lia, pow_add, ← mul_assoc, Nat.mul_mod, ← h,
    ← Nat.mul_mod, mul_assoc, ← pow_add]

/-- The digits of a nonnegative rational number are eventually periodic. -/
theorem digits_ratCast_eventually_periodic {b : ℕ} [NeZero b] {q : ℚ} (hq : 0 ≤ q) :
    ∃ N c, 0 < c ∧ Function.Periodic (fun d ↦ digits (q : ℝ) b (N + d)) c := by
  have hx : (q : ℝ) = (q.num.toNat : ℝ) / q.den := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)).symm
  obtain ⟨N, c, hc, h⟩ := exists_periodic_mod_pow q.num.toNat q.den b q.den_pos
  refine ⟨N, c, hc, fun d ↦ Fin.ext ?_⟩
  dsimp only
  rw [hx, val_digits_natCast_div, val_digits_natCast_div]
  exact congrArg (· * b / q.den) (h d)

private lemma exists_ratCast_eq_sum_ofDigitsTerm {b : ℕ} (a : ℕ → Fin b) (n : ℕ) :
    ∃ q : ℚ, (q : ℝ) = ∑ i ∈ Finset.range n, ofDigitsTerm a i :=
  ⟨∑ i ∈ Finset.range n, ((a i : ℕ) : ℚ) * ((b : ℚ) ^ (i + 1))⁻¹, by simp [ofDigitsTerm]⟩

/-- An eventually periodic sequence of digits in base `b > 1` represents a rational number. -/
theorem exists_ratCast_eq_ofDigits_of_eventually_periodic {b : ℕ} (hb : 1 < b)
    {a : ℕ → Fin b} {N c : ℕ} (hc : 0 < c) (h : Function.Periodic (fun d ↦ a (N + d)) c) :
    ∃ q : ℚ, (q : ℝ) = ofDigits a := by
  set e : ℕ → Fin b := fun i ↦ a (i + N) with he_def
  have he : (fun i ↦ e (i + c)) = e := by
    ext1 i
    simp only [he_def]
    rw [add_comm (i + c) N, add_comm i N]
    exact h i
  have ht : ((b : ℝ) ^ c)⁻¹ ≠ 1 :=
    (inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by exact_mod_cast hb) hc.ne')).ne
  have key := ofDigits_eq_sum_add_ofDigits e c
  rw [he] at key
  obtain ⟨q₁, hq₁⟩ := exists_ratCast_eq_sum_ofDigitsTerm a N
  obtain ⟨q₂, hq₂⟩ := exists_ratCast_eq_sum_ofDigitsTerm e c
  have he' : ofDigits e = q₂ / (1 - ((b : ℝ) ^ c)⁻¹) := by
    rw [eq_div_iff (sub_ne_zero.2 ht.symm), hq₂, eq_sub_of_add_eq key.symm]
    ring
  refine ⟨q₁ + ((b : ℚ) ^ N)⁻¹ * (q₂ / (1 - ((b : ℚ) ^ c)⁻¹)), ?_⟩
  rw [ofDigits_eq_sum_add_ofDigits a N, ← he_def, he', ← hq₁]
  push_cast
  ring

/-- A nonnegative real number is rational if and only if its digits in base `b` are eventually
periodic. -/
theorem exists_ratCast_eq_iff_digits_eventually_periodic {b : ℕ} [NeZero b] (hb : 1 < b)
    {x : ℝ} (hx : 0 ≤ x) :
    (∃ q : ℚ, (q : ℝ) = x) ↔
      ∃ N c, 0 < c ∧ Function.Periodic (fun d ↦ digits x b (N + d)) c := by
  constructor
  · rintro ⟨q, rfl⟩
    exact digits_ratCast_eventually_periodic (mod_cast hx)
  · rintro ⟨N, c, hc, h⟩
    rw [← digits_fract hx] at h
    obtain ⟨q, hq⟩ := exists_ratCast_eq_ofDigits_of_eventually_periodic hb hc h
    rw [ofDigits_digits hb ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩] at hq
    exact ⟨q + ⌊x⌋, by push_cast; rw [hq, Int.fract_add_floor]⟩

end Real
