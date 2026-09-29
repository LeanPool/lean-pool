/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Magnitude
public import Mathlib.Data.Nat.Log

/-!
# Integer Digits, Scaling, and Slices

These definitions are the effective integer layer used by radix-based rounding algorithms.  Signed
division and remainder use `Int.tdiv` and `Int.tmod`, matching Flocq's quotient and remainder toward
zero rather than Lean's Euclidean `/` and `%` operations.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Integer radix power, with the Flocq convention that negative powers are zero. -/
def intPower (β : Numerics.Radix) (e : ℤ) : ℤ :=
  if 0 ≤ e then Int.ofNat (β.base ^ e.toNat) else 0

/-- At nonnegative exponents, `intPower` is the ordinary natural radix power. -/
@[simp] theorem intPower_of_nonneg (β : Numerics.Radix) {e : ℤ} (he : 0 ≤ e) :
    intPower β e = Int.ofNat (β.base ^ e.toNat) := by
  simp [intPower, he]

/-- At negative exponents, the integer radix-power convention returns zero. -/
@[simp] theorem intPower_of_neg (β : Numerics.Radix) {e : ℤ} (he : e < 0) :
    intPower β e = 0 := by
  have hnot : ¬0 ≤ e := by linarith
  simp [intPower, hnot]

/-- The zeroth integer radix power is one. -/
theorem intPower_zero (β : Numerics.Radix) : intPower β 0 = 1 := by
  simp [intPower]

/-- The signed radix digit at position `k`. -/
def digit (β : Numerics.Radix) (n k : ℤ) : ℤ :=
  Int.tmod (Int.tdiv n (intPower β k)) (Int.ofNat β.base)

/-- Every radix digit of zero is zero. -/
@[simp] theorem digit_zero (β : Numerics.Radix) (k : ℤ) : digit β 0 k = 0 := by
  simp [digit]

/-- Signed digit extraction commutes with integer negation. -/
@[simp] theorem digit_neg (β : Numerics.Radix) (n k : ℤ) :
    digit β (-n) k = -digit β n k := by
  simp [digit]

/-- Integer digit positions below zero contain no digit. -/
theorem digit_of_neg_index (β : Numerics.Radix) (n : ℤ) {k : ℤ} (hk : k < 0) :
    digit β n k = 0 := by
  simp [digit, intPower_of_neg β hk]

/-- Every signed digit has absolute value strictly smaller than the radix. -/
theorem digit_abs_lt_base (β : Numerics.Radix) (n k : ℤ) :
    |digit β n k| < Int.ofNat β.base := by
  have hb : (0 : ℤ) < Int.ofNat β.base := by
    exact Int.natCast_pos.mpr (Nat.zero_lt_of_lt β.base_valid)
  have hlower := Int.lt_tmod_of_pos
    (Int.tdiv n (intPower β k)) hb
  have hupper := Int.tmod_lt_of_pos
    (Int.tdiv n (intPower β k)) hb
  rw [abs_lt]
  exact ⟨by simpa [digit] using hlower, by simpa [digit] using hupper⟩

/-- Shift an integer left for nonnegative `k`, and right with truncation for negative `k`. -/
def scale (β : Numerics.Radix) (n k : ℤ) : ℤ :=
  if 0 ≤ k then n * intPower β k else Int.tdiv n (intPower β (-k))

/-- A nonnegative scale multiplies by the corresponding radix power. -/
theorem scale_of_nonneg (β : Numerics.Radix) (n : ℤ) {k : ℤ} (hk : 0 ≤ k) :
    scale β n k = n * intPower β k := by
  simp [scale, hk]

/-- A negative scale divides toward zero by the corresponding positive radix power. -/
theorem scale_of_neg (β : Numerics.Radix) (n : ℤ) {k : ℤ} (hk : k < 0) :
    scale β n k = Int.tdiv n (intPower β (-k)) := by
  have hnot : ¬0 ≤ k := by linarith
  simp [scale, hnot]

/-- Scaling the zero value gives zero. -/
@[simp] theorem scale_zero_value (β : Numerics.Radix) (k : ℤ) : scale β 0 k = 0 := by
  simp [scale]

/-- A zero-place scale leaves the integer unchanged. -/
@[simp] theorem scale_zero_shift (β : Numerics.Radix) (n : ℤ) : scale β n 0 = n := by
  simp [scale]

/-- Radix scaling commutes with integer negation. -/
@[simp] theorem scale_neg (β : Numerics.Radix) (n k : ℤ) :
    scale β (-n) k = -scale β n k := by
  unfold scale
  split <;> simp

/-- Extract `width` radix digits beginning at `start`; negative widths produce zero. -/
def slice (β : Numerics.Radix) (n start width : ℤ) : ℤ :=
  if 0 ≤ width then
    Int.tmod (scale β n (-start)) (intPower β width)
  else 0

/-- Every radix slice of zero is zero. -/
@[simp] theorem slice_zero_value (β : Numerics.Radix) (start width : ℤ) :
    slice β 0 start width = 0 := by
  simp [slice]

/-- A negative-width radix slice is empty and therefore evaluates to zero. -/
theorem slice_of_neg_width (β : Numerics.Radix) (n start : ℤ) {width : ℤ}
    (hwidth : width < 0) : slice β n start width = 0 := by
  have hnot : ¬0 ≤ width := by linarith
  simp [slice, hnot]

/-- A nonnegative-width slice has absolute value below the corresponding radix power. -/
theorem slice_abs_lt_power (β : Numerics.Radix) (n start : ℤ) {width : ℤ}
    (hwidth : 0 ≤ width) :
    |slice β n start width| < intPower β width := by
  have hpow : (0 : ℤ) < intPower β width := by
    rw [intPower_of_nonneg β hwidth]
    exact Int.natCast_pos.mpr (pow_pos (Nat.zero_lt_of_lt β.base_valid) width.toNat)
  have hlower := Int.lt_tmod_of_pos (scale β n (-start)) hpow
  have hupper := Int.tmod_lt_of_pos (scale β n (-start)) hpow
  rw [abs_lt]
  exact ⟨by simpa [slice, hwidth] using hlower,
    by simpa [slice, hwidth] using hupper⟩

/-- Radix slicing commutes with integer negation. -/
@[simp] theorem slice_neg (β : Numerics.Radix) (n start width : ℤ) :
    slice β (-n) start width = -slice β n start width := by
  unfold slice
  split <;> simp

/-- Number of base-`β` digits in the absolute value of an integer. -/
def digits (β : Numerics.Radix) (n : ℤ) : ℕ :=
  if n = 0 then 0 else Nat.log β.base n.natAbs + 1

/-- Zero has no significant radix digits. -/
@[simp] theorem digits_zero (β : Numerics.Radix) : digits β 0 = 0 := by
  simp [digits]

/-- Radix digit count depends only on the integer's absolute value. -/
@[simp] theorem digits_neg (β : Numerics.Radix) (n : ℤ) :
    digits β (-n) = digits β n := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp [digits, hn]

/-- Every nonzero integer has a positive radix digit count. -/
theorem digits_pos {β : Numerics.Radix} {n : ℤ} (hn : n ≠ 0) :
    0 < digits β n := by
  simp [digits, hn]

/-- A nonzero integer lies between consecutive powers selected by its digit count. -/
theorem digits_bounds (β : Numerics.Radix) {n : ℤ} (hn : n ≠ 0) :
    β.base ^ (digits β n - 1) ≤ n.natAbs ∧
      n.natAbs < β.base ^ digits β n := by
  have habs : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hbase : 1 < β.base := lt_of_lt_of_le Nat.one_lt_two β.base_valid
  simp only [digits, ite_eq_right hn]
  constructor
  · simpa using Nat.pow_log_le_self β.base habs
  · simpa [Nat.pow_succ] using Nat.lt_pow_succ_log_self hbase n.natAbs

/-- The radix digit count of a positive integer is the magnitude of its real embedding. -/
theorem magnitude_intCast_of_pos (β : Numerics.Radix) {n : ℤ} (hn : 0 < n) :
    magnitude β (n : ℝ) = (digits β n : ℤ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [magnitude_eq_int_log_add_one β _ hnR.ne', abs_of_pos hnR]
  have hnabs : (n.natAbs : ℝ) = n := by
    rw [Nat.cast_natAbs, abs_of_pos hn]
  rw [← hnabs, Int.log_natCast]
  simp [digits, ne_of_gt hn]

/-- A positive integer is strictly below the radix power selected by its digit count. -/
theorem intCast_lt_bpow_digits (β : Numerics.Radix) {n : ℤ} (hn : 0 < n) :
    (n : ℝ) < bpow β (digits β n : ℤ) := by
  have h := abs_lt_bpow_magnitude β (n : ℝ) (by exact_mod_cast (ne_of_gt hn))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simpa [abs_of_pos hnR, magnitude_intCast_of_pos β hn] using h

/-- The successor of a positive integer does not exceed its next radix-power boundary. -/
theorem intCast_add_one_le_bpow_digits (β : Numerics.Radix) {n : ℤ} (hn : 0 < n) :
    ((n + 1 : ℤ) : ℝ) ≤ bpow β (digits β n : ℤ) := by
  have hb := (digits_bounds β (ne_of_gt hn)).2
  have hnabs : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn.le
  have hz : n + 1 ≤ (β.base ^ digits β n : ℕ) := by
    have hbZ : (n.natAbs : ℤ) < (β.base ^ digits β n : ℕ) := by
      exact_mod_cast hb
    rw [hnabs] at hbZ
    exact Int.add_one_le_iff.mpr hbZ
  rw [show (digits β n : ℤ) = ((digits β n : ℕ) : ℤ) by rfl,
    bpow, zpow_natCast]
  simpa [Numerics.Radix.toReal] using (show ((n + 1 : ℤ) : ℝ) ≤ β.base ^ digits β n by
    exact_mod_cast hz)

/-- The power bounds uniquely determine the digit count of a nonzero integer. -/
theorem digits_unique (β : Numerics.Radix) {n : ℤ} (hn : n ≠ 0) {d : ℕ} (hd : 0 < d)
    (hlower : β.base ^ (d - 1) ≤ n.natAbs)
    (hupper : n.natAbs < β.base ^ d) : digits β n = d := by
  have hlog : Nat.log β.base n.natAbs = d - 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow hlower (by simpa [Nat.sub_add_cancel hd] using hupper)
  simp [digits, hn, hlog, Nat.sub_add_cancel hd]

/-- Digit count is monotone with respect to integer absolute value away from zero. -/
theorem digits_mono_abs (β : Numerics.Radix) {n m : ℤ} (hn : n ≠ 0)
    (hnm : n.natAbs ≤ m.natAbs) : digits β n ≤ digits β m := by
  have hm : m ≠ 0 := by
    intro hm
    subst m
    simp only [Int.natAbs_zero] at hnm
    have hnabs : n.natAbs = 0 := Nat.eq_zero_of_le_zero hnm
    exact hn (Int.natAbs_eq_zero.mp hnabs)
  simp only [digits, ite_eq_right hn, ite_eq_right hm]
  exact Nat.add_le_add_right (Nat.log_mono_right hnm) 1

/-- A nonzero product uses at most the sum of the operand digit counts. -/
theorem digits_mul_le (β : Numerics.Radix) {n m : ℤ} (hn : n ≠ 0) (hm : m ≠ 0) :
    digits β (n * m) ≤ digits β n + digits β m := by
  have hnm : n * m ≠ 0 := mul_ne_zero hn hm
  have hnBounds := digits_bounds β hn
  have hmBounds := digits_bounds β hm
  have hprod : (n * m).natAbs < β.base ^ (digits β n + digits β m) := by
    rw [Int.natAbs_mul, pow_add]
    calc
      n.natAbs * m.natAbs < β.base ^ digits β n * m.natAbs :=
        Nat.mul_lt_mul_of_pos_right hnBounds.2 (Int.natAbs_pos.mpr hm)
      _ < β.base ^ digits β n * β.base ^ digits β m :=
        Nat.mul_lt_mul_of_pos_left hmBounds.2
          (pow_pos (Nat.zero_lt_of_lt β.base_valid) _)
  have hlog : Nat.log β.base (n * m).natAbs <
      digits β n + digits β m :=
    Nat.log_lt_of_lt_pow (Int.natAbs_ne_zero.mpr hnm) hprod
  simp only [digits, ite_eq_right hnm]
  exact Nat.add_one_le_iff.mpr hlog

/-- A positive radix power has one more digit than its exponent. -/
theorem digits_power (β : Numerics.Radix) (k : ℕ) :
    digits β (Int.ofNat (β.base ^ k)) = k + 1 := by
  have hbase : 1 < β.base := lt_of_lt_of_le Nat.one_lt_two β.base_valid
  have hpow : β.base ^ k ≠ 0 := pow_ne_zero _ (Nat.ne_of_gt (Nat.zero_lt_of_lt β.base_valid))
  have hpowInt : Int.ofNat (β.base ^ k) ≠ 0 := Int.ofNat_ne_zero.mpr hpow
  rw [digits, ite_eq_right hpowInt]
  simp [Nat.log_pow hbase]

end FloatLib.Floats.Formats.Flocq
