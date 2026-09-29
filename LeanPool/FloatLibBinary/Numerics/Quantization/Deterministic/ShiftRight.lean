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

import Mathlib.Tactic.NormNum
public import LeanPool.FloatLibBinary.Numerics.Quantization.Deterministic.Quotient
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq

/-!
# Deterministic nearest-even shift rounding

Power-of-two nearest-even rounding shared by binary floating-point, fixed-point, and other
quantized representations. The executable path avoids constructing an enormous halfway marker
when the shift exceeds the input bit length.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Remainder discarded by shifting a natural number right.

Writing the operation this way avoids constructing `2^shift`. When `shift` exceeds the input's
bit length, the quotient is zero and the remainder is the original value.
-/
@[inline] def shiftRightRemainder (value shift : Nat) : Nat :=
  value - Nat.shiftLeft (Nat.shiftRight value shift) shift

/-- The bits discarded by a right shift are exactly the remainder modulo `2^shift`. -/
theorem shiftRightRemainder_eq_mod (value shift : Nat) :
    shiftRightRemainder value shift = value % 2 ^ shift := by
  simp only [shiftRightRemainder, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.mod_eq_sub_div_mul]

/--
Round `value / 2^shift` to the nearest natural number, breaking exact halfway cases toward even.

This is the power-of-two specialization of `roundQuotientEven`. It belongs in the common
quantization layer because binary floats, P3109 formats, and fixed-point kernels all discard low
binary digits in the same way. A bit-length check returns zero before constructing the halfway
marker `2^(shift - 1)` when the shift is too large.
-/
@[inline] def roundShiftRightEven (value shift : Nat) : Nat :=
  if shift == 0 then
    value
  else if value.log2 + 1 < shift then
    0
  else
    let quotient := Nat.shiftRight value shift
    let remainder := shiftRightRemainder value shift
    let half := Nat.shiftLeft 1 (shift - 1)
    if remainder < half then
      quotient
    else if half < remainder then
      quotient + 1
    else if quotient % 2 == 0 then
      quotient
    else
      quotient + 1

/-- Shifting by no bits leaves the value unchanged. -/
@[simp, grind =] theorem roundShiftRightEven_zero (value : Nat) :
    roundShiftRightEven value 0 = value := by
  simp [roundShiftRightEven]

/--
Nearest-even shift rounding in quotient/remainder form.

The runtime definition has an extra branch returning `0` when `shift` exceeds the bit length of
`value`; it exists only to avoid allocating an enormous halfway marker. That branch is invisible
here because the quotient is then zero and the discarded value lies strictly below half, so proofs
can work with the plain quotient/remainder equation.
-/
theorem roundShiftRightEven_def (value shift : Nat) :
    roundShiftRightEven value shift =
      if shift == 0 then
        value
      else
        let quotient := Nat.shiftRight value shift
        let remainder := value - Nat.shiftLeft quotient shift
        let half := 2 ^ (shift - 1)
        if remainder < half then
          quotient
        else if half < remainder then
          quotient + 1
        else if quotient % 2 == 0 then
          quotient
        else
          quotient + 1 := by
  unfold roundShiftRightEven
  simp only [shiftRightRemainder, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
  split
  · rfl
  · split
    · rename_i hshift hlarge
      have hhalf : value < 2 ^ (shift - 1) :=
        Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
      have hquotient : value >>> shift = 0 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_eq_of_lt (lt_of_lt_of_le hhalf (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hquotient, hhalf]
    · rfl

/-- Nearest-even shifting is nearest-even division by the corresponding power of two. -/
theorem roundShiftRightEven_eq_roundQuotientEven (value shift : Nat) :
    roundShiftRightEven value shift = roundQuotientEven value (2 ^ shift) := by
  by_cases hs : shift = 0
  · simp [hs, roundQuotientEven, Nat.mod_one]
  have hp : 2 ^ shift = 2 * 2 ^ (shift - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, shift = n + 1 := ⟨shift - 1, by omega⟩
    simp [pow_succ, Nat.mul_comm]
  rw [roundShiftRightEven_def]
  change (if shift == 0 then value else
    if shiftRightRemainder value shift < 2 ^ (shift - 1) then value.shiftRight shift
    else if 2 ^ (shift - 1) < shiftRightRemainder value shift then value.shiftRight shift + 1
    else if value.shiftRight shift % 2 == 0 then value.shiftRight shift
    else value.shiftRight shift + 1) = _
  simp only [beq_iff_eq, hs, ite_false, shiftRightRemainder_eq_mod, Nat.shiftRight_eq',
    Nat.shiftRight_eq_div_pow, roundQuotientEven]
  rw [hp]
  simp only [Nat.mul_lt_mul_left (by decide : 0 < (2 : Nat))]

private theorem roundShiftRightEven_eq_shiftRight_or_add_one
    (value shift : Nat) :
    roundShiftRightEven value shift = Nat.shiftRight value shift ∨
      roundShiftRightEven value shift = Nat.shiftRight value shift + 1 := by
  classical
  by_cases hshift : shift = 0
  · subst shift
    simp [roundShiftRightEven_def]
  · have hshiftBool : (shift == 0) = false := by
      simp [hshift]
    let quotient := Nat.shiftRight value shift
    let remainder := value - Nat.shiftLeft quotient shift
    let half := 2 ^ (shift - 1)
    have hround :
        roundShiftRightEven value shift =
          if remainder < half then quotient
          else if remainder > half then quotient + 1
          else if quotient % 2 = 0 then quotient else quotient + 1 := by
      simp (config := { zeta := true })
        [roundShiftRightEven_def, hshiftBool, quotient, remainder, half]
    by_cases hlt : remainder < half
    · left
      simp [hround, hlt, quotient]
    · by_cases hgt : remainder > half
      · right
        simp [hround, hlt, hgt, quotient]
      · by_cases heven : quotient % 2 = 0
        · left
          rw [hround]
          simp only [hlt, hgt, heven, ite_false, ite_true]
          rfl
        · right
          rw [hround]
          simp only [hlt, hgt, heven, ite_false]
          rfl

/-- Nearest-even shift rounding is never below the floor quotient. -/
theorem shiftRight_le_roundShiftRightEven (value shift : Nat) :
    Nat.shiftRight value shift ≤ roundShiftRightEven value shift := by
  rcases roundShiftRightEven_eq_shiftRight_or_add_one value shift with h | h
  · simp [h]
  · simp [h]

/-- Nearest-even shift rounding is at most one above the floor quotient. -/
theorem roundShiftRightEven_le_shiftRight_add1 (value shift : Nat) :
    roundShiftRightEven value shift ≤ Nat.shiftRight value shift + 1 := by
  rcases roundShiftRightEven_eq_shiftRight_or_add_one value shift with h | h
  · simp [h]
  · simp [h]

/-- A one-bit nearest-even shift increments the floor quotient exactly when `value % 4 = 3`. -/
theorem roundShiftRightEven_one (value : Nat) :
    roundShiftRightEven value 1 =
      if value % 4 = 3 then value / 2 + 1 else value / 2 := by
  have hmod4 : value % 4 < 4 :=
    Nat.mod_lt value (by decide)
  have hquotientParity :
      (value / 2) % 2 = (value % 4) / 2 := by
    simpa using (Nat.mod_mul_right_div_self value 2 2).symm
  have hremainderParity :
      value % 2 = (value % 4) % 2 := by
    exact (Nat.mod_mul_right_mod value 2 2).symm
  have hquotient :
      value.shiftRight 1 = value / 2 := by
    simpa using Nat.shiftRight_eq_div_pow value 1
  have hshiftBack :
      (value.shiftRight 1).shiftLeft 1 =
        (value / 2) * 2 := by
    simpa [Nat.shiftLeft_eq, hquotient]
  have hremainder :
      value - (value.shiftRight 1).shiftLeft 1 =
        value % 2 := by
    rw [hshiftBack]
    exact Nat.mod_eq_sub_div_mul.symm
  rw [roundShiftRightEven_def]
  simp only [beq_iff_eq, one_ne_zero, ite_false]
  norm_num only [Nat.reducePow, Nat.reduceSub]
  rw [hremainder, hquotient]
  have hcases :
      value % 4 = 0 ∨ value % 4 = 1 ∨
        value % 4 = 2 ∨ value % 4 = 3 := by
    omega
  rcases hcases with hmod4 | hmod4 | hmod4 | hmod4
  all_goals
    have hmod2 := hremainderParity
    have hquotientMod2 := hquotientParity
    rw [hmod4] at hmod2 hquotientMod2
    norm_num at hmod2 hquotientMod2
    simp [hmod4, hmod2, hquotientMod2]

/-- Rounding an exact multiple of two by one bit is exact. -/
theorem roundShiftRightEven_two_mul (value : Nat) :
    roundShiftRightEven (2 * value) 1 = value := by
  simp [roundShiftRightEven_def, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.mul_comm]

end FloatLib.Numerics
