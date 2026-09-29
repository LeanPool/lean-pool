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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Product.Proof
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Verified two-limb rounding

These theorems connect the native `UInt128` shifts, increments, and nearest-even rounding
operations to their natural-number meanings.

The runtime uses two `UInt64` limbs; the proof model interprets them as one `Nat`.
Carry propagation, cross-limb shifts, low-bit insertion, and ties-to-even rounding preserve that
interpretation under the stated capacity bounds.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-! ## Limb-local primitives -/

/-- Mathematical value of two-limb increment when it does not overflow. -/
theorem UInt128.increment_toNat (value : UInt128)
    (hfit : value.toNat + 1 < 2 ^ 128) :
    value.increment.toNat = value.toNat + 1 := by
  let sum := add64 value.lo 1
  have hsum :
      sum.value.toNat + sum.carry.toNat * 2 ^ 64 =
        value.lo.toNat + 1 := by
    simpa [sum] using add64_toNat value.lo 1
  have hcarry : sum.carry.toNat ≤ 1 := by
    simpa [sum] using add64_carry_le_one value.lo 1
  have hhighFit :
      value.hi.toNat + sum.carry.toNat < 2 ^ 64 := by
    unfold UInt128.toNat at hfit
    have hsumNonnegative :
        sum.value.toNat + sum.carry.toNat * 2 ^ 64 ≥
          sum.carry.toNat * 2 ^ 64 := by omega
    by_contra h
    have hlarge :
        2 ^ 64 ≤ value.hi.toNat + sum.carry.toNat :=
      Nat.le_of_not_gt h
    have hpow : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
    rw [hpow] at hfit
    nlinarith
  have hhigh :
      (value.hi + sum.carry).toNat =
        value.hi.toNat + sum.carry.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hhighFit]
  unfold UInt128.increment UInt128.toNat
  dsimp only
  rw [hhigh]
  change
    sum.value.toNat + (value.hi.toNat + sum.carry.toNat) * 2 ^ 64 =
      value.lo.toNat + value.hi.toNat * 2 ^ 64 + 1
  calc
    sum.value.toNat + (value.hi.toNat + sum.carry.toNat) * 2 ^ 64 =
        (sum.value.toNat + sum.carry.toNat * 2 ^ 64) +
          value.hi.toNat * 2 ^ 64 := by ring
    _ = (value.lo.toNat + 1) + value.hi.toNat * 2 ^ 64 := by
      rw [hsum]
    _ = value.lo.toNat + value.hi.toNat * 2 ^ 64 + 1 := by ring

/-- Setting the low bit of a two-limb value agrees with natural-number bitwise OR. -/
@[simp, grind =] theorem UInt128.setLowBit_toNat (value : UInt128) :
    value.setLowBit.toNat = value.toNat ||| 1 := by
  have hlow : value.lo.toNat < 2 ^ 64 :=
    value.lo.toNat_lt
  have hone : (1 : Nat) < 2 ^ 64 := by norm_num
  have hlowSet : value.lo.toNat ||| 1 < 2 ^ 64 :=
    Nat.or_lt_two_pow hlow hone
  unfold UInt128.setLowBit UInt128.toNat
  rw [UInt64.toNat_or]
  simp only [UInt64.toNat_one]
  calc
    (value.lo.toNat ||| 1) + value.hi.toNat * 2 ^ 64 =
        2 ^ 64 * value.hi.toNat + (value.lo.toNat ||| 1) := by ring
    _ = (2 ^ 64 * value.hi.toNat) ||| (value.lo.toNat ||| 1) :=
      Nat.two_pow_add_eq_or_of_lt hlowSet value.hi.toNat
    _ = ((2 ^ 64 * value.hi.toNat) ||| value.lo.toNat) ||| 1 := by
      rw [Nat.or_assoc]
    _ = (2 ^ 64 * value.hi.toNat + value.lo.toNat) ||| 1 := by
      rw [Nat.two_pow_add_eq_or_of_lt hlow value.hi.toNat]
    _ = (value.lo.toNat + value.hi.toNat * 2 ^ 64) ||| 1 := by
      congr 1
      ring

namespace UInt128

/-! ## Cross-limb shifts -/

/-- The native two-word shift is exact division by two. -/
@[simp, grind =] theorem shiftRightOne_toNat (value : UInt128) :
    value.shiftRightOne.toNat = value.toNat / 2 := by
  have hhigh :
      (value.hi >>> 1).toNat = value.hi.toNat / 2 := by
    rw [UInt64.toNat_shiftRight]
    rw [show UInt64.toNat 1 % 64 = 1 by decide]
    norm_num [Nat.shiftRight_eq_div_pow]
  have hlow :
      (value.lo >>> 1).toNat = value.lo.toNat / 2 := by
    rw [UInt64.toNat_shiftRight]
    rw [show UInt64.toNat 1 % 64 = 1 by decide]
    norm_num [Nat.shiftRight_eq_div_pow]
  have hbit :
      (value.hi &&& 1).toNat = value.hi.toNat % 2 := by
    rw [UInt64.toNat_and]
    simp
  have hcarry :
      ((value.hi &&& 1) <<< 63).toNat =
        value.hi.toNat % 2 * 2 ^ 63 := by
    rw [UInt64.toNat_shiftLeft, hbit]
    rw [show UInt64.toNat 63 % 64 = 63 by decide]
    simp only [Nat.shiftLeft_eq]
    have hmod : value.hi.toNat % 2 < 2 :=
      Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt]
    nlinarith
  have hlowBound : value.lo.toNat / 2 < 2 ^ 63 := by
    have hlo := value.lo.toNat_lt
    omega
  have hor :
      (value.lo.toNat / 2) ||| (value.hi.toNat % 2 * 2 ^ 63) =
        value.lo.toNat / 2 + value.hi.toNat % 2 * 2 ^ 63 := by
    rw [Nat.or_comm]
    simpa [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt hlowBound
        (value.hi.toNat % 2)).symm
  unfold shiftRightOne UInt128.toNat
  rw [UInt64.toNat_or, hlow, hcarry, hor, hhigh]
  have hloDecompose := Nat.mod_add_div value.lo.toNat 2
  have hhiDecompose := Nat.mod_add_div value.hi.toNat 2
  norm_num at hloDecompose hhiDecompose ⊢
  omega

private theorem lowTwoBits_toNat (value : UInt128) :
    (value.lo &&& 3).toNat = value.toNat % 4 := by
  rw [UInt64.toNat_and]
  change value.lo.toNat &&& 3 = value.toNat % 4
  rw [show 3 = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  unfold UInt128.toNat
  simp [Nat.add_mod, Nat.mul_mod]

/-! ## Nearest-even right shifts -/

/-- Native one-bit nearest-even rounding agrees with the mathematical rounder. -/
theorem roundShiftRightOneEven_toNat (value : UInt128)
    (hfit : value.toNat / 2 + 1 < 2 ^ 128) :
    value.roundShiftRightOneEven.toNat =
      FloatLib.Numerics.roundShiftRightEven
        value.toNat 1 := by
  have hshift := value.shiftRightOne_toNat
  have hfitShift :
      value.shiftRightOne.toNat + 1 < 2 ^ 128 := by
    rw [hshift]
    exact hfit
  have hbits := lowTwoBits_toNat value
  rw [FloatLib.Numerics.roundShiftRightEven_one]
  unfold roundShiftRightOneEven
  dsimp only
  by_cases hround : value.toNat % 4 = 3
  · have hnative : value.lo &&& 3 = 3 := by
      apply UInt64.toNat_inj.mp
      rw [hbits, hround]
      decide
    simp only [hnative, beq_self_eq_true, ite_true]
    rw [increment_toNat _ hfitShift, hshift]
    simp [hround]
  · have hnative : value.lo &&& 3 ≠ 3 := by
      intro heq
      apply hround
      have heqNat := congrArg UInt64.toNat heq
      rw [hbits] at heqNat
      simpa using heqNat
    simp only [hnative, beq_iff_eq, ite_false, hshift, hround]

/--
When the shifted result fits one limb, `shiftRightLow` is the mathematical right shift of the
two-limb input.
-/
theorem shiftRightLow_toNat (value : UInt128) (shift : Nat)
    (hpositive : 0 < shift) (hshift : shift < 64)
    (hhigh : value.hi.toNat < 2 ^ shift) :
    (shiftRightLow value shift).toNat = value.toNat >>> shift := by
  have hcomplement : 64 - shift < 64 := by omega
  have hlowBound : value.lo.toNat >>> shift < 2 ^ (64 - shift) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
    have hlo := value.lo.toNat_lt
    have hpow : 2 ^ (64 - shift) * 2 ^ shift = 2 ^ 64 := by
      rw [← pow_add]
      congr
      omega
    simpa [hpow] using hlo
  have hhighShift :
      (value.hi <<< UInt64.ofNat (64 - shift)).toNat =
        value.hi.toNat <<< (64 - shift) := by
    apply FloatLib.Numerics.FixedWord.shiftLeft_toNat
      value.hi (64 - shift) hcomplement
    rw [Nat.shiftLeft_eq]
    have hpow : 2 ^ shift * 2 ^ (64 - shift) = 2 ^ 64 := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hshift)]
    nlinarith
  have hor :
      (value.lo.toNat >>> shift) |||
          (value.hi.toNat <<< (64 - shift)) =
        (value.lo.toNat >>> shift) +
          (value.hi.toNat <<< (64 - shift)) := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlowBound, Nat.add_comm]
  unfold shiftRightLow UInt128.toNat
  rw [UInt64.toNat_or,
    FloatLib.Numerics.FixedWord.shiftRight_toNat value.lo shift hshift,
    hhighShift, hor]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hpow64 :
      2 ^ 64 = 2 ^ shift * 2 ^ (64 - shift) := by
    rw [← pow_add]
    rw [Nat.add_sub_of_le (Nat.le_of_lt hshift)]
  rw [hpow64]
  have hreassociate :
      value.hi.toNat * (2 ^ shift * 2 ^ (64 - shift)) =
        2 ^ shift * (value.hi.toNat * 2 ^ (64 - shift)) := by
    ring
  rw [hreassociate, Nat.add_mul_div_left _ _ (by positivity)]

/--
The one-limb result of native two-limb nearest-even rounding agrees with the common mathematical
rounder whenever the stated bounds exclude overflow.
-/
theorem roundShiftRightEven_toNat (value : UInt128) (shift : Nat)
    (hpositive : 0 < shift) (hshift : shift < 64)
    (hhigh : value.hi.toNat < 2 ^ shift)
    (hincrementFit : (value.toNat >>> shift) + 1 < 2 ^ 64) :
    (roundShiftRightEven value shift).toNat =
      FloatLib.Numerics.roundShiftRightEven
        value.toNat shift := by
  have hquotient := shiftRightLow_toNat value shift hpositive hshift hhigh
  have hremainder := uint64_lowBits_toNat value.lo shift hshift
  have hhalf :
      (((1 : UInt64) <<< UInt64.ofNat (shift - 1)).toNat) =
        2 ^ (shift - 1) :=
    uint64_powTwo_toNat (shift - 1) (by omega)
  have hremainderNat :
      value.toNat - (value.toNat >>> shift <<< shift) =
        value.lo.toNat % 2 ^ shift := by
    unfold UInt128.toNat
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      ← Nat.mod_eq_sub_div_mul]
    have hpow : 2 ^ 64 = 2 ^ shift * 2 ^ (64 - shift) := by
      rw [← pow_add]
      rw [Nat.add_sub_of_le (Nat.le_of_lt hshift)]
    rw [hpow]
    have hreassociate :
        value.hi.toNat * (2 ^ shift * 2 ^ (64 - shift)) =
          2 ^ shift * (value.hi.toNat * 2 ^ (64 - shift)) := by
      ring
    rw [hreassociate, Nat.add_mul_mod_self_left]
  change
    value.toNat - (value.toNat.shiftRight shift).shiftLeft shift =
      value.lo.toNat % 2 ^ shift at hremainderNat
  have hincrement :
      (shiftRightLow value shift + 1).toNat =
        (value.toNat >>> shift) + 1 := by
    rw [UInt64.toNat_add, hquotient]
    exact Nat.mod_eq_of_lt hincrementFit
  have heven :
      ((shiftRightLow value shift &&& 1) == 0) ↔
        (value.toNat >>> shift) % 2 == 0 := by
    simp [← UInt64.toNat_inj, hquotient]
  change
    (shiftRightLow value shift).toNat =
      value.toNat.shiftRight shift at hquotient
  change
    (shiftRightLow value shift + 1).toNat =
      value.toNat.shiftRight shift + 1 at hincrement
  change
    ((shiftRightLow value shift &&& 1) == 0) ↔
      value.toNat.shiftRight shift % 2 == 0 at heven
  have hgeneric :
      FloatLib.Numerics.roundShiftRightEven
        value.toNat shift =
        if value.lo.toNat % 2 ^ shift < 2 ^ (shift - 1) then
          value.toNat.shiftRight shift
        else if value.lo.toNat % 2 ^ shift > 2 ^ (shift - 1) then
          value.toNat.shiftRight shift + 1
        else if value.toNat.shiftRight shift % 2 == 0 then
          value.toNat.shiftRight shift
        else
          value.toNat.shiftRight shift + 1 := by
    rw [FloatLib.Numerics.roundShiftRightEven_def]
    simp only [beq_iff_eq, Nat.ne_of_gt hpositive, ite_false]
    rw [hremainderNat]
  rw [hgeneric]
  unfold roundShiftRightEven
  simp only [UInt64.lt_iff_toNat_lt, hremainder, hhalf]
  by_cases hless : value.lo.toNat % 2 ^ shift < 2 ^ (shift - 1)
  · simp [hless, hquotient]
  by_cases hgreater : value.lo.toNat % 2 ^ shift > 2 ^ (shift - 1)
  · simp [hless, hgreater, hincrement]
  by_cases hevenNative : (shiftRightLow value shift &&& 1) == 0
  · have hevenNat := heven.mp hevenNative
    simp only [hless, ↓reduceIte, hgreater, hevenNative, hquotient, Nat.shiftRight_eq', beq_iff_eq,
      left_eq_ite_iff, Nat.mod_two_not_eq_zero, Nat.left_eq_add, one_ne_zero, imp_false,
        Nat.mod_two_not_eq_one]
    change value.toNat.shiftRight shift % 2 = 0
    simpa only [beq_iff_eq] using hevenNat
  · have hevenNat : ¬value.toNat.shiftRight shift % 2 == 0 := by
      exact fun h => hevenNative (heven.mpr h)
    have hoddNat : value.toNat.shiftRight shift % 2 = 1 := by
      have hlt : value.toNat.shiftRight shift % 2 < 2 :=
        Nat.mod_lt _ (by decide)
      have hne : value.toNat.shiftRight shift % 2 ≠ 0 := by
        intro hzero
        apply hevenNat
        simpa only [beq_iff_eq] using hzero
      omega
    simp only [hless, ↓reduceIte, hgreater, hevenNative, Bool.false_eq_true, hincrement,
      Nat.shiftRight_eq',
      beq_iff_eq, right_eq_ite_iff, Nat.add_eq_left, one_ne_zero, imp_false,
        Nat.mod_two_not_eq_zero]
    change value.toNat.shiftRight shift % 2 = 1
    exact hoddNat

end UInt128

end FloatLib.Numerics.FixedWord
