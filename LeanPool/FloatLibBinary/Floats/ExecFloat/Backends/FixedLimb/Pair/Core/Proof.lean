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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Optimized
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-word pair-kernel storage

The field helpers in `Core.Runtime` agree with the width-generic carrier under
`NativePair.Eligible`. The eligibility bounds ensure that field extraction and packing do not
lose bits to native-word overflow.

`packNormal_eq_ofFields` relates native packing to the canonical field constructor for an
in-range exponent field and a normalized significand. `decode_of_normalExponent` gives the
finite components when the exponent is nonzero and not all ones. These contracts apply to
binary128 and every other eligible descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

variable {fmt : FloatFormat}

/-! ## Layout bounds -/

/-- An eligible descriptor uses the conventional IEEE encoding and bias. -/
theorem Eligible.isIEEE (h : Eligible fmt) : fmt.isIEEE = true := h.1

/-- An eligible fraction is wider than one word. -/
theorem Eligible.frac_gt (h : Eligible fmt) : 64 < fmt.fracWidth := h.2.1

/-- An eligible descriptor fits in two words. -/
theorem Eligible.width_le (h : Eligible fmt) : fmt.bitWidth ≤ 128 := h.2.2

/-- The exponent and fraction of an eligible descriptor share at most 127 bits. -/
theorem Eligible.sum_le (h : Eligible fmt) :
    fmt.expWidth + fmt.fracWidth ≤ 127 := by
  have hwidth := h.width_le
  unfold FloatFormat.bitWidth at hwidth
  omega

/-- An eligible fraction has at most 125 bits, since the exponent field has at least two. -/
theorem Eligible.frac_le (h : Eligible fmt) : fmt.fracWidth ≤ 125 := by
  have hsum := h.sum_le
  have hexp := fmt.expWidth_ge_two
  omega

/-- An eligible exponent field has at most 62 bits. -/
theorem Eligible.exp_le (h : Eligible fmt) : fmt.expWidth ≤ 62 := by
  have hsum := h.sum_le
  have hfrac := h.frac_gt
  omega

/-- An eligible descriptor uses the IEEE exceptional-value encoding. -/
theorem Eligible.encoding (h : Eligible fmt) : fmt.encoding = .ieee :=
  ((FloatFormat.isIEEE_eq_true_iff fmt).mp h.1).1

/-- An eligible descriptor uses the conventional bias. -/
theorem Eligible.exponentBias_eq (h : Eligible fmt) : fmt.exponentBias = fmt.bias :=
  ((FloatFormat.isIEEE_eq_true_iff fmt).mp h.1).2

/-- The bias of an eligible descriptor is below `2^61`. -/
theorem Eligible.bias_lt (h : Eligible fmt) : fmt.bias < 2 ^ 61 := by
  have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by decide) h.exp_le
  have hbias := fmt.two_pow_expWidth_eq_two_mul_bias_add_two
  norm_num at hpow ⊢
  omega

/-! ## Layout constants -/

/-- The high word holds `fracWidth - 64` fraction bits. -/
theorem fracHighWidth_toNat (h : Eligible fmt) :
    (fracHighWidth fmt).toNat = fmt.fracWidth - 64 := by
  unfold fracHighWidth
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have := h.frac_le
  omega

/-- The high fraction mask is `2^(fracWidth - 64) - 1`. -/
theorem fracHighMask_toNat (h : Eligible fmt) :
    (fracHighMask fmt).toNat = 2 ^ (fmt.fracWidth - 64) - 1 := by
  have hpow :=
    uint64_powTwo_toNat (fmt.fracWidth - 64) (by have := h.frac_le; omega)
  unfold fracHighMask fracHighWidth
  rw [UInt64.toNat_sub_of_le, hpow]
  · simp
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hpow]
    simpa using Nat.one_le_two_pow

/-- The native all-ones exponent field is the descriptor's all-ones exponent. -/
theorem expAllOnes_toNat (h : Eligible fmt) :
    (expAllOnes fmt).toNat = fmt.expAllOnesNat := by
  have hpow := uint64_powTwo_toNat fmt.expWidth (by have := h.exp_le; omega)
  unfold expAllOnes FloatFormat.expAllOnesNat
  rw [UInt64.toNat_sub_of_le, hpow]
  · simp
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hpow]
    simpa using Nat.one_le_two_pow

/-- The implicit bit sits at high-word position `fracWidth - 64`. -/
theorem implicitBit_toNat (h : Eligible fmt) :
    (implicitBit fmt).toNat = 2 ^ (fmt.fracWidth - 64) := by
  unfold implicitBit fracHighWidth
  exact uint64_powTwo_toNat (fmt.fracWidth - 64) (by have := h.frac_le; omega)

/-- The carry bit sits at high-word position `fracWidth - 63`. -/
theorem carryBit_toNat (h : Eligible fmt) :
    (implicitBit fmt <<< 1).toNat = 2 ^ (fmt.fracWidth - 63) := by
  rw [UInt64.toNat_shiftLeft, implicitBit_toNat h]
  have hfrac := h.frac_le
  have hfracGt := h.frac_gt
  have hpow : 2 ^ (fmt.fracWidth - 64) <<< 1 = 2 ^ (fmt.fracWidth - 63) := by
    rw [Nat.shiftLeft_eq, pow_one,
      show fmt.fracWidth - 63 = fmt.fracWidth - 64 + 1 by omega, pow_succ]
  rw [show (1 : UInt64).toNat % 64 = 1 by decide, hpow]
  apply Nat.mod_eq_of_lt
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- The sign bit sits at high-word position `expWidth + fracWidth - 64`. -/
theorem signMask_toNat (h : Eligible fmt) :
    (signMask fmt).toNat = 2 ^ (fmt.expWidth + fmt.fracWidth - 64) := by
  unfold signMask
  exact uint64_powTwo_toNat _ (by have := h.sum_le; omega)

/-! ## Splitting and joining words -/

/-- The low storage word is the low 64 bits of the encoding. -/
theorem low_word_toNat (x : Model fmt) :
    (toWords x).lo.toNat = x.toNatBits % 2 ^ 64 := by
  simp [toWords, Model.toNatBits, BitVec.extractLsb']

/-- The high storage word is the encoding shifted down by 64 bits. -/
theorem high_word_toNat (h : Eligible fmt) (x : Model fmt) :
    (toWords x).hi.toNat = x.toNatBits / 2 ^ 64 := by
  simp only [toWords, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
  change
    (BitVec.ofNat 64 (x.toNatBits / 2 ^ 64)).toNat =
      x.toNatBits / 2 ^ 64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  calc
    x.toNatBits < 2 ^ fmt.bitWidth := Model.toNatBits_lt_two_pow x
    _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) h.width_le
    _ = 2 ^ 64 * 2 ^ 64 := by norm_num

/-- The two native storage words reconstruct the exact encoding. -/
theorem toWords_toNat (h : Eligible fmt) (x : Model fmt) :
    (toWords x).toNat = x.toNatBits := by
  rw [UInt128.toNat, low_word_toNat, high_word_toNat h, Nat.mul_comm]
  exact Nat.mod_add_div x.toNatBits (2 ^ 64)

/-- Joining two native words reconstructs their value whenever it fits the storage width. -/
theorem ofWords_toNat (words : UInt128)
    (hfit : words.toNat < 2 ^ fmt.bitWidth) :
    (ofWords fmt words).toNatBits = words.toNat := by
  unfold ofWords Model.toNatBits Model.ofBits
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, UInt64.toNat_toBitVec]
  rw [← Nat.shiftLeft_add_eq_or_of_lt words.lo.toNat_lt, Nat.shiftLeft_eq]
  have hvalue : words.hi.toNat * 2 ^ 64 + words.lo.toNat = words.toNat := by
    unfold UInt128.toNat
    ring
  rw [hvalue]
  exact Nat.mod_eq_of_lt hfit

/-! ## Field extraction -/

/-- Native sign extraction agrees with the public carrier. -/
theorem signBit_eq (h : Eligible fmt) (x : Model fmt) :
    signBit fmt (toWords x).hi = Model.signBit x := by
  rw [Model.signBit_eq_signBitImpl_apply]
  unfold signBit Model.signBitImpl
  have hsum := h.sum_le
  have hfrac := h.frac_gt
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq]
  rw [← UInt64.toNat_inj, UInt64.toNat_and, signMask_toNat h, high_word_toNat h x,
    UInt64.toNat_zero, Nat.and_two_pow, Nat.testBit_div_two_pow,
    show fmt.expWidth + fmt.fracWidth - 64 + 64 = fmt.expWidth + fmt.fracWidth by omega]
  cases x.toNatBits.testBit (fmt.expWidth + fmt.fracWidth) <;> simp

/-- Native exponent extraction agrees with the public carrier. -/
theorem expField_toNat (h : Eligible fmt) (x : Model fmt) :
    (expField fmt (toWords x).hi).toNat = Model.expField x := by
  rw [Model.expField_eq_expFieldImpl_apply]
  unfold expField Model.expFieldImpl
  have hfrac := h.frac_gt
  have hfracLe := h.frac_le
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, high_word_toNat h x,
    fracHighWidth_toNat h, expAllOnes_toNat h,
    Nat.mod_eq_of_lt (by omega : fmt.fracWidth - 64 < 64)]
  congr 1
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← pow_add, show 64 + (fmt.fracWidth - 64) = fmt.fracWidth by omega]

/-- The two fraction limbs reconstruct the public fraction field. -/
theorem fraction_toNat (h : Eligible fmt) (x : Model fmt) :
    (fracHigh fmt (toWords x).hi).toNat * 2 ^ 64 + (toWords x).lo.toNat =
      Model.fracField x := by
  rw [Model.fracField_eq_fracFieldImpl_apply]
  unfold fracHigh Model.fracFieldImpl FloatFormat.fracMaskNat
  have hfrac := h.frac_gt
  rw [UInt64.toNat_and, high_word_toNat h x, low_word_toNat, fracHighMask_toNat h,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    show 2 ^ fmt.fracWidth = 2 ^ 64 * 2 ^ (fmt.fracWidth - 64) by
      rw [← pow_add]
      congr 1
      omega,
    Nat.mod_mul]
  ring

/-- The high fraction limb occupies at most `fracWidth - 64` bits. -/
theorem fracHigh_lt (h : Eligible fmt) (high : UInt64) :
    (fracHigh fmt high).toNat < 2 ^ (fmt.fracWidth - 64) := by
  unfold fracHigh
  rw [UInt64.toNat_and, fracHighMask_toNat h]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide))

/-- The native exponent field fits the exponent width. -/
theorem expField_lt (h : Eligible fmt) (high : UInt64) :
    (expField fmt high).toNat < 2 ^ fmt.expWidth := by
  unfold expField
  rw [UInt64.toNat_and, expAllOnes_toNat h]
  unfold FloatFormat.expAllOnesNat
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide))

/-- A nonzero, nonexceptional native exponent lies in the normal range. -/
theorem normalExponent_bounds (h : Eligible fmt) (x : Model fmt)
    (hnonzero : expField fmt (toWords x).hi ≠ 0)
    (hnotAllOnes : expField fmt (toWords x).hi ≠ expAllOnes fmt) :
    0 < (expField fmt (toWords x).hi).toNat ∧
      (expField fmt (toWords x).hi).toNat < fmt.expAllOnesNat := by
  have hnonzeroModel : Model.expField x ≠ 0 := by
    rw [← expField_toNat h x]
    intro hzero
    apply hnonzero
    apply UInt64.toNat_inj.mp
    simpa using hzero
  have hnotAllOnesModel : Model.expField x ≠ fmt.expAllOnesNat := by
    rw [← expAllOnes_toNat h, ← expField_toNat h x]
    intro heq
    exact hnotAllOnes (UInt64.toNat_inj.mp heq)
  have hbounds := Model.expField_interior_bounds x hnonzeroModel hnotAllOnesModel
  rwa [← expField_toNat h x] at hbounds

/-! ## Normal significands -/

/-- The normal significand is `2^fracWidth` plus the two fraction limbs in place. -/
theorem normalMantissa_toNat (h : Eligible fmt) (high low : UInt64)
    (hhigh : high.toNat < 2 ^ (fmt.fracWidth - 64)) :
    (normalMantissa fmt high low).toNat =
      2 ^ fmt.fracWidth + high.toNat * 2 ^ 64 + low.toNat := by
  have hfrac := h.frac_gt
  unfold normalMantissa UInt128.toNat
  rw [UInt64.toNat_or, implicitBit_toNat h, Nat.or_two_pow_eq_add_of_lt hhigh,
    show 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 by
      rw [← pow_add]
      congr 1
      omega]
  ring

/-- A normal significand occupies exactly `fracWidth + 1` bits, including its implicit bit. -/
theorem normalMantissa_bounds (h : Eligible fmt) (high low : UInt64)
    (hhigh : high.toNat < 2 ^ (fmt.fracWidth - 64)) :
    2 ^ fmt.fracWidth ≤ (normalMantissa fmt high low).toNat ∧
      (normalMantissa fmt high low).toNat < 2 ^ (fmt.fracWidth + 1) := by
  rw [normalMantissa_toNat h high low hhigh]
  have hfrac := h.frac_gt
  have hlow := low.toNat_lt
  have hsplit : 2 ^ fmt.fracWidth = 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 := by
    rw [← pow_add]
    congr 1
    omega
  have hsucc : 2 ^ (fmt.fracWidth + 1) = 2 * 2 ^ fmt.fracWidth := by
    rw [pow_succ]
    ring
  have hhighMul : (high.toNat + 1) * 2 ^ 64 ≤ 2 ^ (fmt.fracWidth - 64) * 2 ^ 64 :=
    Nat.mul_le_mul_right _ hhigh
  rw [← hsplit] at hhighMul
  constructor
  · omega
  · rw [hsucc]
    omega

/-- The significand `2^fracWidth` as two limbs. -/
theorem implicitMantissa_toNat (h : Eligible fmt) :
    (implicitMantissa fmt).toNat = 2 ^ fmt.fracWidth := by
  have hfrac := h.frac_gt
  unfold implicitMantissa UInt128.toNat
  rw [implicitBit_toNat h, ← pow_add]
  simp only [UInt64.toNat_zero, zero_add]
  congr 1
  omega

/-- The carried-out significand `2^(fracWidth + 1)` as two limbs. -/
theorem carryMantissa_toNat (h : Eligible fmt) :
    (carryMantissa fmt).toNat = 2 ^ (fmt.fracWidth + 1) := by
  have hfrac := h.frac_gt
  unfold carryMantissa UInt128.toNat
  rw [carryBit_toNat h, ← pow_add]
  simp only [UInt64.toNat_zero, zero_add]
  congr 1
  omega

/-- The two-limb carry test is exactly the carry produced by `fracWidth + 1`-bit rounding. -/
theorem isCarry_iff (h : Eligible fmt) (value : UInt128) :
    isCarry fmt value = true ↔ value.toNat = pow2 (fmt.fracWidth + 1) := by
  rw [pow2_eq_two_pow]
  unfold isCarry
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hhi, hlo⟩
    have hvalue : value = carryMantissa fmt := by
      cases value
      simp only [carryMantissa] at hhi hlo ⊢
      rw [hhi, hlo]
    rw [hvalue]
    exact carryMantissa_toNat h
  · intro hvalue
    have heq : value = carryMantissa fmt := by
      apply UInt128.toNat_injective
      rw [hvalue, carryMantissa_toNat h]
    rw [heq]
    exact ⟨rfl, rfl⟩

/-- Carry normalization of a rounded significand is either that significand or `2^fracWidth`. -/
theorem normalizeCarry_toNat (h : Eligible fmt) (carry : Bool) (rounded : UInt128) :
    (normalizeCarry fmt carry rounded).toNat =
      if carry then pow2 fmt.fracWidth else rounded.toNat := by
  unfold normalizeCarry
  cases carry
  · rfl
  · simp [implicitMantissa_toNat h, pow2_eq_two_pow]

/-! ## Packing -/

private theorem mul_two_pow_or_eq_add {a b i : Nat} (hb : b < 2 ^ i) :
    a * 2 ^ i ||| b = a * 2 ^ i + b := by
  have hor := Nat.two_pow_add_eq_or_of_lt hb a
  rw [Nat.mul_comm] at hor
  exact hor.symm

private theorem two_pow_or_eq_add {b i : Nat} (hb : b < 2 ^ i) :
    2 ^ i ||| b = 2 ^ i + b := by
  have hor := Nat.two_pow_add_eq_or_of_lt hb 1
  rw [Nat.mul_one] at hor
  exact hor.symm

/--
Native packing agrees with the field constructor for a normalized significand and an in-range
exponent field.
-/
theorem packNormal_eq_ofFields (h : Eligible fmt)
    (sign : Bool) (exponent : UInt64) (mantissa : UInt128)
    (hexponent : exponent.toNat < 2 ^ fmt.expWidth)
    (hmantissaLower : 2 ^ fmt.fracWidth ≤ mantissa.toNat)
    (hmantissaUpper : mantissa.toNat < 2 ^ (fmt.fracWidth + 1)) :
    packNormal fmt sign exponent mantissa =
      ofFields fmt sign exponent.toNat (mantissa.toNat - pow2 fmt.fracWidth) := by
  have hfrac := h.frac_gt
  have hfracLe := h.frac_le
  have hsum := h.sum_le
  have hexpGe := fmt.expWidth_ge_two
  set F := fmt.fracWidth with hF
  set E := fmt.expWidth with hE
  set k := F - 64 with hk
  set X := exponent.toNat with hX
  set hi := mantissa.hi.toNat with hhi
  set lo := mantissa.lo.toNat with hlo
  have hm : mantissa.toNat = lo + hi * 2 ^ 64 := rfl
  have hloLt : lo < 2 ^ 64 := mantissa.lo.toNat_lt
  have hpowF : 2 ^ F = 2 ^ k * 2 ^ 64 := by
    rw [← pow_add]
    congr 1
    omega
  have hpowEF : 2 ^ (E + F) = 2 ^ (E + k) * 2 ^ 64 := by
    rw [← pow_add]
    congr 1
    omega
  have hpowEk : 2 ^ (E + k) = 2 ^ E * 2 ^ k := pow_add 2 E k
  have hpowEkLe : 2 ^ (E + k) ≤ 2 ^ 63 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpowFsucc : 2 ^ (F + 1) = 2 ^ F + 2 ^ F := by
    rw [pow_succ]
    ring
  have hpowEFsucc : 2 ^ (E + F + 1) = 2 ^ (E + F) + 2 ^ (E + F) := by
    rw [pow_succ]
    ring
  have hbitWidth : 2 ^ fmt.bitWidth = 2 ^ (E + F + 1) := by
    unfold FloatFormat.bitWidth
    congr 1
    omega
  -- The high limb of a normal significand lies in `[2^k, 2^(k+1))`.
  have hhiLower : 2 ^ k ≤ hi := by
    by_contra hcon
    have hle : (hi + 1) * 2 ^ 64 ≤ 2 ^ k * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (Nat.lt_of_not_ge hcon)
    rw [← hpowF] at hle
    omega
  have hhiUpper : hi < 2 ^ k + 2 ^ k := by
    by_contra hcon
    have hle : (2 ^ k + 2 ^ k) * 2 ^ 64 ≤ hi * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (Nat.le_of_not_gt hcon)
    rw [Nat.add_mul, ← hpowF] at hle
    omega
  have hhiMask : hi &&& (2 ^ k - 1) = hi - 2 ^ k := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_sub_mod hhiLower,
      Nat.mod_eq_of_lt (by omega)]
  have hhiRest : hi - 2 ^ k < 2 ^ k := by omega
  have hexponentMask : X &&& (2 ^ E - 1) = X := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hexponent]
  have hexpShifted : X * 2 ^ k < 2 ^ (E + k) := by
    rw [hpowEk]
    exact Nat.mul_lt_mul_of_pos_right hexponent (Nat.two_pow_pos k)
  have hexpShiftedWord : X <<< k % 2 ^ 64 = X * 2 ^ k := by
    rw [Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    calc
      X * 2 ^ k < 2 ^ (E + k) := hexpShifted
      _ ≤ 2 ^ 63 := hpowEkLe
      _ < 2 ^ 64 := by norm_num
  -- The three fields of the high word occupy disjoint bit ranges.
  have hmiddle : X * 2 ^ k ||| (hi - 2 ^ k) = X * 2 ^ k + (hi - 2 ^ k) :=
    mul_two_pow_or_eq_add hhiRest
  have hmiddleLt : X * 2 ^ k + (hi - 2 ^ k) < 2 ^ (E + k) := by
    have hstep : (X + 1) * 2 ^ k ≤ 2 ^ E * 2 ^ k :=
      Nat.mul_le_mul_right _ hexponent
    rw [Nat.add_mul, one_mul] at hstep
    rw [hpowEk]
    omega
  have hhighValue :
      ((if sign then signMask fmt else 0) |||
          ((exponent &&& expAllOnes fmt) <<< fracHighWidth fmt) |||
          (mantissa.hi &&& fracHighMask fmt)).toNat =
        (if sign then 2 ^ (E + k) else 0) + (X * 2 ^ k + (hi - 2 ^ k)) := by
    rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_and,
      UInt64.toNat_and, expAllOnes_toNat h, fracHighWidth_toNat h, fracHighMask_toNat h]
    unfold FloatFormat.expAllOnesNat
    rw [← hX, ← hhi, ← hk, hexponentMask, hhiMask,
      Nat.mod_eq_of_lt (by omega : k < 64), hexpShiftedWord, Nat.lor_assoc, hmiddle]
    cases sign
    · simp
    · simp only [ite_true]
      rw [signMask_toNat h, ← hE, ← hF, show E + F - 64 = E + k by omega]
      exact two_pow_or_eq_add hmiddleLt
  have hhighLt :
      (if sign then 2 ^ (E + k) else 0) + (X * 2 ^ k + (hi - 2 ^ k)) < 2 ^ 64 := by
    have hsignLe : (if sign then 2 ^ (E + k) else 0) ≤ 2 ^ (E + k) := by
      cases sign <;> simp
    have : 2 ^ (E + k) + 2 ^ (E + k) ≤ 2 ^ 64 := by
      calc
        2 ^ (E + k) + 2 ^ (E + k) = 2 ^ (E + k + 1) := by
          rw [pow_succ]
          ring
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- The complete value assembled from both words.
  have hfraction : (hi - 2 ^ k) * 2 ^ 64 + lo = mantissa.toNat - 2 ^ F := by
    rw [hm, hpowF, Nat.sub_mul]
    have := Nat.mul_le_mul_right (2 ^ 64) hhiLower
    omega
  have hfractionLt : mantissa.toNat - 2 ^ F < 2 ^ F := by omega
  have hexpF : X * 2 ^ F < 2 ^ (E + F) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hexponent (Nat.two_pow_pos F)
  have hbodyLt : X * 2 ^ F + (mantissa.toNat - 2 ^ F) < 2 ^ (E + F) := by
    have hstep : (X + 1) * 2 ^ F ≤ 2 ^ E * 2 ^ F :=
      Nat.mul_le_mul_right _ hexponent
    rw [Nat.add_mul, one_mul] at hstep
    rw [pow_add]
    omega
  have htotal :
      ((if sign then 2 ^ (E + k) else 0) + (X * 2 ^ k + (hi - 2 ^ k))) * 2 ^ 64 + lo =
        (if sign then 2 ^ (E + F) else 0) + (X * 2 ^ F + (mantissa.toNat - 2 ^ F)) := by
    rw [← hfraction, hpowF, hpowEF]
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  have htotalLt :
      (if sign then 2 ^ (E + F) else 0) + (X * 2 ^ F + (mantissa.toNat - 2 ^ F)) <
        2 ^ (E + F + 1) := by
    rw [hpowEFsucc]
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  -- Compare the two encodings bit for bit through their natural-number values.
  rw [Model.ofFields_eq_ofFieldsImpl]
  unfold packNormal ofWords Model.ofFieldsImpl
  apply congrArg Model.ofBits
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, UInt64.toNat_toBitVec,
    Model.mkBitsImpl, BitVec.toNat_ofNatLT]
  rw [hhighValue, ← hlo, ← Nat.shiftLeft_add_eq_or_of_lt hloLt, Nat.shiftLeft_eq, htotal,
    hbitWidth, Nat.mod_eq_of_lt htotalLt]
  unfold FloatFormat.expAllOnesNat FloatFormat.fracMaskNat
  rw [← hE, ← hF, pow2_eq_two_pow, hexponentMask, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hfractionLt]
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
  rw [Nat.lor_assoc, mul_two_pow_or_eq_add hfractionLt]
  cases sign
  · simp
  · simp only [↓reduceIte]
    exact (two_pow_or_eq_add hbodyLt).symm

/-! ## Finite decoding -/

/-- Decode a normal finite value directly from its two native storage words. -/
theorem decode_of_normalExponent (h : Eligible fmt) (x : Model fmt)
    (hexponentZero : expField fmt (toWords x).hi ≠ 0)
    (hexponentFinite : expField fmt (toWords x).hi ≠ expAllOnes fmt) :
    FiniteKernel.decodeOption x =
      some {
        sign := signBit fmt (toWords x).hi
        exponent := (expField fmt (toWords x).hi).toNat
        mantissa :=
          (normalMantissa fmt (fracHigh fmt (toWords x).hi)
            (toWords x).lo).toNat } := by
  have hexponent :
      (expField fmt (toWords x).hi).toNat = Model.expField x :=
    expField_toNat h x
  have hexponentBounds :=
    normalExponent_bounds h x hexponentZero hexponentFinite
  have hsign :
      signBit fmt (toWords x).hi = Model.signBit x :=
    signBit_eq h x
  have hfraction :=
    fraction_toNat h x
  have hhigh :=
    fracHigh_lt h (toWords x).hi
  have hmantissa :
      (normalMantissa fmt (fracHigh fmt (toWords x).hi)
          (toWords x).lo).toNat =
        pow2 fmt.fracWidth + Model.fracField x := by
    rw [normalMantissa_toNat h _ _ hhigh, ← hfraction, pow2_eq_two_pow]
    ring
  have hexponentZeroNat : Model.expField x ≠ 0 := by
    rw [← hexponent]
    exact hexponentBounds.1.ne'
  have hexponentFiniteNat : Model.expField x ≠ fmt.expAllOnesNat := by
    rw [← hexponent]
    exact Nat.ne_of_lt hexponentBounds.2
  have hfinite : Model.isFinite x = true := by
    simp [Model.isFinite, h.encoding, Model.IEEE.isFinite, hexponentFiniteNat]
  unfold FiniteKernel.decodeOption
  rw [ite_eq_right (by simp [hfinite])]
  dsimp only
  unfold FiniteKernel.decodeMantissa
  rw [ite_eq_right (by simpa using hexponentZeroNat)]
  rw [← hexponent, ← hsign, hmantissa]

/-- Interpret normal finite-kernel components as their exact dyadic value. -/
theorem normalComponents_toDyadic (h : Eligible fmt)
    (sign : Bool) (exponent mantissa : Nat)
    (hexponent : exponent ≠ 0) (hmantissa : mantissa ≠ 0) :
    FiniteKernel.Components.toDyadic fmt {
        sign
        exponent
        mantissa } =
      { negative := sign
        significand := mantissa
        exponent := Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth) } := by
  simp [FiniteKernel.Components.toDyadic, FiniteKernel.dyadicExponent,
    hexponent, hmantissa, h.exponentBias_eq]
  omega

/-- Normalize the scale used by the product-round kernels. -/
theorem roundScaleExponent (h : Eligible fmt) (exponent : Nat) :
    Int.ofNat (exponent + (fmt.bias + fmt.fracWidth - 2)) -
        Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) =
      Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth) := by
  have hfrac := h.frac_gt
  unfold FloatFormat.ieeeSubnormalAlignExp
  simp only [Int.ofNat_eq_natCast]
  omega

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
