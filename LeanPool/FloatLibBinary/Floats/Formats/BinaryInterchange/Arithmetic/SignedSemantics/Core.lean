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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Correctness of binary sign operations

Negation usually changes only the stored sign bit. Formats with unsigned zero are the exception:
their would-be negative-zero word is a reserved NaN, so semantic negation preserves both that NaN
and the single zero encoding. This module separates raw sign toggling from policy-aware negation
and transports the latter through dyadic decoding to the real semantics.

## Reference

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Sections 3.4 and 5.5.1.
  https://doi.org/10.1109/IEEESTD.2019.8766229
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

private theorem ofWordNat_xor_signMask_eq_or
    (fmt : FloatFormat) (value : Nat)
    (hvalue : value < 2 ^ (FloatFormat.bitWidth fmt - 1)) :
    FloatFormat.ofWordNat fmt value ^^^ FloatFormat.signMask fmt =
      FloatFormat.signMask fmt ||| FloatFormat.ofWordNat fmt value := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or]
  by_cases hsign : i = fmt.bitWidth - 1
  · subst i
    have hvalueBit :
        (BitVec.ofNat fmt.bitWidth value).getLsbD
            (fmt.bitWidth - 1) = false := by
      rw [BitVec.getLsbD_ofNat]
      simp [hi, Nat.testBit_eq_false_of_lt hvalue]
    have hsignBit :
        (BitVec.ofNat fmt.bitWidth (2 ^ (fmt.bitWidth - 1))).getLsbD
            (fmt.bitWidth - 1) = true := by
      rw [BitVec.getLsbD_ofNat]
      simp [hi, Nat.testBit_two_pow_self]
    simp [FloatFormat.signMask, FloatFormat.ofWordNat,
      FloatFormat.signMaskNat, FloatFormat.signBitIndex, hvalueBit, hsignBit]
  · have hmask :
        (2 ^ (fmt.bitWidth - 1)).testBit i = false :=
      Nat.testBit_two_pow_of_ne (Ne.symm hsign)
    have hsignBit :
        (BitVec.ofNat fmt.bitWidth (2 ^ (fmt.bitWidth - 1))).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]
      simp [hi, hmask]
    simp [FloatFormat.signMask, FloatFormat.ofWordNat,
      FloatFormat.signMaskNat, FloatFormat.signBitIndex, hsignBit]

private theorem expMaskNat_lt_signMaskNat (fmt : FloatFormat) :
    FloatFormat.expMaskNat fmt < 2 ^ (FloatFormat.bitWidth fmt - 1) := by
  have hfracPower : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos fmt.fracWidth
  have hexponent :
      2 ^ fmt.expWidth - 1 < 2 ^ fmt.expWidth :=
    Nat.sub_lt (Nat.two_pow_pos fmt.expWidth) (by decide)
  unfold FloatFormat.expMaskNat FloatFormat.expAllOnesNat FloatFormat.bitWidth
  rw [show 1 + fmt.expWidth + fmt.fracWidth - 1 =
      fmt.expWidth + fmt.fracWidth by omega, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hexponent hfracPower

private theorem expMask_toNat (fmt : FloatFormat) :
    (FloatFormat.expMask fmt).toNat = FloatFormat.expMaskNat fmt := by
  unfold FloatFormat.expMask FloatFormat.ofWordNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact (expMaskNat_lt_signMaskNat fmt).trans <|
    Nat.pow_lt_pow_right (by decide) (Nat.sub_one_lt (by
      unfold FloatFormat.bitWidth
      omega))

private theorem expMask_ne_zero (fmt : FloatFormat) :
    FloatFormat.expMask fmt ≠ 0 := by
  intro hzero
  have hnat := congrArg BitVec.toNat hzero
  rw [expMask_toNat] at hnat
  have hpositive : 0 < FloatFormat.expMaskNat fmt := by
    simp [FloatFormat.expMaskNat, FloatFormat.expAllOnesNat_pos]
  simp at hnat
  omega

private theorem expMask_ne_signMask (fmt : FloatFormat) :
    FloatFormat.expMask fmt ≠ FloatFormat.signMask fmt := by
  intro hequal
  have hnat := congrArg BitVec.toNat hequal
  rw [expMask_toNat, FloatFormat.signMask_toNat] at hnat
  exact (Nat.ne_of_lt (expMaskNat_lt_signMaskNat fmt)) hnat

/-- Toggling an explicitly packed value changes only its supplied sign field. -/
@[simp] theorem toggleSign_ofFields (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) :
    toggleSign (ofFields fmt sign exponent fraction) =
      ofFields fmt (!sign) exponent fraction := by
  apply congrArg ofBits
  change mkBits fmt sign exponent fraction ^^^ FloatFormat.signMask fmt =
    mkBits fmt (!sign) exponent fraction
  unfold mkBits
  dsimp only
  unfold FloatFormat.signMask FloatFormat.signMaskNat FloatFormat.signBitIndex
    FloatFormat.expAllOnes FloatFormat.expAllOnesNat
    FloatFormat.fracMask FloatFormat.fracMaskNat FloatFormat.ofWordNat
  cases sign <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi
  all_goals
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
    by_cases hisign : i = fmt.bitWidth - 1
    · subst i
      have hnotFrac : ¬(fmt.bitWidth - 1 < fmt.fracWidth) := by
        unfold FloatFormat.bitWidth
        omega
      have hExpIndex : fmt.bitWidth - 1 - fmt.fracWidth = fmt.expWidth := by
        unfold FloatFormat.bitWidth
        omega
      have hmaskElem :
          (BitVec.ofNat fmt.bitWidth (2 ^ (fmt.bitWidth - 1)))[fmt.bitWidth - 1] =
            true := by
        rw [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_ofNat]
        simp [hi, Nat.testBit_two_pow_self]
      simp [hi, hnotFrac, hExpIndex, hmaskElem]
    · have hmask : (2 ^ (fmt.bitWidth - 1)).testBit i = false :=
        Nat.testBit_two_pow_of_ne (Ne.symm hisign)
      have hmaskElem :
          (BitVec.ofNat fmt.bitWidth (2 ^ (fmt.bitWidth - 1)))[i] = false := by
        rw [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_ofNat]
        simp [hi, hmask]
      simp [hi, hmask, hmaskElem]

/-- Packed-field negation toggles the supplied sign when the format represents signed zero. -/
theorem neg_ofFields_of_supportsSignedZero (fmt : FloatFormat)
    (hfmt : fmt.supportsSignedZero = true) (sign : Bool)
    (exponent fraction : Nat) :
    neg (ofFields fmt sign exponent fraction) =
      ofFields fmt (!sign) exponent fraction := by
  rw [neg_eq_toggleSign_of_supportsSignedZero _ hfmt, toggleSign_ofFields]

private theorem isNaN_toggleSign_eq_isZero_of_finiteUnsignedZero
    {fmt : FloatFormat} (hfmt : fmt.encoding = .finiteUnsignedZero)
    (x : Model fmt) :
    isNaN (toggleSign x) = isZero x := by
  simp only [isNaN, isZero, hfmt, toggleSign, ofBits]
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  simpa using
    (BitVec.xor_left_inj (x := x.bits) (y := 0) (FloatFormat.signMask fmt))

private theorem isZero_toggleSign_eq_isNaN_of_finiteUnsignedZero
    {fmt : FloatFormat} (hfmt : fmt.encoding = .finiteUnsignedZero)
    (x : Model fmt) :
    isZero (toggleSign x) = isNaN x := by
  simp only [isNaN, isZero, hfmt, toggleSign, ofBits]
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  exact BitVec.xor_eq_zero_iff

/-- Copying a sign never changes the fraction field. -/
@[simp] theorem fracField_copySign {fmt : FloatFormat}
    (magnitude signSource : Model fmt) :
    fracField (copySign magnitude signSource) = fracField magnitude := by
  unfold copySign
  split
  · rfl
  · split
    · rfl
    · simp

/-- Copying a sign never changes the exponent field. -/
@[simp] theorem expField_copySign {fmt : FloatFormat}
    (magnitude signSource : Model fmt) :
    expField (copySign magnitude signSource) = expField magnitude := by
  unfold copySign
  split
  · rfl
  · split
    · rfl
    · simp

/-- In a signed-zero format, `copySign` gives the magnitude the source's sign. -/
theorem signBit_copySign_of_supportsSignedZero
    {fmt : FloatFormat} (magnitude signSource : Model fmt)
    (hfmt : fmt.supportsSignedZero = true) :
    signBit (copySign magnitude signSource) = signBit signSource := by
  cases hmagnitude : signBit magnitude <;>
    cases hsource : signBit signSource <;>
    simp [copySign, hfmt, hmagnitude, hsource]

/-- Copying a sign preserves NaN classification under every format policy. -/
@[simp] theorem isNaN_copySign {fmt : FloatFormat}
    (magnitude signSource : Model fmt) :
    isNaN (copySign magnitude signSource) = isNaN magnitude := by
  cases hencoding : fmt.encoding with
  | ieee | finiteMaxNaN | finite =>
      by_cases hsign : signBit magnitude = signBit signSource
      · simp [copySign, isNaN, hencoding,
          FloatFormat.supportsSignedZero, hsign]
      · rw [show copySign magnitude signSource = toggleSign magnitude by
          simp [copySign, hencoding, FloatFormat.supportsSignedZero, hsign]]
        simp [isNaN, hencoding]
  | finiteUnsignedZero =>
      have hunsigned : fmt.supportsSignedZero = false := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      by_cases hnan : isNaN magnitude = true
      · rw [copySign_eq_self_of_not_supportsSignedZero_of_isNaN
          magnitude signSource hunsigned hnan]
      · have hnanFalse := Bool.eq_false_of_not_eq_true hnan
        by_cases hzero : isZero magnitude = true
        · rw [copySign_eq_self_of_not_supportsSignedZero_of_isZero
            magnitude signSource hunsigned hzero]
        · have hzeroFalse := Bool.eq_false_of_not_eq_true hzero
          by_cases hsign : signBit magnitude = signBit signSource
          · simp [copySign, hunsigned, hnanFalse, hzeroFalse, hsign]
          · rw [show copySign magnitude signSource = toggleSign magnitude by
                simp [copySign, hunsigned, hnanFalse, hzeroFalse, hsign],
              isNaN_toggleSign_eq_isZero_of_finiteUnsignedZero hencoding,
              hzeroFalse, hnanFalse]

/-- Copying a sign preserves zero classification under every format policy. -/
@[simp] theorem isZero_copySign {fmt : FloatFormat}
    (magnitude signSource : Model fmt) :
    isZero (copySign magnitude signSource) = isZero magnitude := by
  cases hencoding : fmt.encoding with
  | ieee | finiteMaxNaN | finite =>
      by_cases hsign : signBit magnitude = signBit signSource
      · simp [copySign, isZero, hencoding,
          FloatFormat.supportsSignedZero, hsign]
      · rw [show copySign magnitude signSource = toggleSign magnitude by
          simp [copySign, hencoding, FloatFormat.supportsSignedZero, hsign]]
        simp [isZero, hencoding]
  | finiteUnsignedZero =>
      have hunsigned : fmt.supportsSignedZero = false := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      by_cases hzero : isZero magnitude = true
      · rw [copySign_eq_self_of_not_supportsSignedZero_of_isZero
          magnitude signSource hunsigned hzero]
      · have hzeroFalse := Bool.eq_false_of_not_eq_true hzero
        by_cases hnan : isNaN magnitude = true
        · rw [copySign_eq_self_of_not_supportsSignedZero_of_isNaN
            magnitude signSource hunsigned hnan]
        · have hnanFalse := Bool.eq_false_of_not_eq_true hnan
          by_cases hsign : signBit magnitude = signBit signSource
          · simp [copySign, hunsigned, hnanFalse, hzeroFalse, hsign]
          · rw [show copySign magnitude signSource = toggleSign magnitude by
                simp [copySign, hunsigned, hnanFalse, hzeroFalse, hsign],
              isZero_toggleSign_eq_isNaN_of_finiteUnsignedZero hencoding,
              hnanFalse, hzeroFalse]

/-- Copying a sign preserves infinity classification. -/
@[simp] theorem isInf_copySign {fmt : FloatFormat}
    (magnitude signSource : Model fmt) :
    isInf (copySign magnitude signSource) = isInf magnitude := by
  cases hencoding : fmt.encoding with
  | ieee =>
      by_cases hsign : signBit magnitude = signBit signSource
      · simp [copySign, isInf, hencoding,
          FloatFormat.supportsSignedZero, hsign]
      · rw [show copySign magnitude signSource = toggleSign magnitude by
          simp [copySign, hencoding, FloatFormat.supportsSignedZero, hsign]]
        simp [isInf, hencoding]
  | finiteMaxNaN | finite | finiteUnsignedZero =>
      simp [isInf, hencoding]

/-- Copying a sign preserves finiteness. -/
@[simp] theorem isFinite_copySign {fmt : FloatFormat}
    (magnitude signSource : Model fmt) :
    isFinite (copySign magnitude signSource) = isFinite magnitude := by
  cases hencoding : fmt.encoding with
  | ieee =>
      by_cases hsign : signBit magnitude = signBit signSource
      · simp [copySign, isFinite, hencoding,
          FloatFormat.supportsSignedZero, hsign]
      · rw [show copySign magnitude signSource = toggleSign magnitude by
          simp [copySign, hencoding, FloatFormat.supportsSignedZero, hsign]]
        simp [isFinite, hencoding]
  | finiteMaxNaN | finite | finiteUnsignedZero =>
      simp [isFinite, hencoding]

/-- Absolute value preserves NaN classification. -/
@[simp] theorem isNaN_abs {fmt : FloatFormat} (x : Model fmt) :
    isNaN (abs x) = isNaN x := by
  simp [abs]

/-- Absolute value preserves zero classification. -/
@[simp] theorem isZero_abs {fmt : FloatFormat} (x : Model fmt) :
    isZero (abs x) = isZero x := by
  simp [abs]

/-- Absolute value preserves infinity classification. -/
@[simp] theorem isInf_abs {fmt : FloatFormat} (x : Model fmt) :
    isInf (abs x) = isInf x := by
  simp [abs]

/-- Absolute value preserves finiteness. -/
@[simp] theorem isFinite_abs {fmt : FloatFormat} (x : Model fmt) :
    isFinite (abs x) = isFinite x := by
  simp [abs]

/-- In a signed-zero format, absolute value clears the stored sign. -/
theorem signBit_abs_of_supportsSignedZero
    {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.supportsSignedZero = true) :
    signBit (abs x) = false := by
  simpa [abs] using
    signBit_copySign_of_supportsSignedZero
      x (posZero fmt) hfmt

/-- Policy-aware negation is involutive for every supported encoding. -/
@[simp] theorem neg_neg {fmt : FloatFormat} (x : Model fmt) :
    neg (neg x) = x := by
  cases hencoding : fmt.encoding with
  | ieee | finiteMaxNaN | finite =>
      simp [neg, FloatFormat.supportsSignedZero, hencoding]
  | finiteUnsignedZero =>
      have hunsigned : fmt.supportsSignedZero = false := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      by_cases hnan : isNaN x = true
      · have hx := neg_eq_self_of_not_supportsSignedZero_of_isNaN
          x hunsigned hnan
        rw [hx, hx]
      · have hnanFalse : isNaN x = false := Bool.eq_false_of_not_eq_true hnan
        by_cases hzero : isZero x = true
        · have hx := neg_eq_self_of_not_supportsSignedZero_of_isZero
            x hunsigned hzero
          rw [hx, hx]
        · have hzeroFalse : isZero x = false := Bool.eq_false_of_not_eq_true hzero
          have hnanToggle : isNaN (toggleSign x) = false := by
            rw [isNaN_toggleSign_eq_isZero_of_finiteUnsignedZero hencoding, hzeroFalse]
          have hzeroToggle : isZero (toggleSign x) = false := by
            rw [isZero_toggleSign_eq_isNaN_of_finiteUnsignedZero hencoding, hnanFalse]
          rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
            x hnanFalse hzeroFalse]
          rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
            (toggleSign x) hnanToggle hzeroToggle]
          exact toggleSign_toggleSign x

/-- Negation maps positive zero to the format's policy-selected negative zero. -/
@[simp] theorem neg_posZero (fmt : FloatFormat) :
    neg (posZero fmt) = zero fmt true := by
  cases hencoding : fmt.encoding <;>
    simp [neg, zero, FloatFormat.supportsSignedZero, hencoding,
      isNaN, isZero, posZero, negZero,
      ofNatBits, ofBits, FloatFormat.ofWordNat, toggleSign]

/-- Negation maps negative zero to positive zero when negative zero is representable. -/
theorem neg_negZero_of_supportsSignedZero (fmt : FloatFormat)
    (hfmt : fmt.supportsSignedZero = true) :
    neg (negZero fmt) = posZero fmt := by
  have hpos : neg (posZero fmt) = negZero fmt := by
    simp [zero, hfmt]
  rw [← hpos, neg_neg]

/-- Raw sign toggling exchanges the positive and negative IEEE infinity bit patterns. -/
private theorem toggleSign_posInf (fmt : FloatFormat) :
    toggleSign (posInf fmt) = negInf fmt := by
  apply congrArg ofBits
  change FloatFormat.expMask fmt ^^^ FloatFormat.signMask fmt =
    FloatFormat.signMask fmt ||| FloatFormat.expMask fmt
  exact ofWordNat_xor_signMask_eq_or
    fmt (FloatFormat.expMaskNat fmt) (expMaskNat_lt_signMaskNat fmt)

/-- Negation exchanges the positive and negative IEEE infinity bit patterns in every encoding. -/
@[simp] theorem neg_posInf (fmt : FloatFormat) :
    neg (posInf fmt) = negInf fmt := by
  have hexponent :
      expField (posInf fmt) = fmt.expAllOnesNat := by
    rw [posInf_eq_ofModel_infinity]
    exact expField_ofModel_infinity fmt .positive
  have hfraction : fracField (posInf fmt) = 0 := by
    rw [posInf_eq_ofModel_infinity]
    exact fracField_ofModel_infinity fmt .positive
  have hnan : isNaN (posInf fmt) = false := by
    cases hencoding : fmt.encoding with
    | ieee =>
        simp [isNaN, hencoding, IEEE.isNaN, hexponent, hfraction]
    | finiteMaxNaN =>
        have hfracMask : (0 : Nat) ≠ fmt.fracMaskNat :=
          (FloatFormat.fracMaskNat_pos fmt).ne
        simp [isNaN, hencoding, hexponent, hfraction, hfracMask]
    | finiteUnsignedZero =>
        have hbits :
            (posInf fmt).bits ≠ FloatFormat.signMask fmt := by
          change FloatFormat.expMask fmt ≠ FloatFormat.signMask fmt
          exact expMask_ne_signMask fmt
        simp [isNaN, hencoding, hbits]
    | finite =>
        simp [isNaN, hencoding]
  have hzero : isZero (posInf fmt) = false := by
    cases hencoding : fmt.encoding with
    | ieee | finiteMaxNaN | finite =>
        have hexponentNe : fmt.expAllOnesNat ≠ 0 :=
          (FloatFormat.expAllOnesNat_pos fmt).ne'
        simp [isZero, hencoding, IEEE.isZero, hexponent, hfraction,
          hexponentNe]
    | finiteUnsignedZero =>
        have hbits : (posInf fmt).bits ≠ 0 := by
          change FloatFormat.expMask fmt ≠ 0
          exact expMask_ne_zero fmt
        simp only [isZero, hencoding]
        exact (beq_eq_false_iff_ne).2 hbits
  rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
    (posInf fmt) hnan hzero, toggleSign_posInf]

/-- Negation maps the negative IEEE infinity bit pattern to the positive pattern. -/
@[simp] theorem neg_negInf (fmt : FloatFormat) :
    neg (negInf fmt) = posInf fmt := by
  rw [← neg_posInf fmt, neg_neg]

/-- Raw sign toggling maps the least positive subnormal to its negative counterpart. -/
private theorem toggleSign_posMinSubnormal (fmt : FloatFormat) :
    toggleSign (posMinSubnormal fmt) = negMinSubnormal fmt := by
  apply congrArg ofBits
  change FloatFormat.ofWordNat fmt 1 ^^^ FloatFormat.signMask fmt =
    FloatFormat.signMask fmt ||| FloatFormat.ofWordNat fmt 1
  apply ofWordNat_xor_signMask_eq_or
  exact Nat.one_lt_two_pow (by
    have hexponent := fmt.expWidth_ge_two
    have hfraction := fmt.fracWidth_pos
    unfold FloatFormat.bitWidth
    omega)

/-- The least positive subnormal has sign zero. -/
@[simp] theorem signBit_posMinSubnormal (fmt : FloatFormat) :
    signBit (posMinSubnormal fmt) = false := by
  rw [posMinSubnormal_eq_ofFields]
  simp

/-- The least positive subnormal is finite in every supported encoding. -/
@[simp] theorem isFinite_posMinSubnormal (fmt : FloatFormat) :
    isFinite (posMinSubnormal fmt) = true := by
  have hfraction : 1 < 2 ^ fmt.fracWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos)
  have hexponentNe : (0 : Nat) ≠ fmt.expAllOnesNat :=
    (FloatFormat.expAllOnesNat_pos fmt).ne
  rw [posMinSubnormal_eq_ofFields,
    isFinite_ofFields fmt false 0 1 (by positivity) hfraction]
  cases hencoding : fmt.encoding <;>
    simp [hexponentNe]

/-- The least positive subnormal is nonzero. -/
@[simp] theorem isZero_posMinSubnormal (fmt : FloatFormat) :
    isZero (posMinSubnormal fmt) = false := by
  have hfraction : 1 < 2 ^ fmt.fracWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos)
  rw [posMinSubnormal_eq_ofFields,
    isZero_ofFields fmt false 0 1 (by positivity) hfraction]
  cases hencoding : fmt.encoding <;> simp

/-- The least positive subnormal is not a NaN. -/
@[simp] theorem isNaN_posMinSubnormal (fmt : FloatFormat) :
    isNaN (posMinSubnormal fmt) = false :=
  isNaN_eq_false_of_isFinite_eq_true _ (isFinite_posMinSubnormal fmt)

/-- The least positive subnormal is not an infinity. -/
@[simp] theorem isInf_posMinSubnormal (fmt : FloatFormat) :
    isInf (posMinSubnormal fmt) = false :=
  isInf_eq_false_of_isFinite_eq_true _ (isFinite_posMinSubnormal fmt)

/-- The negative subnormal of least magnitude is explicit field packing with fraction one. -/
theorem negMinSubnormal_eq_ofFields (fmt : FloatFormat) :
    negMinSubnormal fmt = ofFields fmt true 0 1 := by
  calc
    negMinSubnormal fmt = toggleSign (posMinSubnormal fmt) :=
      (toggleSign_posMinSubnormal fmt).symm
    _ = toggleSign (ofFields fmt false 0 1) := by
      rw [posMinSubnormal_eq_ofFields]
    _ = ofFields fmt true 0 1 := by simp

/-- The negative subnormal of least magnitude has sign one. -/
@[simp] theorem signBit_negMinSubnormal (fmt : FloatFormat) :
    signBit (negMinSubnormal fmt) = true := by
  rw [negMinSubnormal_eq_ofFields]
  simp

/-- The negative subnormal of least magnitude is finite in every supported encoding. -/
@[simp] theorem isFinite_negMinSubnormal (fmt : FloatFormat) :
    isFinite (negMinSubnormal fmt) = true := by
  have hfraction : 1 < 2 ^ fmt.fracWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos)
  have hexponentNe : (0 : Nat) ≠ fmt.expAllOnesNat :=
    (FloatFormat.expAllOnesNat_pos fmt).ne
  rw [negMinSubnormal_eq_ofFields,
    isFinite_ofFields fmt true 0 1 (by positivity) hfraction]
  cases hencoding : fmt.encoding <;>
    simp [hexponentNe]

/-- The negative subnormal of least magnitude is nonzero. -/
@[simp] theorem isZero_negMinSubnormal (fmt : FloatFormat) :
    isZero (negMinSubnormal fmt) = false := by
  have hfraction : 1 < 2 ^ fmt.fracWidth :=
    Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos)
  rw [negMinSubnormal_eq_ofFields,
    isZero_ofFields fmt true 0 1 (by positivity) hfraction]
  cases hencoding : fmt.encoding <;> simp

/-- The negative subnormal of least magnitude is not a NaN. -/
@[simp] theorem isNaN_negMinSubnormal (fmt : FloatFormat) :
    isNaN (negMinSubnormal fmt) = false :=
  isNaN_eq_false_of_isFinite_eq_true _ (isFinite_negMinSubnormal fmt)

/-- The negative subnormal of least magnitude is not an infinity. -/
@[simp] theorem isInf_negMinSubnormal (fmt : FloatFormat) :
    isInf (negMinSubnormal fmt) = false :=
  isInf_eq_false_of_isFinite_eq_true _ (isFinite_negMinSubnormal fmt)

/-- Negation maps the least positive subnormal to its negative counterpart. -/
@[simp] theorem neg_posMinSubnormal (fmt : FloatFormat) :
    neg (posMinSubnormal fmt) = negMinSubnormal fmt := by
  rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
    (posMinSubnormal fmt) (isNaN_posMinSubnormal fmt)
    (isZero_posMinSubnormal fmt), toggleSign_posMinSubnormal]

/-- Negation maps the negative subnormal of least magnitude to its positive counterpart. -/
@[simp] theorem neg_negMinSubnormal (fmt : FloatFormat) :
    neg (negMinSubnormal fmt) = posMinSubnormal fmt := by
  rw [← neg_posMinSubnormal fmt, neg_neg]

/-- The largest finite encoding carries exactly the requested sign. -/
@[simp] theorem signBit_maxFinite (fmt : FloatFormat) (sign : Bool) :
    signBit (maxFinite fmt sign) = sign := by
  simp [maxFinite]

/-- A largest finite encoding is never zero. -/
@[simp] theorem isZero_maxFinite (fmt : FloatFormat) (sign : Bool) :
    isZero (maxFinite fmt sign) = false := by
  rw [maxFinite, isZero_ofFields fmt sign fmt.maxFiniteExpField
    fmt.maxFiniteFracField fmt.maxFiniteExpField_lt_two_pow
    fmt.maxFiniteFracField_lt_two_pow]
  cases hencoding : fmt.encoding <;>
    simp [Nat.ne_of_gt fmt.maxFiniteExpField_pos]

/-- A largest finite encoding is never a NaN. -/
@[simp] theorem isNaN_maxFinite (fmt : FloatFormat) (sign : Bool) :
    isNaN (maxFinite fmt sign) = false :=
  isNaN_eq_false_of_isFinite_eq_true _ (isFinite_maxFinite fmt sign)

/-- A largest finite encoding is never an infinity. -/
@[simp] theorem isInf_maxFinite (fmt : FloatFormat) (sign : Bool) :
    isInf (maxFinite fmt sign) = false :=
  isInf_eq_false_of_isFinite_eq_true _ (isFinite_maxFinite fmt sign)

/-- Negation toggles the sign of the largest finite magnitude. -/
@[simp] theorem neg_maxFinite (fmt : FloatFormat) (sign : Bool) :
    neg (maxFinite fmt sign) = maxFinite fmt (!sign) := by
  rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
    (maxFinite fmt sign) (isNaN_maxFinite fmt sign)
    (isZero_maxFinite fmt sign)]
  simp [maxFinite, toggleSign_ofFields]

/-- Negation maps the largest positive finite value to its negative counterpart. -/
@[simp] theorem neg_posMaxFinite (fmt : FloatFormat) :
    neg (posMaxFinite fmt) = negMaxFinite fmt := by
  simp [posMaxFinite, negMaxFinite]

/-- Negation maps the most negative finite value to its positive counterpart. -/
@[simp] theorem neg_negMaxFinite (fmt : FloatFormat) :
    neg (negMaxFinite fmt) = posMaxFinite fmt := by
  simp [posMaxFinite, negMaxFinite]

/-- Negation preserves NaN classification, including the reserved NaN of unsigned-zero formats. -/
@[simp] theorem isNaN_neg {fmt : FloatFormat} (x : Model fmt) :
    isNaN (neg x) = isNaN x := by
  cases hencoding : fmt.encoding with
  | ieee | finiteMaxNaN | finite =>
      simp [neg, FloatFormat.supportsSignedZero, hencoding, isNaN]
  | finiteUnsignedZero =>
      have hunsigned : fmt.supportsSignedZero = false := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      by_cases hnan : isNaN x = true
      · rw [neg_eq_self_of_not_supportsSignedZero_of_isNaN x hunsigned hnan]
      · have hnanFalse : isNaN x = false := Bool.eq_false_of_not_eq_true hnan
        by_cases hzero : isZero x = true
        · rw [neg_eq_self_of_not_supportsSignedZero_of_isZero x hunsigned hzero]
        · have hzeroFalse : isZero x = false := Bool.eq_false_of_not_eq_true hzero
          rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
            x hnanFalse hzeroFalse]
          rw [isNaN_toggleSign_eq_isZero_of_finiteUnsignedZero hencoding, hzeroFalse]
          exact hnanFalse.symm

/-- Negation preserves infinity classification. -/
@[simp] theorem isInf_neg {fmt : FloatFormat} (x : Model fmt) :
    isInf (neg x) = isInf x := by
  cases hencoding : fmt.encoding <;>
    simp [isInf, hencoding, neg, FloatFormat.supportsSignedZero]

/-- Negation preserves zero classification. -/
@[simp] theorem isZero_neg {fmt : FloatFormat} (x : Model fmt) :
    isZero (neg x) = isZero x := by
  cases hencoding : fmt.encoding with
  | ieee | finiteMaxNaN | finite =>
      simp [neg, FloatFormat.supportsSignedZero, hencoding, isZero]
  | finiteUnsignedZero =>
      have hunsigned : fmt.supportsSignedZero = false := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      by_cases hnan : isNaN x = true
      · have hzeroFalse : isZero x = false := by
          cases hzero : isZero x
          · rfl
          · have hfinite := isFinite_eq_true_of_isZero_eq_true x hzero
            have hnanFalse := isNaN_eq_false_of_isFinite_eq_true x hfinite
            rw [hnan] at hnanFalse
            contradiction
        rw [neg_eq_self_of_not_supportsSignedZero_of_isNaN x hunsigned hnan]
      · have hnanFalse : isNaN x = false := Bool.eq_false_of_not_eq_true hnan
        by_cases hzero : isZero x = true
        · rw [neg_eq_self_of_not_supportsSignedZero_of_isZero x hunsigned hzero]
        · have hzeroFalse : isZero x = false := Bool.eq_false_of_not_eq_true hzero
          rw [neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
            x hnanFalse hzeroFalse]
          rw [isZero_toggleSign_eq_isNaN_of_finiteUnsignedZero hencoding, hnanFalse]
          exact hzeroFalse.symm

/-- Negation preserves finiteness. -/
@[simp] theorem isFinite_neg {fmt : FloatFormat} (x : Model fmt) :
    isFinite (neg x) = isFinite x := by
  cases hencoding : fmt.encoding <;>
    simp [isFinite, hencoding, isNaN_neg]

/-- Flipping the sign flag of a dyadic negates its real value, including for zero significands. -/
@[simp] theorem Numerics.Dyadic.toReal_mk_not_negative (d : Numerics.Dyadic) :
    (Numerics.Dyadic.mk (!d.negative) d.significand d.exponent).toReal = -d.toReal := by
  cases hs : d.negative <;> simp [Numerics.Dyadic.toReal, hs]

/-- Policy-aware negation decodes to exact dyadic negation with the format's zero convention. -/
theorem toDyadicOption_neg_of_toDyadicOption_some {fmt : FloatFormat} (x : Model fmt) {d :
  Numerics.Dyadic}
    (hx : toDyadicOption x = some d) :
    toDyadicOption (neg x) = some (negDyadic fmt d) := by
  have hfinite : isFinite x = true := by
    rw [← toDyadicOption_isSome_eq_isFinite x, hx]
    rfl
  have hnan : isNaN x = false :=
    isNaN_eq_false_of_toDyadicOption_some hx
  cases hencoding : fmt.encoding with
  | ieee =>
      have hsignedZero : fmt.supportsSignedZero = true := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      have hneg : neg x = toggleSign x :=
        neg_eq_toggleSign_of_supportsSignedZero x hsignedZero
      by_cases hieee : fmt.isIEEE = true
      · have hdecode : ieeeToDyadicOption x = some d := by
          simpa [toDyadicOption, hieee] using hx
        rw [hneg]
        simpa [negDyadic, hsignedZero, toDyadicOption, hieee] using
          ieeeToDyadicOption_toggleSign_of_ieeeToDyadicOption_some x hdecode
      · have hfiniteNeg : isFinite (neg x) = true := by
          simpa using hfinite
        by_cases hexponent : expField x = 0 <;> by_cases hfraction : fracField x = 0 <;>
          · simp_all only [toDyadicOption, Bool.false_eq_true, ↓reduceIte, Bool.not_true, isZero,
            IEEE.isZero, BEq.rfl, Bool.and_self, Option.some.injEq, Bool.not_eq_true,
            expField_toggleSign, fracField_toggleSign, signBit_toggleSign, negDyadic,
            Bool.and_false, Numerics.Dyadic.neg_eq, Numerics.Dyadic.mk.injEq,
            Bool.not_eq_eq_eq_not, Bool.not_not, Bool.true_and, beq_iff_eq, Bool.and_true,
            add_zero, Int.ofNat_eq_natCast, Bool.and_eq_true, and_self]
            exact Numerics.Dyadic.mk.inj hx
  | finiteMaxNaN =>
      have hsignedZero : fmt.supportsSignedZero = true := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      have hneg : neg x = toggleSign x :=
        neg_eq_toggleSign_of_supportsSignedZero x hsignedZero
      have hieee : fmt.isIEEE = false := by
        simp [FloatFormat.isIEEE, hencoding]
      have hfiniteNeg : isFinite (neg x) = true := by
        simpa using hfinite
      by_cases hexponent : expField x = 0 <;> by_cases hfraction : fracField x = 0 <;>
        · simp_all only [toDyadicOption, Bool.false_eq_true, ↓reduceIte, Bool.not_true, isZero,
          IEEE.isZero, BEq.rfl, Bool.and_self, Option.some.injEq, expField_toggleSign,
          fracField_toggleSign, signBit_toggleSign, negDyadic, Bool.and_false,
          Numerics.Dyadic.neg_eq, Numerics.Dyadic.mk.injEq, Bool.not_eq_eq_eq_not, Bool.not_not,
          Bool.true_and, beq_iff_eq, Bool.and_true, add_zero, Int.ofNat_eq_natCast,
          Bool.and_eq_true, and_self]
          exact Numerics.Dyadic.mk.inj hx
  | finiteUnsignedZero =>
      have hunsigned : fmt.supportsSignedZero = false := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      by_cases hzero : isZero x = true
      · have hneg : neg x = x :=
          neg_eq_self_of_not_supportsSignedZero_of_isZero x hunsigned hzero
        have hbits : x.bits = 0 := by
          simpa [isZero, hencoding] using hzero
        have hsign : signBit x = false := by
          unfold signBit
          rw [hbits]
          simp
        have hdecode := toDyadicOption_eq_zero_of_isZero_eq_true x hzero
        rw [hx] at hdecode
        have hd : d = { negative := false, significand := 0, exponent := 0 } := by
          have := Option.some.inj hdecode
          simpa [hsign] using this
        rw [hneg, hx, hd]
        simp [negDyadic, hunsigned, Numerics.Dyadic.zero]
      · have hzeroFalse : isZero x = false :=
          Bool.eq_false_of_not_eq_true hzero
        have hneg : neg x = toggleSign x :=
          neg_eq_toggleSign_of_isNaN_eq_false_of_isZero_eq_false
            x hnan hzeroFalse
        have hieee : fmt.isIEEE = false := by
          simp [FloatFormat.isIEEE, hencoding]
        have hfiniteNeg : isFinite (neg x) = true := by
          simpa using hfinite
        by_cases hexponent : expField x = 0
        · by_cases hfraction : fracField x = 0
          · have hreconstruct := ofFields_signBit_expField_fracField x
            cases hsign : signBit x
            · have hzero' : isZero x = true := by
                rw [hexponent, hfraction, hsign] at hreconstruct
                rw [← hreconstruct, ofFields_false_zero_zero]
                simp
              exact (hzero hzero').elim
            · have hnan' : isNaN x = true := by
                rw [hexponent, hfraction, hsign] at hreconstruct
                rw [← hreconstruct, ofFields_true_zero_zero]
                simpa [negZero] using
                  signMask_isNaN_of_encoding_finiteUnsignedZero hencoding
              simp [hnan] at hnan'
          · have hzeroNeg : isZero (neg x) = false := by
              simpa using hzeroFalse
            simp_all [toDyadicOption, negDyadic]
            cases hx
            simp [hfraction]
        · have hzeroNeg : isZero (neg x) = false := by
            simpa using hzeroFalse
          simp_all [toDyadicOption, negDyadic]
          cases hx
          simp [pow2_eq_two_pow]
  | finite =>
      have hsignedZero : fmt.supportsSignedZero = true := by
        simp [FloatFormat.supportsSignedZero, hencoding]
      have hneg : neg x = toggleSign x :=
        neg_eq_toggleSign_of_supportsSignedZero x hsignedZero
      have hieee : fmt.isIEEE = false := by
        simp [FloatFormat.isIEEE, hencoding]
      have hfiniteNeg : isFinite (neg x) = true := by
        simpa using hfinite
      by_cases hexponent : expField x = 0 <;> by_cases hfraction : fracField x = 0 <;>
        · simp_all only [toDyadicOption, Bool.false_eq_true, ↓reduceIte, Bool.not_true, isZero,
          IEEE.isZero, BEq.rfl, Bool.and_self, Option.some.injEq, isNaN, expField_toggleSign,
          fracField_toggleSign, signBit_toggleSign, negDyadic, Bool.and_false,
          Numerics.Dyadic.neg_eq, Numerics.Dyadic.mk.injEq, Bool.not_eq_eq_eq_not, Bool.not_not,
          Bool.true_and, beq_iff_eq, Bool.and_true, add_zero, Int.ofNat_eq_natCast,
          Bool.and_eq_true, and_self]
          exact Numerics.Dyadic.mk.inj hx

/-- Format-aware dyadic negation is real-number negation. -/
@[simp] theorem Numerics.Dyadic.toReal_negDyadic (fmt : FloatFormat) (d : Numerics.Dyadic) :
    (negDyadic fmt d).toReal = -d.toReal := by
  by_cases hmant : d.significand = 0
  · cases hsignedZero : fmt.supportsSignedZero <;>
      simp [negDyadic, hmant, hsignedZero, Numerics.Dyadic.toReal]
  · simp [negDyadic, hmant]

/-- On finite values, executable policy negation is real-number negation. -/
@[simp] theorem toReal_neg {fmt : FloatFormat} (x : Model fmt)
    (hx : isFinite x = true) :
    toReal (neg x) = -toReal x := by
  obtain ⟨d, hd⟩ := exists_toDyadicOption_of_isFinite hx
  have hneg := toDyadicOption_neg_of_toDyadicOption_some x hd
  rw [toReal_eq, hneg, toReal_eq, hd]
  exact Numerics.Dyadic.toReal_negDyadic fmt d

end Model
end FloatLib.Floats.Formats.BinaryInterchange
