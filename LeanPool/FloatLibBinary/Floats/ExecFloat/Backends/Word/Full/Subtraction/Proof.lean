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

public import Std.Tactic.BVDecide
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Subtraction.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof

/-!
# Verified exact subtraction for nearby binary64 values

Sterbenz's lemma guarantees exact representability for subtraction of finite floating-point
values with the same sign and magnitudes within a factor of two. This module proves a positive
normal-input core,
then handles negative operands by negating and swapping them. It computes the exact significand
difference in `UInt64` and packs it without entering the arbitrary-precision generic addition
kernel.

Every rejected input retains the existing exact generic implementation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

/-! ## Bit-level bridges for finite binary64 values -/

private theorem toUInt64_negate (x : Value) :
    toUInt64 (negate x) = toUInt64 x ^^^ 0x8000000000000000 := by
  cases x
  rfl

private theorem expField_xor_sign (bits : UInt64) :
    expField (bits ^^^ 0x8000000000000000) = expField bits := by
  apply UInt64.toNat_inj.mp
  change
    (expField (toUInt64 (negate (ofUInt64 bits)))).toNat =
      (expField (toUInt64 (ofUInt64 bits))).toNat
  rw [expField_toNat, expField_toNat, negate_eq, Model.expField_neg]

private theorem fracField_xor_sign (bits : UInt64) :
    fracField (bits ^^^ 0x8000000000000000) = fracField bits := by
  apply UInt64.toNat_inj.mp
  change
    (fracField (toUInt64 (negate (ofUInt64 bits)))).toNat =
      (fracField (toUInt64 (ofUInt64 bits))).toNat
  rw [fracField_toNat, fracField_toNat, negate_eq, Model.fracField_neg]

private theorem signBit_xor_sign (bits : UInt64) :
    signBit (bits ^^^ 0x8000000000000000) = !signBit bits := by
  change
    signBit (toUInt64 (negate (ofUInt64 bits))) =
      !signBit (toUInt64 (ofUInt64 bits))
  rw [signBit_eq, signBit_eq, negate_eq, Model.signBit_neg]
  simp [FloatFormat.supportsSignedZero, FloatFormat.binary64]

private theorem decode_negate_of_finiteExponent (x : Value)
    (hfinite : expField (toUInt64 x) ≠ 0x7ff) :
    decodeOption (negate x) =
      some {
        sign := !signBit (toUInt64 x)
        exponent := (expField (toUInt64 x)).toNat
        mantissa :=
          (finiteMantissa (expField (toUInt64 x))
            (fracField (toUInt64 x))).toNat } := by
  simp only [decodeOption, toUInt64_negate]
  rw [expField_xor_sign, fracField_xor_sign, signBit_xor_sign]
  simp [hfinite]

private theorem addFiniteImpl_negate_eq_components
    (x y : Value)
    (hxfinite : expField (toUInt64 x) ≠ 0x7ff)
    (hyfinite : expField (toUInt64 y) ≠ 0x7ff) :
    addFiniteImplOption x (negate y) =
      some (FiniteKernel.addComponents FloatFormat.binary64
        {
          sign := signBit (toUInt64 x)
          exponent := (expField (toUInt64 x)).toNat
          mantissa :=
            (finiteMantissa (expField (toUInt64 x))
              (fracField (toUInt64 x))).toNat }
        {
          sign := !signBit (toUInt64 y)
          exponent := (expField (toUInt64 y)).toNat
          mantissa :=
            (finiteMantissa (expField (toUInt64 y))
              (fracField (toUInt64 y))).toNat }) := by
  unfold addFiniteImplOption
  rw [decode_of_finiteExponent x hxfinite,
    decode_negate_of_finiteExponent y hyfinite]
  simp only [FiniteKernel.addComponentsImpl_eq]

@[simp] private theorem binary64_bias :
    FloatFormat.binary64.bias = 1023 := by
  decide

@[simp] private theorem binary64_align :
    FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64 = 1074 := by
  decide

/-! ## Exact finite-difference packing -/

private def packExactDifferenceSpec
    (sign : Bool) (difference exponent : Nat) : Value :=
  if difference = 0 then
    Model.posZero FloatFormat.binary64
  else if difference.log2 + exponent < 53 then
    Model.ofFields FloatFormat.binary64 sign 0
      (difference <<< (exponent - 1))
  else
    let shift := 52 - difference.log2
    let mantissa := difference <<< shift
    let encodedExponent := exponent + difference.log2 - 52
    Model.ofFields FloatFormat.binary64 sign encodedExponent
      (mantissa - 2 ^ 52)

private theorem packExactDifference_eq_spec_subnormal
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < 2047)
    (hsubnormal : difference.log2 + exponent < 53) :
    packExactDifference sign difference exponent =
      packExactDifferenceSpec sign difference.toNat exponent.toNat := by
  have hzeroNat : difference.toNat ≠ 0 := by
    simpa [uint64_toNat_eq_zero] using hdifference
  have hleading : difference.log2.toNat = difference.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat difference
  have hleadingLt : difference.log2.toNat < 53 :=
    log2_toNat_lt_of_toNat_lt_two_pow difference 53
      hdifference hdifferenceFit
  have hpositionFit :
      difference.log2.toNat + exponent.toNat < 2 ^ 64 := by
    have hsmall :
        difference.log2.toNat + exponent.toNat < 2100 := by
      omega
    exact lt_trans hsmall (by norm_num)
  have hposition :
      (difference.log2 + exponent).toNat =
        difference.log2.toNat + exponent.toNat :=
    uint64_add_toNat_of_lt difference.log2 exponent hpositionFit
  have hsubnormalNat :
      difference.toNat.log2 + exponent.toNat < 53 := by
    have hnative := UInt64.lt_iff_toNat_lt.mp hsubnormal
    rw [hposition, hleading] at hnative
    simpa using hnative
  unfold packExactDifference packExactDifferenceSpec
  simp only [beq_iff_eq, hdifference, hzeroNat, ite_false,
    hsubnormal, hsubnormalNat, ite_true]
  have hexponentWord : (1 : UInt64) ≤ exponent := by
    apply UInt64.le_iff_toNat_le.mpr
    simp
    omega
  have hwordShift :
      (exponent - 1).toNat = exponent.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le exponent 1 hexponentWord]
    simp
  have hshiftLt : exponent.toNat - 1 < 64 := by
    omega
  have hfractionFit :
      difference.toNat <<< (exponent.toNat - 1) < 2 ^ 64 := by
    have hbound :
        difference.toNat.log2 + 1 + (exponent.toNat - 1) < 53 := by
      omega
    exact lt_trans
      (Nat.shiftLeft_lt (m := exponent.toNat - 1) Nat.lt_log2_self)
      (Nat.pow_lt_pow_right (by decide) (by omega))
  have hnativeFraction :
      (difference <<< (exponent - 1)).toNat =
        difference.toNat <<< (exponent.toNat - 1) := by
    rw [UInt64.toNat_shiftLeft, hwordShift,
      Nat.mod_eq_of_lt hshiftLt, Nat.mod_eq_of_lt hfractionFit]
  have hnativeFractionWord :
      difference <<< (exponent - 1) =
        UInt64.ofNat
          (difference.toNat <<< (exponent.toNat - 1)) := by
    apply UInt64.toNat_inj.mp
    rw [hnativeFraction]
    exact (UInt64.toNat_ofNat_of_lt hfractionFit).symm
  rw [hnativeFractionWord]
  exact packFieldsWord_eq_ofNat sign 0 _

private theorem normalizedMantissa_toNat
    (difference : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53) :
    (difference <<< (52 - difference.log2)).toNat =
      difference.toNat <<< (52 - difference.toNat.log2) := by
  have hleading : difference.log2.toNat = difference.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat difference
  have hleadingLt : difference.log2.toNat < 53 :=
    log2_toNat_lt_of_toNat_lt_two_pow difference 53
      hdifference hdifferenceFit
  have hleadingLe : difference.log2 ≤ (52 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    change difference.log2.toNat ≤ 52
    omega
  have hshift :
      ((52 : UInt64) - difference.log2).toNat =
        52 - difference.toNat.log2 := by
    rw [UInt64.toNat_sub_of_le _ _ hleadingLe, hleading]
    rfl
  have hshiftLt : 52 - difference.toNat.log2 < 64 := by
    omega
  have hmantissaFit :
      difference.toNat <<< (52 - difference.toNat.log2) < 2 ^ 64 := by
    exact lt_trans
      (Nat.shiftLeft_lt (m := 52 - difference.toNat.log2)
        Nat.lt_log2_self)
      (Nat.pow_lt_pow_right (by decide) (by omega))
  rw [UInt64.toNat_shiftLeft, hshift,
    Nat.mod_eq_of_lt hshiftLt, Nat.mod_eq_of_lt hmantissaFit]

private theorem encodedExponent_word
    (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentFinite : exponent.toNat < 2047)
    (hnormal : ¬difference.log2 + exponent < 53) :
    exponent + difference.log2 - 52 =
      UInt64.ofNat
        (exponent.toNat + difference.toNat.log2 - 52) := by
  have hleading : difference.log2.toNat = difference.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat difference
  have hleadingLt : difference.log2.toNat < 53 :=
    log2_toNat_lt_of_toNat_lt_two_pow difference 53
      hdifference hdifferenceFit
  have haddFit :
      exponent.toNat + difference.log2.toNat < 2 ^ 64 := by
    have hsmall : exponent.toNat + difference.log2.toNat < 2100 := by
      omega
    exact lt_trans hsmall (by norm_num)
  have hadd :
      (exponent + difference.log2).toNat =
        exponent.toNat + difference.toNat.log2 := by
    have h := uint64_add_toNat_of_lt exponent difference.log2 haddFit
    simpa only [hleading] using h
  have hpositionFit :
      difference.log2.toNat + exponent.toNat < 2 ^ 64 := by
    simpa only [Nat.add_comm] using haddFit
  have hposition :
      (difference.log2 + exponent).toNat =
        difference.toNat.log2 + exponent.toNat := by
    rw [uint64_add_toNat_of_lt difference.log2 exponent hpositionFit, hleading]
  have hnormalNat :
      53 ≤ difference.toNat.log2 + exponent.toNat := by
    by_contra hlt
    apply hnormal
    apply UInt64.lt_iff_toNat_lt.mpr
    change (difference.log2 + exponent).toNat < 53
    rw [hposition]
    omega
  have h52 : (52 : UInt64) ≤ exponent + difference.log2 := by
    apply UInt64.le_iff_toNat_le.mpr
    change 52 ≤ (exponent + difference.log2).toNat
    rw [hadd]
    omega
  have hencodedFit :
      exponent.toNat + difference.toNat.log2 - 52 < 2 ^ 64 := by
    have hsmall :
        exponent.toNat + difference.toNat.log2 - 52 < 2100 := by
      omega
    exact lt_trans hsmall (by norm_num)
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ h52, hadd]
  exact (UInt64.toNat_ofNat_of_lt hencodedFit).symm

private theorem uint64_sub_eq_ofNat
    (x y : UInt64) (hle : y ≤ x)
    (hfit : x.toNat - y.toNat < 2 ^ 64) :
    x - y = UInt64.ofNat (x.toNat - y.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ hle]
  exact (UInt64.toNat_ofNat_of_lt hfit).symm

private theorem normalizedFraction_word
    (difference : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53) :
    difference <<< (52 - difference.log2) -
        0x0010000000000000 =
      UInt64.ofNat
        (difference.toNat <<< (52 - difference.toNat.log2) -
          2 ^ 52) := by
  have hzeroNat : difference.toNat ≠ 0 := by
    simpa [uint64_toNat_eq_zero] using hdifference
  have hleading : difference.log2.toNat = difference.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat difference
  have hleadingLt : difference.log2.toNat < 53 :=
    log2_toNat_lt_of_toNat_lt_two_pow difference 53
      hdifference hdifferenceFit
  have hleadingNatLe : difference.toNat.log2 ≤ 52 := by
    rw [← hleading]
    omega
  have hnativeMantissa :=
    normalizedMantissa_toNat difference hdifference hdifferenceFit
  have hmantissaLower :
      2 ^ 52 ≤ difference.toNat <<< (52 - difference.toNat.log2) := by
    exact two_pow_le_shiftLeft_sub_log2 52 difference.toNat hzeroNat hleadingNatLe
  have hbaseWord :
      (0x0010000000000000 : UInt64) ≤
        difference <<< (52 - difference.log2) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hnativeMantissa]
    simpa using hmantissaLower
  have hfractionFit :
      difference.toNat <<< (52 - difference.toNat.log2) - 2 ^ 52 <
        2 ^ 64 := by
    have hmantissaUpper :
        difference.toNat <<< (52 - difference.toNat.log2) < 2 ^ 53 := by
      exact shiftLeft_sub_log2_lt_two_pow 52 difference.toNat hleadingNatLe
    exact lt_trans (Nat.sub_lt_of_lt hmantissaUpper) (by norm_num)
  rw [uint64_sub_eq_ofNat _ _ hbaseWord (by
    rw [hnativeMantissa]
    norm_num
    exact hfractionFit)]
  rw [hnativeMantissa]
  congr 1

private theorem packExactDifference_eq_spec_normal
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < 2047)
    (hnormal : ¬difference.log2 + exponent < 53) :
    packExactDifference sign difference exponent =
      packExactDifferenceSpec sign difference.toNat exponent.toNat := by
  have hzeroNat : difference.toNat ≠ 0 := by
    simpa [uint64_toNat_eq_zero] using hdifference
  have hleading : difference.log2.toNat = difference.toNat.log2 :=
    FloatLib.Numerics.FixedWord.log2_toNat difference
  have hpositionFit :
      difference.log2.toNat + exponent.toNat < 2 ^ 64 := by
    have hsmall :
        difference.log2.toNat + exponent.toNat < 2100 := by
      have hleadingLt :=
        log2_toNat_lt_of_toNat_lt_two_pow difference 53
          hdifference hdifferenceFit
      omega
    exact lt_trans hsmall (by norm_num)
  have hposition :
      (difference.log2 + exponent).toNat =
        difference.log2.toNat + exponent.toNat :=
    uint64_add_toNat_of_lt difference.log2 exponent hpositionFit
  have hnormalNat :
      ¬difference.toNat.log2 + exponent.toNat < 53 := by
    intro h
    apply hnormal
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hposition, hleading]
    simpa using h
  unfold packExactDifference packExactDifferenceSpec
  simp only [beq_iff_eq, hdifference, hzeroNat, ite_false,
    hnormal, hnormalNat, ite_false]
  rw [encodedExponent_word difference exponent hdifference hdifferenceFit
      hexponentFinite hnormal,
    normalizedFraction_word difference hdifference hdifferenceFit]
  exact packFieldsWord_eq_ofNat sign
    (exponent.toNat + difference.toNat.log2 - 52)
    (difference.toNat <<< (52 - difference.toNat.log2) - 2 ^ 52)

private theorem packExactDifference_eq_spec
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < 2047) :
    packExactDifference sign difference exponent =
      packExactDifferenceSpec sign difference.toNat exponent.toNat := by
  by_cases hsubnormal : difference.log2 + exponent < 53
  · exact packExactDifference_eq_spec_subnormal sign difference exponent
      hdifference hdifferenceFit hexponentPositive hexponentFinite hsubnormal
  · exact packExactDifference_eq_spec_normal sign difference exponent
      hdifference hdifferenceFit hexponentPositive hexponentFinite hsubnormal

private theorem packExactDifferenceSpec_eq_round
    (sign : Bool) (difference exponent : Nat)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference < 2 ^ 53)
    (hexponentPositive : 0 < exponent)
    (hexponentFinite : exponent < 2047) :
    packExactDifferenceSpec sign difference exponent =
      FiniteProductRound.round FloatFormat.binary64 sign difference
        (exponent + 1073) := by
  have hleadingLt : difference.log2 < 53 := by
    rw [Nat.log2_lt]
    · exact hdifferenceFit
    · exact hdifference
  unfold packExactDifferenceSpec FiniteProductRound.round
  simp only [beq_iff_eq, hdifference, ite_false]
  by_cases hsubnormal : difference.log2 + exponent < 53
  · have hgenericSubnormal :
        difference.log2 + (exponent + 1073) <
          FloatFormat.binary64.bias +
            2 * FloatFormat.binary64.fracWidth - 1 := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [ite_eq_left hsubnormal, ite_eq_left hgenericSubnormal]
    have hscaleNotSmall :
        ¬exponent + 1073 <
          FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64 := by
      simp only [binary64_align]
      omega
    rw [ite_eq_right hscaleNotSmall]
    have hshift :
        exponent + 1073 -
            FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64 =
          exponent - 1 := by
      simp only [binary64_align]
      omega
    rw [hshift]
    have hfractionPositive :
        difference <<< (exponent - 1) ≠ 0 := by
      simp [hdifference]
    have hfractionLt :
        difference <<< (exponent - 1) < 2 ^ 52 := by
      have hbound :
          difference.log2 + 1 + (exponent - 1) ≤ 52 := by
        omega
      exact lt_of_lt_of_le
        (Nat.shiftLeft_lt (m := exponent - 1) Nat.lt_log2_self)
        (Nat.pow_le_pow_right (n := 2) (by decide) hbound)
    simp only [hfractionPositive, ite_false]
    have hfractionNotBase :
        difference <<< (exponent - 1) ≠
          Model.pow2 FloatFormat.binary64.fracWidth := by
      simp only [binary64_fracWidth, Model.pow2_eq_two_pow]
      exact ne_of_lt hfractionLt
    simp only [hfractionNotBase, ite_false]
  · have hgenericNormal :
        ¬difference.log2 + (exponent + 1073) <
          FloatFormat.binary64.bias +
            2 * FloatFormat.binary64.fracWidth - 1 := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [ite_eq_right hsubnormal, ite_eq_right hgenericNormal]
    have hleadingLe : difference.log2 ≤ 52 := by
      omega
    have hgenericRounded :
        (if FloatFormat.binary64.fracWidth ≤ difference.log2 then
            Numerics.roundShiftRightEven difference
              (difference.log2 - FloatFormat.binary64.fracWidth)
          else
            difference <<<
              (FloatFormat.binary64.fracWidth - difference.log2)) =
          difference <<< (52 - difference.log2) := by
      simp only [binary64_fracWidth]
      by_cases htop : difference.log2 = 52
      · simp [htop]
      · have hsmall : difference.log2 < 52 := by
          omega
        simp [Nat.not_le_of_lt hsmall]
    rw [hgenericRounded]
    have hcarry :
        difference <<< (52 - difference.log2) ≠
          Model.pow2 (FloatFormat.binary64.fracWidth + 1) := by
      have hupper :=
        shiftLeft_sub_log2_lt_two_pow 52 difference hleadingLe
      simp only [binary64_fracWidth, Model.pow2_eq_two_pow]
      omega
    simp only [hcarry, ite_false]
    have hoverflow :
        ¬3 * FloatFormat.binary64.bias +
              2 * FloatFormat.binary64.fracWidth - 2 <
            difference.log2 + (exponent + 1073) := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [ite_eq_right hoverflow]
    have hencoded :
        difference.log2 + (exponent + 1073) -
            (FloatFormat.binary64.bias +
              2 * FloatFormat.binary64.fracWidth - 2) =
          exponent + difference.log2 - 52 := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [hencoded]
    simp only [binary64_fracWidth, Model.pow2_eq_two_pow]

/-- Exact native difference packing agrees with the generic unsigned-scale rounder. -/
theorem packExactDifference_eq_round
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < 2047) :
    packExactDifference sign difference exponent =
      FiniteProductRound.round FloatFormat.binary64 sign difference.toNat
        (exponent.toNat + 1073) := by
  rw [packExactDifference_eq_spec sign difference exponent hdifference
    hdifferenceFit hexponentPositive hexponentFinite]
  exact packExactDifferenceSpec_eq_round sign difference.toNat exponent.toNat
    (by simpa [uint64_toNat_eq_zero] using hdifference)
    hdifferenceFit hexponentPositive hexponentFinite

/-! ## Sterbenz exactness in the dyadic model -/

private theorem addDyadic_pos_neg_adjacent_left
    (large small : Nat) (exponent : Int)
    (hlarge : large ≠ 0) (hsmall : small ≠ 0)
    (hlt : small < large <<< 1) :
    addDyadic
        { negative := false, significand := large, exponent := exponent + 1 }
        { negative := true, significand := small, exponent := exponent } =
      { negative := false, significand := (large <<< 1) - small, exponent := exponent } := by
  exact addDyadic_oppositeSign_adjacentExponent_largeLeft
    false true large small exponent hlarge hsmall (by decide) hlt

private theorem addDyadic_pos_neg_adjacent_right
    (small large : Nat) (exponent : Int)
    (hsmall : small ≠ 0) (hlarge : large ≠ 0)
    (hlt : small < large <<< 1) :
    addDyadic
        { negative := false, significand := small, exponent := exponent }
        { negative := true, significand := large, exponent := exponent + 1 } =
      { negative := true, significand := (large <<< 1) - small, exponent := exponent } := by
  exact addDyadic_oppositeSign_adjacentExponent_largeRight
    false true small large exponent hsmall hlarge (by decide) hlt

/-! ## Component-level binary64 subtraction -/

private theorem addComponents_same_large_left
    (large small exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlt : small < large) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa := large }
        { sign := true, exponent, mantissa := small } =
      FiniteProductRound.round FloatFormat.binary64 false (large - small)
        (exponent + 1073) := by
  have hlarge : large ≠ 0 := by omega
  unfold FiniteKernel.addComponents
  rw [← roundDyadic_eq_roundDyadicImpl,
    normalComponents_toDyadic false exponent large hexponent hlarge,
    normalComponents_toDyadic true exponent small hexponent hsmall,
    addDyadic_oppositeSign_sameExponent_largeLeft false true large small
      (Int.ofNat exponent - 1075) hlarge hsmall (by decide) hlt,
    FiniteProductRound.round_eq_roundDyadic FloatFormat.binary64 (by decide)]
  rw [roundScaleExponent]

private theorem addComponents_same_equal
    (mantissa exponent : Nat)
    (hexponent : exponent ≠ 0) (hmantissa : mantissa ≠ 0) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa }
        { sign := true, exponent, mantissa } =
      packExactDifference false 0 (UInt64.ofNat exponent) := by
  unfold FiniteKernel.addComponents
  rw [normalComponents_toDyadic false exponent mantissa
      hexponent hmantissa,
    normalComponents_toDyadic true exponent mantissa
      hexponent hmantissa]
  rw [show addDyadic
      { negative := false, significand := mantissa, exponent := Int.ofNat exponent - 1075 }
      { negative := true, significand := mantissa, exponent := Int.ofNat exponent - 1075 } =
        { negative := false, significand := 0, exponent := 0 } by
      exact addDyadic_oppositeSign_sameExponent_eq_zero
        false true mantissa (Int.ofNat exponent - 1075)
        hmantissa (by decide)]
  rfl

private theorem addComponents_same_large_right
    (small large exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlt : small < large) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa := small }
        { sign := true, exponent, mantissa := large } =
      FiniteProductRound.round FloatFormat.binary64 true (large - small)
        (exponent + 1073) := by
  have hlarge : large ≠ 0 := by omega
  unfold FiniteKernel.addComponents
  rw [← roundDyadic_eq_roundDyadicImpl,
    normalComponents_toDyadic false exponent small hexponent hsmall,
    normalComponents_toDyadic true exponent large hexponent hlarge,
    addDyadic_oppositeSign_sameExponent_largeRight false true small large
      (Int.ofNat exponent - 1075) hsmall hlarge (by decide) hlt,
    FiniteProductRound.round_eq_roundDyadic FloatFormat.binary64 (by decide)]
  rw [roundScaleExponent]

private theorem addComponents_adjacent_large_left
    (large small exponent : Nat)
    (hexponent : exponent ≠ 0) (hlarge : large ≠ 0)
    (hsmall : small ≠ 0) (hlt : small < large <<< 1) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent := exponent + 1, mantissa := large }
        { sign := true, exponent, mantissa := small } =
      FiniteProductRound.round FloatFormat.binary64 false
        ((large <<< 1) - small) (exponent + 1073) := by
  have hexponentSucc : exponent + 1 ≠ 0 := by omega
  have hexponentShift :
      Int.ofNat (exponent + 1) - 1075 =
        (Int.ofNat exponent - 1075) + 1 := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  unfold FiniteKernel.addComponents
  rw [← roundDyadic_eq_roundDyadicImpl,
    normalComponents_toDyadic false (exponent + 1) large
      hexponentSucc hlarge,
    normalComponents_toDyadic true exponent small hexponent hsmall,
    hexponentShift,
    addDyadic_pos_neg_adjacent_left large small
      (Int.ofNat exponent - 1075) hlarge hsmall hlt,
    FiniteProductRound.round_eq_roundDyadic FloatFormat.binary64 (by decide)]
  rw [roundScaleExponent]

private theorem addComponents_adjacent_large_right
    (small large exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlarge : large ≠ 0) (hlt : small < large <<< 1) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa := small }
        { sign := true, exponent := exponent + 1, mantissa := large } =
      FiniteProductRound.round FloatFormat.binary64 true
        ((large <<< 1) - small) (exponent + 1073) := by
  have hexponentSucc : exponent + 1 ≠ 0 := by omega
  have hexponentShift :
      Int.ofNat (exponent + 1) - 1075 =
        (Int.ofNat exponent - 1075) + 1 := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  unfold FiniteKernel.addComponents
  rw [← roundDyadic_eq_roundDyadicImpl,
    normalComponents_toDyadic false exponent small hexponent hsmall,
    normalComponents_toDyadic true (exponent + 1) large
      hexponentSucc hlarge,
    hexponentShift,
    addDyadic_pos_neg_adjacent_right small large
      (Int.ofNat exponent - 1075) hsmall hlarge hlt,
    FiniteProductRound.round_eq_roundDyadic FloatFormat.binary64 (by decide)]
  rw [roundScaleExponent]

private theorem adjacentDifference_facts (upper lower : UInt64)
    (hupper : 2 ^ 52 ≤ upper.toNat ∧ upper.toNat < 2 ^ 53)
    (hlower : 2 ^ 52 ≤ lower.toNat ∧ lower.toNat < 2 ^ 53)
    (hle : upper ≤ lower) :
    lower.toNat < upper.toNat <<< 1 ∧
      ((upper <<< 1) - lower).toNat = (upper.toNat <<< 1) - lower.toNat ∧
      (upper <<< 1) - lower ≠ 0 ∧
      ((upper <<< 1) - lower).toNat < 2 ^ 53 := by
  have hshiftFit : upper.toNat <<< 1 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hshift : (upper <<< 1).toNat = upper.toNat <<< 1 := by
    simpa using shiftLeft_toNat upper 1 (by norm_num) hshiftFit
  have hlt : lower.toNat < upper.toNat <<< 1 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hword : lower ≤ upper <<< 1 :=
    UInt64.le_iff_toNat_le.mpr (by rw [hshift]; exact hlt.le)
  have hdifference :
      ((upper <<< 1) - lower).toNat = (upper.toNat <<< 1) - lower.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hword, hshift]
  refine ⟨hlt, hdifference, ?_, ?_⟩
  · intro hzero
    have hzeroNat := congrArg UInt64.toNat hzero
    rw [hdifference] at hzeroNat
    simp only [UInt64.toNat_zero] at hzeroNat
    omega
  · have hleNat := UInt64.le_iff_toNat_le.mp hle
    rw [hdifference, Nat.shiftLeft_eq]
    norm_num
    omega

private theorem sterbenzExponentCases (x y result : Value) :
  let xBits := toUInt64 x;
  let yBits := toUInt64 y;
  let xExponent := expField xBits;
  let yExponent := expField yBits;
  let xFraction := fracField xBits;
  let yFraction := fracField yBits;
  let xMantissa := finiteMantissa xExponent xFraction;
  let yMantissa := finiteMantissa yExponent yFraction;
  2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 →
    2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 →
      0 < xExponent.toNat →
        0 < yExponent.toNat →
          xExponent.toNat < 2047 →
            yExponent.toNat < 2047 →
              (if xExponent = yExponent then
                    if yMantissa ≤ xMantissa then some (packExactDifference false (xMantissa -
                      yMantissa) xExponent)
                    else some (packExactDifference true (yMantissa - xMantissa) xExponent)
                  else
                    if xExponent = yExponent + 1 ∧ xMantissa ≤ yMantissa then
                      some (packExactDifference false (xMantissa <<< 1 - yMantissa) yExponent)
                    else
                      if yExponent = xExponent + 1 ∧ yMantissa ≤ xMantissa then
                        some (packExactDifference true (yMantissa <<< 1 - xMantissa) xExponent)
                      else none) =
                  some result →
                some
                    (FiniteKernel.addComponents FloatFormat.binary64
                      { sign := false, exponent := xExponent.toNat, mantissa := xMantissa.toNat }
                      { sign := true, exponent := yExponent.toNat, mantissa := yMantissa.toNat }) =
                  some result := by
  intro xBits yBits xExponent yExponent xFraction yFraction xMantissa yMantissa hxMantissaBounds
    hyMantissaBounds hxExponentPositive hyExponentPositive hxExponentFinite hyExponentFinite
    hfast
  by_cases hsame : xExponent = yExponent
  · simp only [hsame, ↓reduceIte] at hfast
    by_cases hle : yMantissa ≤ xMantissa
    · rw [ite_eq_left hle] at hfast
      have hresult := Option.some.inj hfast
      subst result
      by_cases hequal : xMantissa = yMantissa
      · rw [← hsame, ← hequal]
        rw [addComponents_same_equal xMantissa.toNat xExponent.toNat
          hxExponentPositive.ne' (by omega)]
        have hexponentRoundtrip :
            UInt64.ofNat xExponent.toNat = xExponent := by
          exact UInt64.ofNat_toNat
        rw [hexponentRoundtrip]
        simp [packExactDifference]
      · have hleNat : yMantissa.toNat ≤ xMantissa.toNat :=
          UInt64.le_iff_toNat_le.mp hle
        have hneNat : yMantissa.toNat ≠ xMantissa.toNat := by
          intro h
          apply hequal
          apply UInt64.toNat_inj.mp
          exact h.symm
        have hltNat : yMantissa.toNat < xMantissa.toNat :=
          Nat.lt_of_le_of_ne hleNat hneNat
        rw [← hsame]
        rw [addComponents_same_large_left
          xMantissa.toNat yMantissa.toNat xExponent.toNat
          hxExponentPositive.ne' (by omega) hltNat]
        rw [packExactDifference_eq_round false
          (xMantissa - yMantissa) xExponent]
        · rw [UInt64.toNat_sub_of_le _ _ hle]
        · intro hzero
          have := congrArg UInt64.toNat hzero
          rw [UInt64.toNat_sub_of_le _ _ hle] at this
          simp at this
          omega
        · rw [UInt64.toNat_sub_of_le _ _ hle]
          omega
        · exact hxExponentPositive
        · exact hxExponentFinite
    · rw [ite_eq_right hle] at hfast
      have hresult := Option.some.inj hfast
      subst result
      have hltNat : xMantissa.toNat < yMantissa.toNat := by
        have hnotLeNat : ¬yMantissa.toNat ≤ xMantissa.toNat := by
          intro hleNat
          apply hle
          exact UInt64.le_iff_toNat_le.mpr hleNat
        omega
      have hxyLe : xMantissa ≤ yMantissa :=
        UInt64.le_iff_toNat_le.mpr hltNat.le
      rw [← hsame]
      rw [addComponents_same_large_right
        xMantissa.toNat yMantissa.toNat xExponent.toNat
        hxExponentPositive.ne' (by omega) hltNat]
      rw [packExactDifference_eq_round true
        (yMantissa - xMantissa) xExponent]
      · rw [UInt64.toNat_sub_of_le _ _ hxyLe]
      · intro hzero
        have := congrArg UInt64.toNat hzero
        rw [UInt64.toNat_sub_of_le _ _ hxyLe] at this
        simp at this
        omega
      · rw [UInt64.toNat_sub_of_le _ _ hxyLe]
        omega
      · exact hxExponentPositive
      · exact hxExponentFinite
  · by_cases hleft :
        xExponent = yExponent + 1 ∧ xMantissa ≤ yMantissa
    · have hleftCondition := hleft
      rcases hleft with ⟨hxAdjacent, hxyMantissa⟩
      simp only [ite_eq_right hsame, ite_eq_left hleftCondition] at hfast
      have hresult := Option.some.inj hfast
      subst result
      have hxExponentNat :
          xExponent.toNat = yExponent.toNat + 1 := by
        rw [hxAdjacent, uint64_add_toNat_of_lt]
        · rfl
        · norm_num
          exact lt_trans (Nat.add_lt_add_right hyExponentFinite 1)
            (by norm_num)
      obtain ⟨hyLtShiftNat, hdifferenceNat, hdifferenceNonzero, hdifferenceFit⟩ :=
        adjacentDifference_facts xMantissa yMantissa
          hxMantissaBounds hyMantissaBounds hxyMantissa
      rw [hxExponentNat]
      rw [addComponents_adjacent_large_left
        xMantissa.toNat yMantissa.toNat yExponent.toNat
        hyExponentPositive.ne' (by omega) (by omega) hyLtShiftNat]
      rw [packExactDifference_eq_round false
        ((xMantissa <<< 1) - yMantissa) yExponent
        hdifferenceNonzero hdifferenceFit
        hyExponentPositive hyExponentFinite]
      rw [hdifferenceNat]
    · by_cases hright :
          yExponent = xExponent + 1 ∧ yMantissa ≤ xMantissa
      · have hrightCondition := hright
        rcases hright with ⟨hyAdjacent, hyxMantissa⟩
        simp only [ite_eq_right hsame, ite_eq_right hleft,
          ite_eq_left hrightCondition] at hfast
        have hresult := Option.some.inj hfast
        subst result
        have hyExponentNat :
            yExponent.toNat = xExponent.toNat + 1 := by
          rw [hyAdjacent, uint64_add_toNat_of_lt]
          · rfl
          · norm_num
            exact lt_trans (Nat.add_lt_add_right hxExponentFinite 1)
              (by norm_num)
        obtain ⟨hxLtShiftNat, hdifferenceNat, hdifferenceNonzero, hdifferenceFit⟩ :=
          adjacentDifference_facts yMantissa xMantissa
            hyMantissaBounds hxMantissaBounds hyxMantissa
        rw [hyExponentNat]
        rw [addComponents_adjacent_large_right
          xMantissa.toNat yMantissa.toNat xExponent.toNat
          hxExponentPositive.ne' (by omega) (by omega) hxLtShiftNat]
        rw [packExactDifference_eq_round true
          ((yMantissa <<< 1) - xMantissa) xExponent
          hdifferenceNonzero hdifferenceFit
          hxExponentPositive hxExponentFinite]
        rw [hdifferenceNat]
      · simp [hsame, hleft, hright] at hfast

/--
Every accepted Sterbenz result is exactly the existing finite binary64 subtraction path.

The theorem is the trust boundary for the specialization: rejected inputs retain
`addFiniteImplOption x (negate y)`, while an accepted native result is bit-for-bit identical to it.
-/
theorem subSterbenz_refines (x y result : Value)
    (hfast : subSterbenzOption x y = some result) :
    addFiniteImplOption x (negate y) = some result := by
  unfold subSterbenzOption at hfast
  dsimp only at hfast
  set xBits := toUInt64 x with hxBits
  set yBits := toUInt64 y with hyBits
  set xExponent := expField xBits with hxExponent
  set yExponent := expField yBits with hyExponent
  set xFraction := fracField xBits with hxFraction
  set yFraction := fracField yBits with hyFraction
  set xMantissa := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa := finiteMantissa yExponent yFraction with hyMantissa
  by_cases hxSign : signBit xBits = true
  · simp [hxSign] at hfast
  have hxSignFalse : signBit xBits = false := by
    cases h : signBit xBits <;> simp_all
  by_cases hySign : signBit yBits = true
  · simp [hxSignFalse, hySign] at hfast
  have hySignFalse : signBit yBits = false := by
    cases h : signBit yBits <;> simp_all
  by_cases hxExponentZero : xExponent = 0
  · simp [hxSignFalse, hySignFalse, hxExponentZero] at hfast
  by_cases hyExponentZero : yExponent = 0
  · simp [hxSignFalse, hySignFalse, hyExponentZero] at hfast
  by_cases hxExponentExceptional : xExponent = 0x7ff
  · simp [hxSignFalse, hySignFalse, hxExponentExceptional] at hfast
  by_cases hyExponentExceptional : yExponent = 0x7ff
  · simp [hxSignFalse, hySignFalse, hyExponentExceptional] at hfast
  have hxFractionFit : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits, hxBits] using fracField_lt x
  have hyFractionFit : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits, hyBits] using fracField_lt y
  have hxBounds :=
    finiteMantissa_bounds xExponent xFraction
      hxExponentZero hxFractionFit
  have hyBounds :=
    finiteMantissa_bounds yExponent yFraction
      hyExponentZero hyFractionFit
  have hxMantissaBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [hxMantissa] using hxBounds
  have hyMantissaBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [hyMantissa] using hyBounds
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xExponent, xBits, hxBits] using
      normalExponent_bounds x
        (by simpa [xExponent, xBits, hxBits] using hxExponentZero)
        (by
          simpa [xExponent, xBits, hxBits] using
            hxExponentExceptional)
  have hyExponentBounds :
      0 < yExponent.toNat ∧ yExponent.toNat < 2047 := by
    simpa [yExponent, yBits, hyBits] using
      normalExponent_bounds y
        (by simpa [yExponent, yBits, hyBits] using hyExponentZero)
        (by
          simpa [yExponent, yBits, hyBits] using
            hyExponentExceptional)
  have hxExponentPositive : 0 < xExponent.toNat :=
    hxExponentBounds.1
  have hyExponentPositive : 0 < yExponent.toNat :=
    hyExponentBounds.1
  have hxExponentFinite : xExponent.toNat < 2047 :=
    hxExponentBounds.2
  have hyExponentFinite : yExponent.toNat < 2047 :=
    hyExponentBounds.2
  have hxFiniteWord :
      expField (toUInt64 x) ≠ 0x7ff := by
    simpa [xExponent, xBits, hxBits] using hxExponentExceptional
  have hyFiniteWord :
      expField (toUInt64 y) ≠ 0x7ff := by
    simpa [yExponent, yBits, hyBits] using hyExponentExceptional
  simp only [hxSignFalse, hySignFalse, Bool.or_self, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    hxExponentZero,
    hyExponentZero, or_self, hxExponentExceptional, hyExponentExceptional, ↓reduceIte,
      Bool.and_eq_true,
    decide_eq_true_eq] at hfast
  rw [addFiniteImpl_negate_eq_components x y hxFiniteWord hyFiniteWord]
  rw [← hxBits, ← hyBits, ← hxExponent, ← hyExponent, ← hxFraction,
    ← hyFraction, ← hxMantissa, ← hyMantissa, hxSignFalse, hySignFalse]
  simp only [Bool.not_false]
  exact sterbenzExponentCases (x := x) (y := y) (result := result) hxMantissaBounds
    hyMantissaBounds hxExponentPositive hyExponentPositive hxExponentFinite hyExponentFinite
    hfast

/--
Every accepted signed Sterbenz result is exactly the existing finite subtraction path.

The negative case reuses the positive theorem after negating and swapping both inputs, then uses
commutativity of exact finite addition.
-/
theorem subSignedSterbenz_refines (x y result : Value)
    (hfast : subSignedSterbenzOption x y = some result) :
    addFiniteImplOption x (negate y) = some result := by
  unfold subSignedSterbenzOption at hfast
  dsimp only at hfast
  cases hxSign : signBit (toUInt64 x) <;>
    cases hySign : signBit (toUInt64 y)
  · exact subSterbenz_refines x y result (by simpa [hxSign, hySign] using hfast)
  · simp [hxSign, hySign] at hfast
  · simp [hxSign, hySign] at hfast
  · have hnegative :
        subSterbenzOption (negate y) (negate x) = some result := by
      simpa [hxSign, hySign] using hfast
    have hrefines :=
      subSterbenz_refines (negate y) (negate x) result hnegative
    rw [negate_negate] at hrefines
    calc
      addFiniteImplOption x (negate y) =
          addFiniteImplOption (negate y) x := addFiniteImpl_comm _ _
      _ = some result := hrefines

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
