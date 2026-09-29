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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.RealSemantics

/-!
# Packing special values in Lean's float model

These packing identities preserve the sign of zero and infinity in Lean's IEEE model. They apply
to arbitrary field widths; descriptor-level classification additionally requires the relevant
encoding support. In particular, `negZero` is a NaN word under FNUZ, and `posInf` and `negInf` need
not denote infinities under finite-only policies.

The shared lemmas let operation proofs handle zero and overflow results without unfolding their
exponent and significand fields.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model
open Float.Model.UnpackedFloat

private theorem one_lt_two_pow_expWidth (fmt : FloatFormat) :
    1 < 2 ^ fmt.expWidth := by
  have hfour : 4 ≤ 2 ^ fmt.expWidth := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      fmt.expWidth_ge_two
  omega

private theorem expAllOnes_lt_two_pow (fmt : FloatFormat) :
    2 ^ fmt.expWidth - 1 < 2 ^ fmt.expWidth := by
  have hpos : 0 < 2 ^ fmt.expWidth := Nat.pow_pos (by decide)
  omega

private theorem expMaskNat_lt_two_pow_bitWidth (fmt : FloatFormat) :
    FloatFormat.expMaskNat fmt < 2 ^ fmt.bitWidth := by
  unfold FloatFormat.expMaskNat FloatFormat.expAllOnesNat FloatFormat.bitWidth
  have hfracPos : 0 < 2 ^ fmt.fracWidth := Nat.pow_pos (by decide)
  have hones : 2 ^ fmt.expWidth - 1 < 2 ^ fmt.expWidth :=
    expAllOnes_lt_two_pow fmt
  have hmaskLt :
      (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth <
        2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
    Nat.mul_lt_mul_of_pos_right hones hfracPos
  have hproductPos : 0 < 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
    mul_pos (Nat.pow_pos (by decide)) hfracPos
  rw [show 2 ^ (1 + fmt.expWidth + fmt.fracWidth) =
    2 * 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth by ring]
  nlinarith

/-- Packing and unpacking an infinity preserves its sign. -/
@[simp] theorem unpack_pack_infinity (spec : Format) (sign : Sign) :
    Float.Model.UnpackedFloat.unpack spec
        (Float.Model.UnpackedFloat.pack spec (.infinity sign)) =
      .infinity sign := by
  unfold Float.Model.UnpackedFloat.pack packedInfinity
    Float.Model.UnpackedFloat.unpack
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents]
  have hsign : Sign.ofBitVec sign.toBitVec = sign := by
    cases sign <;> rfl
  simp [hsign]

private theorem expMask_eq_packedInfinity_positive (fmt : FloatFormat) :
    FloatFormat.expMask fmt =
      packedInfinity (FloatFormat.toModel fmt) .positive := by
  unfold FloatFormat.expMask FloatFormat.expMaskNat FloatFormat.expAllOnesNat
    FloatFormat.ofWordNat FloatFormat.toModel FloatFormat.bitWidth
    packedInfinity packComponents Sign.toBitVec
  apply BitVec.toNat_inj.mp
  simp only [BitVec.toNat_ofNat, BitVec.toNat_append, BitVec.toNat_neg,
    Nat.shiftLeft_eq]
  simp only [Nat.zero_mod, Nat.zero_mul, Nat.zero_or]
  rw [Nat.mod_eq_of_lt (by
    simpa [FloatFormat.expMaskNat, FloatFormat.expAllOnesNat,
      FloatFormat.bitWidth] using expMaskNat_lt_two_pow_bitWidth fmt)]
  simp [Nat.mod_eq_of_lt (one_lt_two_pow_expWidth fmt),
    Nat.mod_eq_of_lt (expAllOnes_lt_two_pow fmt)]

private theorem signMask_or_expMask_eq_packedInfinity_negative (fmt : FloatFormat) :
    FloatFormat.signMask fmt ||| FloatFormat.expMask fmt =
      packedInfinity (FloatFormat.toModel fmt) .negative := by
  apply BitVec.toNat_inj.mp
  have hsignIndex :
      1 + fmt.expWidth + fmt.fracWidth - 1 = fmt.expWidth + fmt.fracWidth := by
    omega
  have hsign :
      2 ^ (1 + fmt.expWidth + fmt.fracWidth - 1) =
        2 ^ fmt.expWidth * 2 ^ fmt.fracWidth := by
    rw [hsignIndex, pow_add]
  have hsignLt :
      2 ^ (1 + fmt.expWidth + fmt.fracWidth - 1) <
        2 ^ (1 + fmt.expWidth + fmt.fracWidth) := by
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  unfold FloatFormat.signMask FloatFormat.expMask
  rw [BitVec.toNat_or]
  unfold FloatFormat.ofWordNat FloatFormat.signMaskNat FloatFormat.signBitIndex
    FloatFormat.expMaskNat FloatFormat.expAllOnesNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by simpa [FloatFormat.bitWidth] using hsignLt)]
  rw [Nat.mod_eq_of_lt (by
    simpa [FloatFormat.expMaskNat, FloatFormat.expAllOnesNat] using
      expMaskNat_lt_two_pow_bitWidth fmt)]
  unfold packedInfinity packComponents Sign.toBitVec
  change
    2 ^ (FloatFormat.bitWidth fmt - 1) |||
        (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth =
      ((1#1 ++ -1#fmt.expWidth) ++ 0#fmt.fracWidth).toNat
  rw [BitVec.toNat_append, BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_neg, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (one_lt_two_pow_expWidth fmt),
    Nat.mod_eq_of_lt (expAllOnes_lt_two_pow fmt)]
  rw [show 2 ^ (FloatFormat.bitWidth fmt - 1) =
      2 ^ fmt.expWidth * 2 ^ fmt.fracWidth by
    simpa [FloatFormat.bitWidth] using hsign]
  norm_num
  simpa [Nat.shiftLeft_eq] using
    (Nat.shiftLeft_or_distrib
      (a := 2 ^ fmt.expWidth)
      (b := 2 ^ fmt.expWidth - 1)
      (i := fmt.fracWidth)).symm

/-- Positive executable infinity is Lean's positive packed infinity. -/
theorem posInf_eq_ofModel_infinity (fmt : FloatFormat) :
    posInf fmt = ofModel fmt (.infinity .positive) := by
  unfold posInf ofBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
  rw [expMask_eq_packedInfinity_positive]

/-- Negative executable infinity is Lean's negative packed infinity. -/
theorem negInf_eq_ofModel_infinity (fmt : FloatFormat) :
    negInf fmt = ofModel fmt (.infinity .negative) := by
  unfold negInf ofBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
  rw [signMask_or_expMask_eq_packedInfinity_negative]

/-- Model packing exposes the all-ones exponent field for either infinity sign. -/
@[simp] theorem expField_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    expField (ofModel fmt (.infinity sign)) =
      FloatFormat.expAllOnesNat fmt := by
  rw [← unpackExponent_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedInfinity
  rw [unpackExponent_packComponents]
  exact toNat_neg_one_exponentBits fmt

/-- Model packing exposes a zero fraction field for either infinity sign. -/
@[simp] theorem fracField_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    fracField (ofModel fmt (.infinity sign)) = 0 := by
  rw [← unpackMantissa_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedInfinity
  rw [unpackMantissa_packComponents]
  rfl

/-- Model packing preserves the sign bit of an infinity. -/
@[simp] theorem signBit_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    signBit (ofModel fmt (.infinity sign)) = modelSignBit sign := by
  rw [← modelSignBit_ofBitVec_unpackSign]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedInfinity
  rw [unpackSign_packComponents]
  cases sign <;> rfl

/-- A model-packed infinity is classified as infinity by every infinity-bearing descriptor. -/
@[simp] theorem isInf_ofModel_infinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) (sign : Sign) :
    isInf (ofModel fmt (.infinity sign)) = true := by
  have hencoding : fmt.encoding = .ieee := by
    simpa [FloatFormat.supportsInfinity] using hfmt
  simp [isInf, IEEE.isInf, hencoding]

/-- A model-packed infinity is not classified as NaN by an infinity-bearing descriptor. -/
@[simp] theorem isNaN_ofModel_infinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) (sign : Sign) :
    isNaN (ofModel fmt (.infinity sign)) = false := by
  have hencoding : fmt.encoding = .ieee := by
    simpa [FloatFormat.supportsInfinity] using hfmt
  simp [isNaN, IEEE.isNaN, hencoding]

/-- A model-packed infinity is not finite under an infinity-bearing descriptor. -/
@[simp] theorem isFinite_ofModel_infinity
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) (sign : Sign) :
    isFinite (ofModel fmt (.infinity sign)) = false := by
  have hencoding : fmt.encoding = .ieee := by
    simpa [FloatFormat.supportsInfinity] using hfmt
  simp [isFinite, IEEE.isFinite, hencoding]

/-- Re-decoding a model-packed infinity recovers the same logical value. -/
@[simp] theorem toModel_ofModel_infinity (fmt : FloatFormat) (sign : Sign) :
    toModel (ofModel fmt (.infinity sign)) = .infinity sign := by
  unfold toModel ofModel toModelBits ofModelBits
  exact unpack_pack_infinity _ _

/-- Positive executable infinity has positive sign. -/
@[simp] theorem signBit_posInf (fmt : FloatFormat) :
    signBit (posInf fmt) = false := by
  rw [posInf_eq_ofModel_infinity]
  exact signBit_ofModel_infinity fmt .positive

/-- Negative executable infinity has negative sign. -/
@[simp] theorem signBit_negInf (fmt : FloatFormat) :
    signBit (negInf fmt) = true := by
  rw [negInf_eq_ofModel_infinity]
  exact signBit_ofModel_infinity fmt .negative

/-- Positive executable infinity is classified as infinity whenever the format supports it. -/
@[simp] theorem isInf_posInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isInf (posInf fmt) = true := by
  rw [posInf_eq_ofModel_infinity]
  exact isInf_ofModel_infinity fmt hfmt .positive

/-- Negative executable infinity is classified as infinity whenever the format supports it. -/
@[simp] theorem isInf_negInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isInf (negInf fmt) = true := by
  rw [negInf_eq_ofModel_infinity]
  exact isInf_ofModel_infinity fmt hfmt .negative

/-- Positive executable infinity is not a NaN whenever the format supports infinity. -/
@[simp] theorem isNaN_posInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isNaN (posInf fmt) = false := by
  rw [posInf_eq_ofModel_infinity]
  exact isNaN_ofModel_infinity fmt hfmt .positive

/-- Negative executable infinity is not a NaN whenever the format supports infinity. -/
@[simp] theorem isNaN_negInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isNaN (negInf fmt) = false := by
  rw [negInf_eq_ofModel_infinity]
  exact isNaN_ofModel_infinity fmt hfmt .negative

/-- Positive executable infinity is not finite whenever the format supports infinity. -/
@[simp] theorem isFinite_posInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isFinite (posInf fmt) = false := by
  rw [posInf_eq_ofModel_infinity]
  exact isFinite_ofModel_infinity fmt hfmt .positive

/-- Negative executable infinity is not finite whenever the format supports infinity. -/
@[simp] theorem isFinite_negInf
    (fmt : FloatFormat) (hfmt : fmt.supportsInfinity = true) :
    isFinite (negInf fmt) = false := by
  rw [negInf_eq_ofModel_infinity]
  exact isFinite_ofModel_infinity fmt hfmt .negative

/-- Decoding positive executable infinity recovers positive logical infinity. -/
@[simp] theorem toModel_posInf (fmt : FloatFormat) :
    toModel (posInf fmt) = .infinity .positive := by
  rw [posInf_eq_ofModel_infinity]
  simp

/-- Decoding negative executable infinity recovers negative logical infinity. -/
@[simp] theorem toModel_negInf (fmt : FloatFormat) :
    toModel (negInf fmt) = .infinity .negative := by
  rw [negInf_eq_ofModel_infinity]
  simp

/-- Packing and unpacking a signed zero preserves its sign. -/
@[simp] theorem unpack_pack_zero (spec : Format) (sign : Sign) :
    unpack spec (pack spec (.zero sign)) = .zero sign := by
  unfold Float.Model.UnpackedFloat.pack Float.Model.UnpackedFloat.packedZero
    Float.Model.UnpackedFloat.unpack
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents]
  have hExponent : (0#spec.exponentBits) ≠ (-1#spec.exponentBits) := by
    rw [ne_eq, BitVec.zero_eq_neg_one_iff]
    exact Nat.ne_zero_of_lt spec.he
  have hsign : Sign.ofBitVec sign.toBitVec = sign := by
    cases sign <;> rfl
  simp [hExponent, hsign]

/-- Model packing exposes a zero exponent field for either signed zero. -/
@[simp] theorem expField_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    expField (ofModel fmt (.zero sign)) = 0 := by
  rw [← unpackExponent_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedZero
  rw [unpackExponent_packComponents]
  rfl

/-- Model packing exposes a zero fraction field for either signed zero. -/
@[simp] theorem fracField_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    fracField (ofModel fmt (.zero sign)) = 0 := by
  rw [← unpackMantissa_toNat]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedZero
  rw [unpackMantissa_packComponents]
  rfl

/-- Model packing preserves the sign bit of zero. -/
@[simp] theorem signBit_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    signBit (ofModel fmt (.zero sign)) = modelSignBit sign := by
  rw [← modelSignBit_ofBitVec_unpackSign]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    packedZero
  rw [unpackSign_packComponents]
  cases sign <;> rfl

/-- A model-packed signed zero is classified as zero by a conventional IEEE descriptor. -/
@[simp] theorem isZero_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    isZero (ofModel fmt (.zero sign)) = true := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  simp [isZero, IEEE.isZero, hencoding]

/-- A model-packed signed zero is not infinity under a conventional IEEE descriptor. -/
@[simp] theorem isInf_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    isInf (ofModel fmt (.zero sign)) = false := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hne : (0 : Nat) ≠ FloatFormat.expAllOnesNat fmt := by
    unfold FloatFormat.expAllOnesNat
    have hpow := one_lt_two_pow_expWidth fmt
    omega
  simp [isInf, IEEE.isInf, hencoding, hne]

/-- A model-packed signed zero is not NaN under a conventional IEEE descriptor. -/
@[simp] theorem isNaN_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    isNaN (ofModel fmt (.zero sign)) = false := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  simp [isNaN, IEEE.isNaN, hencoding]

/-- A model-packed signed zero is finite under a conventional IEEE descriptor. -/
@[simp] theorem isFinite_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    isFinite (ofModel fmt (.zero sign)) = true := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hne : (0 : Nat) ≠ FloatFormat.expAllOnesNat fmt := by
    unfold FloatFormat.expAllOnesNat
    have hpow := one_lt_two_pow_expWidth fmt
    omega
  simp [isFinite, IEEE.isFinite, hencoding, hne]

/-- Re-decoding a model-packed signed zero recovers the same logical value. -/
@[simp] theorem toModel_ofModel_zero (fmt : FloatFormat) (sign : Sign) :
    toModel (ofModel fmt (.zero sign)) = .zero sign := by
  unfold toModel ofModel toModelBits ofModelBits
  exact unpack_pack_zero _ _

/-- IEEE model packing preserves the real value of signed zero. -/
@[simp] theorem toReal_ofModel_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) :
    toReal (ofModel fmt (.zero sign)) = 0 := by
  rw [toReal_eq_unpackedToReal_toModel hfmt]
  unfold toModel ofModel toModelBits ofModelBits
  rw [unpack_pack_zero]
  exact unpackedToReal_zero sign

/-- Positive executable zero is Lean's positive packed zero. -/
theorem posZero_eq_ofModel_zero (fmt : FloatFormat) :
    posZero fmt = ofModel fmt (.zero .positive) := by
  unfold posZero ofNatBits ofBits ofModel ofModelBits
    Float.Model.UnpackedFloat.pack Float.Model.UnpackedFloat.packedZero
    Float.Model.UnpackedFloat.packComponents Float.Model.UnpackedFloat.Sign.toBitVec
    FloatFormat.ofWordNat FloatFormat.toModel FloatFormat.bitWidth
  congr 1
  apply BitVec.toNat_inj.mp
  simp

/-- Negative executable zero is Lean's negative packed zero. -/
theorem negZero_eq_ofModel_zero (fmt : FloatFormat) :
    negZero fmt = ofModel fmt (.zero .negative) := by
  unfold negZero ofBits ofModel ofModelBits Float.Model.UnpackedFloat.pack
    Float.Model.UnpackedFloat.packedZero Float.Model.UnpackedFloat.packComponents
    Float.Model.UnpackedFloat.Sign.toBitVec FloatFormat.signMask FloatFormat.ofWordNat
    FloatFormat.signMaskNat FloatFormat.signBitIndex FloatFormat.toModel FloatFormat.bitWidth
  congr 1
  apply BitVec.toNat_inj.mp
  simp only [BitVec.toNat_ofNat, pow_add, pow_one, BitVec.ofNat_eq_ofNat, BitVec.toNat_append,
    Nat.mod_succ,
    Nat.shiftLeft_eq, one_mul, Nat.zero_mod, Nat.or_zero]
  have hindex : 1 + fmt.expWidth + fmt.fracWidth - 1 =
      fmt.expWidth + fmt.fracWidth := by omega
  have hnumerator : 2 ^ (1 + fmt.expWidth + fmt.fracWidth - 1) =
      2 ^ fmt.expWidth * 2 ^ fmt.fracWidth := by
    rw [hindex, pow_add]
  rw [hnumerator]
  rw [Nat.mod_eq_of_lt]
  have hpow : 0 < 2 ^ fmt.expWidth * 2 ^ fmt.fracWidth :=
    mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _)
  nlinarith

/-- Positive executable zero has positive sign. -/
@[simp] theorem signBit_posZero (fmt : FloatFormat) :
    signBit (posZero fmt) = false := by
  rw [posZero_eq_ofModel_zero]
  exact signBit_ofModel_zero fmt .positive

/-- Negative executable zero has negative sign. -/
@[simp] theorem signBit_negZero (fmt : FloatFormat) :
    signBit (negZero fmt) = true := by
  rw [negZero_eq_ofModel_zero]
  exact signBit_ofModel_zero fmt .negative

/--
The policy-aware zero constructor keeps the requested sign exactly when signed zero is supported.
-/
@[simp] theorem signBit_zero (fmt : FloatFormat) (sign : Bool) :
    signBit (zero fmt sign) = (sign && fmt.supportsSignedZero) := by
  cases sign
  · simp [zero]
  · cases hfmt : fmt.supportsSignedZero <;> simp [zero, hfmt]

/-- The canonical positive-zero word is classified as zero in every supported encoding. -/
@[simp] theorem isZero_posZero (fmt : FloatFormat) :
    isZero (posZero fmt) = true := by
  cases hencoding : fmt.encoding <;>
    simp [isZero, IEEE.isZero, hencoding, posZero, ofNatBits, ofBits,
      FloatFormat.ofWordNat, expField, fracField]

/-- Positive executable zero has a zero exponent field. -/
@[simp] theorem expField_posZero (fmt : FloatFormat) :
    expField (posZero fmt) = 0 := by
  rw [posZero_eq_ofModel_zero]
  exact expField_ofModel_zero fmt .positive

/-- Positive executable zero has a zero fraction field. -/
@[simp] theorem fracField_posZero (fmt : FloatFormat) :
    fracField (posZero fmt) = 0 := by
  rw [posZero_eq_ofModel_zero]
  exact fracField_ofModel_zero fmt .positive

/-- Negative executable zero has a zero exponent field. -/
@[simp] theorem expField_negZero (fmt : FloatFormat) :
    expField (negZero fmt) = 0 := by
  rw [negZero_eq_ofModel_zero]
  exact expField_ofModel_zero fmt .negative

/-- Negative executable zero has a zero fraction field. -/
@[simp] theorem fracField_negZero (fmt : FloatFormat) :
    fracField (negZero fmt) = 0 := by
  rw [negZero_eq_ofModel_zero]
  exact fracField_ofModel_zero fmt .negative

private theorem zero_ne_expAllOnesNat (fmt : FloatFormat) :
    (0 : Nat) ≠ FloatFormat.expAllOnesNat fmt := by
  unfold FloatFormat.expAllOnesNat
  have hpow := one_lt_two_pow_expWidth fmt
  omega

/--
In an encoding with two zero words, negative executable zero is classified as zero.

Under the finite-unsigned-zero encoding the negative-zero word is the NaN, so the hypothesis
cannot be dropped.
-/
@[simp] theorem isZero_negZero (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    isZero (negZero fmt) = true := by
  cases hencoding : fmt.encoding
  · simp [isZero, IEEE.isZero, hencoding]
  · simp [isZero, IEEE.isZero, hencoding]
  · exact absurd hfmt (by simp [FloatFormat.supportsSignedZero, hencoding])
  · simp [isZero, IEEE.isZero, hencoding]

/-- Positive executable zero is not a NaN in any encoding. -/
@[simp] theorem isNaN_posZero (fmt : FloatFormat) :
    isNaN (posZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  have hbits : (posZero fmt).bits ≠ FloatFormat.signMask fmt :=
    fun hzero => FloatFormat.signMask_ne_zero fmt hzero.symm
  cases hencoding : fmt.encoding
  · simp [isNaN, IEEE.isNaN, hencoding]
  · simp [isNaN, hencoding, hne]
  · simp [isNaN, hencoding, hbits]
  · simp [isNaN, hencoding]

/--
Negative executable zero is not a NaN when the encoding has two zero words.

Under the finite-unsigned-zero encoding the negative-zero word is the NaN, so the hypothesis
cannot be dropped.
-/
@[simp] theorem isNaN_negZero (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    isNaN (negZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  cases hencoding : fmt.encoding
  · simp [isNaN, IEEE.isNaN, hencoding]
  · simp [isNaN, hencoding, hne]
  · exact absurd hfmt (by simp [FloatFormat.supportsSignedZero, hencoding])
  · simp [isNaN, hencoding]

/-- Positive executable zero is not infinity in any encoding. -/
@[simp] theorem isInf_posZero (fmt : FloatFormat) :
    isInf (posZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  cases hencoding : fmt.encoding <;> simp [isInf, IEEE.isInf, hencoding, hne]

/-- Negative executable zero is not infinity in any encoding. -/
@[simp] theorem isInf_negZero (fmt : FloatFormat) :
    isInf (negZero fmt) = false := by
  have hne := zero_ne_expAllOnesNat fmt
  cases hencoding : fmt.encoding <;> simp [isInf, IEEE.isInf, hencoding, hne]

/-- Positive executable zero is finite in any encoding. -/
@[simp] theorem isFinite_posZero (fmt : FloatFormat) :
    isFinite (posZero fmt) = true := by
  have hne := zero_ne_expAllOnesNat fmt
  have hnan := isNaN_posZero fmt
  cases hencoding : fmt.encoding <;> simp [isFinite, IEEE.isFinite, hencoding, hne, hnan]

/--
Negative executable zero is finite when the encoding has two zero words.

Under the finite-unsigned-zero encoding the negative-zero word is the NaN, so the hypothesis
cannot be dropped.
-/
@[simp] theorem isFinite_negZero (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    isFinite (negZero fmt) = true := by
  have hne := zero_ne_expAllOnesNat fmt
  have hnan := isNaN_negZero fmt hfmt
  cases hencoding : fmt.encoding <;> simp [isFinite, IEEE.isFinite, hencoding, hne, hnan]

/-- Decoding positive executable zero recovers positive logical zero. -/
@[simp] theorem toModel_posZero (fmt : FloatFormat) :
    toModel (posZero fmt) = .zero .positive := by
  rw [posZero_eq_ofModel_zero]
  simp

/-- Decoding negative executable zero recovers negative logical zero. -/
@[simp] theorem toModel_negZero (fmt : FloatFormat) :
    toModel (negZero fmt) = .zero .negative := by
  rw [negZero_eq_ofModel_zero]
  simp

/-- Positive zero denotes real zero in every conventional IEEE format. -/
@[simp] theorem toReal_posZero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toReal (posZero fmt) = 0 := by
  rw [posZero_eq_ofModel_zero, toReal_ofModel_zero fmt hfmt]

/-- Negative zero denotes real zero in every conventional IEEE format. -/
@[simp] theorem toReal_negZero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    toReal (negZero fmt) = 0 := by
  rw [negZero_eq_ofModel_zero, toReal_ofModel_zero fmt hfmt]

/-- Either signed-zero constructor has real value zero in a conventional IEEE format. -/
@[simp] theorem toReal_signedZero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (negative : Bool) :
    toReal (if negative then negZero fmt else posZero fmt) = 0 := by
  cases negative <;> simp [hfmt]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
