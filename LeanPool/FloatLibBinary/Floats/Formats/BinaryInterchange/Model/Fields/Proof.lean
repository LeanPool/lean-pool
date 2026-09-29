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

import LeanPool.FloatLibBinary.Numerics.Bitwise
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Optimized -- shake: keep

/-!
# Correctness of packed field access

The packed-field laws describe how `Model.ofFields` decodes. The results are uniform in the
format and isolate the bit-layout reasoning needed by rounding, status-flag, and interval
proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
The sign bit is set exactly for storage words in the upper half of the format's code space.
-/
theorem signBit_eq_true_iff_signMaskNat_le
    {fmt : FloatFormat} (x : Model fmt) :
    signBit x = true ↔ fmt.signMaskNat ≤ x.toNatBits := by
  let index := fmt.expWidth + fmt.fracWidth
  have hwidth : fmt.bitWidth = index + 1 := by
    unfold index FloatFormat.bitWidth
    omega
  have hfit : x.toNatBits < 2 ^ (index + 1) := by
    simpa [hwidth] using toNatBits_lt_two_pow x
  rw [signBit_eq_signBitImpl_apply]
  unfold signBitImpl
  rw [Nat.testBit_eq_true_iff_two_pow_le_of_lt hfit]
  unfold FloatFormat.signMaskNat FloatFormat.signBitIndex
  rw [hwidth]
  simp

/--
The sign bit is clear exactly for storage words in the lower half of the format's code space.
-/
theorem signBit_eq_false_iff_toNatBits_lt_signMaskNat
    {fmt : FloatFormat} (x : Model fmt) :
    signBit x = false ↔ x.toNatBits < fmt.signMaskNat := by
  constructor
  · intro hfalse
    have hnotTrue : signBit x ≠ true := by
      simp [hfalse]
    have hnotLe : ¬fmt.signMaskNat ≤ x.toNatBits := by
      intro hle
      exact hnotTrue <|
        (signBit_eq_true_iff_signMaskNat_le x).2 hle
    omega
  · intro hlt
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    have hle :=
      (signBit_eq_true_iff_signMaskNat_le x).1 htrue
    omega

private theorem ofFields_bits_eq_zero_iff
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    (ofFields fmt sign exponent fraction).bits = 0 ↔
      sign = false ∧ exponent = 0 ∧ fraction = 0 := by
  constructor
  · intro hbits
    have hvalue : ofFields fmt sign exponent fraction = posZero fmt := by
      calc
        ofFields fmt sign exponent fraction =
            ofBits (ofFields fmt sign exponent fraction).bits :=
          (ofBits_toBits _).symm
        _ = ofBits (posZero fmt).bits := by
          congr 1
        _ = posZero fmt := ofBits_toBits _
    rw [← ofFields_false_zero_zero] at hvalue
    have hsign : sign = false := by
      simpa only [signBit_ofFields] using congrArg signBit hvalue
    have hexp : exponent = 0 := by
      simpa only [
        expField_ofFields_of_lt fmt sign exponent fraction hexponent,
        expField_ofFields_of_lt fmt false 0 0 (Nat.two_pow_pos fmt.expWidth)
      ] using congrArg expField hvalue
    have hfrac : fraction = 0 := by
      simpa only [
        fracField_ofFields_of_lt fmt sign exponent fraction hfraction,
        fracField_ofFields_of_lt fmt false 0 0 (Nat.two_pow_pos fmt.fracWidth)
      ] using congrArg fracField hvalue
    exact ⟨hsign, hexp, hfrac⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [ofFields_false_zero_zero, posZero, ofNatBits, ofBits,
      FloatFormat.ofWordNat]

private theorem ofFields_bits_eq_signMask_iff
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    (ofFields fmt sign exponent fraction).bits = fmt.signMask ↔
      sign = true ∧ exponent = 0 ∧ fraction = 0 := by
  constructor
  · intro hbits
    have hvalue : ofFields fmt sign exponent fraction = negZero fmt := by
      calc
        ofFields fmt sign exponent fraction =
            ofBits (ofFields fmt sign exponent fraction).bits :=
          (ofBits_toBits _).symm
        _ = ofBits (negZero fmt).bits := by
          congr 1
        _ = negZero fmt := ofBits_toBits _
    rw [← ofFields_true_zero_zero] at hvalue
    have hsign : sign = true := by
      simpa only [signBit_ofFields] using congrArg signBit hvalue
    have hexp : exponent = 0 := by
      simpa only [
        expField_ofFields_of_lt fmt sign exponent fraction hexponent,
        expField_ofFields_of_lt fmt true 0 0 (Nat.two_pow_pos fmt.expWidth)
      ] using congrArg expField hvalue
    have hfrac : fraction = 0 := by
      simpa only [
        fracField_ofFields_of_lt fmt sign exponent fraction hfraction,
        fracField_ofFields_of_lt fmt true 0 0 (Nat.two_pow_pos fmt.fracWidth)
      ] using congrArg fracField hvalue
    exact ⟨hsign, hexp, hfrac⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [ofFields_true_zero_zero, negZero, ofBits]

/-! ## Field classification -/

/-- Classification of an in-range explicit field tuple as zero. -/
theorem isZero_ofFields
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    isZero (ofFields fmt sign exponent fraction) =
      match fmt.encoding with
      | .finiteUnsignedZero => !sign && exponent == 0 && fraction == 0
      | .ieee | .finiteMaxNaN | .finite => exponent == 0 && fraction == 0 := by
  have hExp := expField_ofFields_of_lt fmt sign exponent fraction hexponent
  have hFrac := fracField_ofFields_of_lt fmt sign exponent fraction hfraction
  cases hencoding : fmt.encoding
  · simp [isZero, hencoding, IEEE.isZero, hExp, hFrac]
  · simp [isZero, hencoding, IEEE.isZero, hExp, hFrac]
  · apply Bool.eq_iff_iff.mpr
    simp only [isZero, hencoding, beq_iff_eq, Bool.and_eq_true]
    rw [ofFields_bits_eq_zero_iff fmt sign exponent fraction hexponent hfraction]
    cases sign <;> simp
  · simp [isZero, hencoding, IEEE.isZero, hExp, hFrac]

/-- Classification of an in-range explicit field tuple as finite. -/
theorem isFinite_ofFields
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    isFinite (ofFields fmt sign exponent fraction) =
      match fmt.encoding with
      | .ieee => exponent != fmt.expAllOnesNat
      | .finiteMaxNaN =>
          !(exponent == fmt.expAllOnesNat && fraction == fmt.fracMaskNat)
      | .finiteUnsignedZero => !(sign && exponent == 0 && fraction == 0)
      | .finite => true := by
  have hExp := expField_ofFields_of_lt fmt sign exponent fraction hexponent
  have hFrac := fracField_ofFields_of_lt fmt sign exponent fraction hfraction
  cases hencoding : fmt.encoding
  · simp [isFinite, hencoding, IEEE.isFinite, hExp]
  · simp [isFinite, isNaN, hencoding, hExp, hFrac]
  · have hnan :
        isNaN (ofFields fmt sign exponent fraction) =
          (sign && exponent == 0 && fraction == 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [isNaN, hencoding, beq_iff_eq, Bool.and_eq_true]
      rw [ofFields_bits_eq_signMask_iff fmt sign exponent fraction
        hexponent hfraction]
      cases sign <;> simp
    simp only [isFinite, hencoding, hnan]
  · simp [isFinite, hencoding]

/--
An IEEE field tuple is finite whenever its exponent is not the reserved all-ones pattern.

`ofFields` truncates the supplied fraction to the descriptor width, so this specialization needs
no separate fraction bound.
-/
theorem isFinite_ofFields_ieee
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < fmt.expAllOnesNat) :
    isFinite (ofFields fmt sign exponent fraction) = true := by
  have hencoding :=
    (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hexponentWidth : exponent < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat at hexponent
    omega
  simp only [isFinite, hencoding, IEEE.isFinite, expField_ofFields,
    Nat.mod_eq_of_lt hexponentWidth, bne_iff_ne]
  exact Nat.ne_of_lt hexponent

/-- The maximum-magnitude finite encoding is finite for either sign. -/
@[simp] theorem isFinite_maxFinite (fmt : FloatFormat) (sign : Bool) :
    isFinite (maxFinite fmt sign) = true := by
  rw [maxFinite, isFinite_ofFields fmt sign fmt.maxFiniteExpField
    fmt.maxFiniteFracField fmt.maxFiniteExpField_lt_two_pow
    fmt.maxFiniteFracField_lt_two_pow]
  have hfracMaskPos := fmt.fracMaskNat_pos
  have hfracPred : fmt.fracMaskNat - 1 ≠ fmt.fracMaskNat := by
    omega
  have hexponentFour : 4 ≤ 2 ^ fmt.expWidth := by
    simpa using
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.expWidth_ge_two
  cases hencoding : fmt.encoding
  · simp [FloatFormat.maxFiniteExpField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      hencoding]
    omega
  · simp [FloatFormat.maxFiniteExpField, FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      hencoding, hfracPred]
  · simp [FloatFormat.maxFiniteExpField, FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent,
      hencoding, Nat.ne_of_gt hfracMaskPos]
  · simp

/-- The largest positive finite encoding is finite. -/
@[simp] theorem isFinite_posMaxFinite (fmt : FloatFormat) :
    isFinite (posMaxFinite fmt) = true :=
  isFinite_maxFinite fmt false

/--
A normal field pair at or below the descriptor's greatest finite field pair is finite.
-/
theorem isFinite_ofFields_normal_of_le_maxFinite
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponentPos : exponent ≠ 0)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hmax :
      exponent < fmt.maxFiniteExpField ∨
        exponent = fmt.maxFiniteExpField ∧
          fraction ≤ fmt.maxFiniteFracField) :
    isFinite (ofFields fmt sign exponent fraction) = true := by
  rw [isFinite_ofFields fmt sign exponent fraction hexponent hfraction]
  have hexpPow : 4 ≤ 2 ^ fmt.expWidth := by
    simpa using
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.expWidth_ge_two
  have hfracPow : 2 ≤ 2 ^ fmt.fracWidth := by
    simpa using
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.fracWidth_pos
  cases hencoding : fmt.encoding
  · simp [hencoding, FloatFormat.maxFiniteExpField,
      FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      FloatFormat.fracMaskNat] at hmax ⊢
    omega
  · simp [hencoding, FloatFormat.maxFiniteExpField,
      FloatFormat.maxFiniteFracField,
      FloatFormat.Encoding.maxFiniteExponent, FloatFormat.expAllOnesNat,
      FloatFormat.fracMaskNat] at hmax ⊢
    omega
  · simp [hexponentPos]
  · simp

/-! ## Finite field decoding -/

/--
Decode in-range fields known to denote a finite value.

The exact exponent uses the bias declared by the complete format descriptor. This includes
all-ones exponent fields when the selected non-IEEE encoding treats them as finite.
-/
theorem toDyadicOption_ofFields_of_isFinite
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hfinite : isFinite (ofFields fmt sign exponent fraction) = true) :
    toDyadicOption (ofFields fmt sign exponent fraction) =
      if exponent = 0 then
        if fraction = 0 then
          some { negative := sign, significand := 0, exponent := 0 }
        else
          some {
            negative := sign
            significand := fraction
            exponent := fmt.minSubnormalExponent }
      else
        some {
          negative := sign
          significand := pow2 fmt.fracWidth + fraction
          exponent := Int.ofNat exponent - Int.ofNat fmt.exponentBias -
            Int.ofNat fmt.fracWidth } := by
  have hExp := expField_ofFields_of_lt fmt sign exponent fraction hexponent
  have hFrac := fracField_ofFields_of_lt fmt sign exponent fraction hfraction
  have hSign := signBit_ofFields fmt sign exponent fraction
  have hZero := isZero_ofFields fmt sign exponent fraction hexponent hfraction
  by_cases hieee : fmt.isIEEE = true
  · obtain ⟨hencoding, hbias⟩ := (FloatFormat.isIEEE_eq_true_iff fmt).mp hieee
    have hfiniteIEEE :
        IEEE.isFinite (ofFields fmt sign exponent fraction) = true := by
      simpa [isFinite, hencoding] using hfinite
    have hnotAllOnes : exponent ≠ fmt.expAllOnesNat := by
      intro hexponentAll
      have : expField (ofFields fmt sign exponent fraction) =
          fmt.expAllOnesNat := hExp.trans hexponentAll
      simp [IEEE.isFinite, this] at hfiniteIEEE
    simp [toDyadicOption, hieee, ieeeToDyadicOption, IEEE.isNaN, IEEE.isInf,
      hExp, hFrac, hSign, hnotAllOnes, FloatFormat.ieeeMinSubnormalExponent,
      FloatFormat.ieeeNormalMantissaExpOffset, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, hbias, sub_sub]
  · simp only [toDyadicOption, hieee, Bool.false_eq_true, ite_false]
    rw [hfinite]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [hZero, hExp, hFrac, hSign]
    by_cases hexponentZero : exponent = 0
    · subst exponent
      by_cases hfractionZero : fraction = 0
      · subst fraction
        rw [isFinite_ofFields fmt sign 0 0 (Nat.two_pow_pos fmt.expWidth)
          (Nat.two_pow_pos fmt.fracWidth)] at hfinite
        cases hencoding : fmt.encoding <;> cases sign <;>
          simp_all
      · cases hencoding : fmt.encoding <;> cases sign <;>
          simp_all
    · cases hencoding : fmt.encoding <;> cases sign <;>
        simp_all

/-- An in-range nonzero fraction at biased exponent zero decodes as a subnormal. -/
theorem toDyadicOption_ofFields_subnormal (fmt : FloatFormat) (sign : Bool)
    (fraction : Nat) (hfractionPos : fraction ≠ 0)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toDyadicOption (ofFields fmt sign 0 fraction) =
      some {
        negative := sign
        significand := fraction
        exponent := fmt.minSubnormalExponent } := by
  have hexponent : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos fmt.expWidth
  have hzeroAll : (0 : Nat) ≠ fmt.expAllOnesNat :=
    (FloatFormat.expAllOnesNat_pos fmt).ne
  have hfinite : isFinite (ofFields fmt sign 0 fraction) = true := by
    rw [isFinite_ofFields fmt sign 0 fraction hexponent hfraction]
    cases hencoding : fmt.encoding <;> cases sign <;>
      simp [hfractionPos, hzeroAll]
  simpa [hfractionPos] using
    toDyadicOption_ofFields_of_isFinite fmt sign 0 fraction hexponent hfraction hfinite

/-- In-range nonexceptional fields with nonzero biased exponent decode as a normal value. -/
theorem toDyadicOption_ofFields_normal (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (hexponentPos : exponent ≠ 0)
    (hexponent : exponent < FloatFormat.expAllOnesNat fmt)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toDyadicOption (ofFields fmt sign exponent fraction) =
      some {
        negative := sign
        significand := pow2 fmt.fracWidth + fraction
        exponent := Int.ofNat exponent - Int.ofNat fmt.exponentBias -
          Int.ofNat fmt.fracWidth } := by
  have hexponentWidth : exponent < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat at hexponent
    omega
  have hfinite : isFinite (ofFields fmt sign exponent fraction) = true := by
    rw [isFinite_ofFields fmt sign exponent fraction hexponentWidth hfraction]
    cases hencoding : fmt.encoding <;>
      simp [Nat.ne_of_lt hexponent, hexponentPos]
  simpa [hexponentPos] using
    toDyadicOption_ofFields_of_isFinite fmt sign exponent fraction hexponentWidth
      hfraction hfinite

/-! ## Closed-form real semantics -/

/-- Closed-form real value of an explicitly packed subnormal. -/
theorem toReal_ofFields_subnormal (fmt : FloatFormat) (sign : Bool)
    (fraction : Nat) (hfractionPos : fraction ≠ 0)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toReal (ofFields fmt sign 0 fraction) =
      (if sign then (-1 : ℝ) else 1) * (fraction : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
          fmt.minSubnormalExponent := by
  rw [toReal_eq,
    toDyadicOption_ofFields_subnormal fmt sign fraction hfractionPos hfraction]
  cases sign <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- Closed-form real value of explicitly packed normal fields. -/
theorem toReal_ofFields_normal (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (hexponentPos : exponent ≠ 0)
    (hexponent : exponent < FloatFormat.expAllOnesNat fmt)
    (hfraction : fraction < 2 ^ fmt.fracWidth) :
    toReal (ofFields fmt sign exponent fraction) =
      (if sign then (-1 : ℝ) else 1) *
        ((pow2 fmt.fracWidth + fraction : Nat) : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat exponent - Int.ofNat fmt.exponentBias -
              Int.ofNat fmt.fracWidth) := by
  rw [toReal_eq,
    toDyadicOption_ofFields_normal fmt sign exponent fraction hexponentPos
      hexponent hfraction]
  cases sign <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/--
Closed-form real value of finite normal fields, including all-ones exponent fields when the
selected encoding treats them as finite.
-/
theorem toReal_ofFields_normal_of_isFinite
    (fmt : FloatFormat) (sign : Bool) (exponent fraction : Nat)
    (hexponentPos : exponent ≠ 0)
    (hexponent : exponent < 2 ^ fmt.expWidth)
    (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hfinite : isFinite (ofFields fmt sign exponent fraction) = true) :
    toReal (ofFields fmt sign exponent fraction) =
      (if sign then (-1 : ℝ) else 1) *
        ((pow2 fmt.fracWidth + fraction : Nat) : ℝ) *
          FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
            (Int.ofNat exponent - Int.ofNat fmt.exponentBias -
              Int.ofNat fmt.fracWidth) := by
  rw [toReal_eq,
    toDyadicOption_ofFields_of_isFinite fmt sign exponent fraction hexponent
      hfraction hfinite]
  cases sign <;>
    simp [hexponentPos, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
