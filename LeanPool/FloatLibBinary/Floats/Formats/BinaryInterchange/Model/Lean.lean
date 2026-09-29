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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Carrier
public import Init.Data.Float.Model.Unpacked
public import Mathlib.Data.Nat.Bitwise

/-!
# Lean floating-point model bridge

`Model fmt` retains the raw interchange bits, including noncanonical NaN payloads. Lean's
`Float.Model.UnpackedFloat` interprets those bits using the conventional IEEE bias and exceptional
encodings for their field widths. This module connects the two without selecting binary32 or any
other fixed format. Custom descriptor biases and encoding policies require separate semantic
agreement theorems.

The bridge is width preserving: `FloatFormat.toModel` has exactly `fmt.bitWidth` packed bits, so no
padding, truncation, or host `Float` conversion occurs. Packing a model value canonicalizes NaNs,
as Lean's model requires; unpacking arbitrary `Model` bits remains total.

## References

- `Init.Data.Float.Model`, Lean 4's logical floating-point model.
- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019.
  https://doi.org/10.1109/IEEESTD.2019.8766229
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model
open Float.Model.UnpackedFloat

/-- Translate the executable sign bit to Lean's logical floating-point sign. -/
@[inline] def modelSign (negative : Bool) : Float.Model.UnpackedFloat.Sign :=
  if negative then .negative else .positive

/-- Translate Lean's logical floating-point sign back to an executable sign bit. -/
@[inline] def modelSignBit : Float.Model.UnpackedFloat.Sign → Bool
  | .negative => true
  | .positive => false

/-- Translating a clear executable sign bit produces Lean's positive sign. -/
@[simp] theorem modelSign_false : modelSign false = .positive :=
  rfl

/-- Translating a set executable sign bit produces Lean's negative sign. -/
@[simp] theorem modelSign_true : modelSign true = .negative :=
  rfl

/-- Lean's negative logical sign translates to a set executable sign bit. -/
@[simp] theorem modelSignBit_negative : modelSignBit .negative = true :=
  rfl

/-- Lean's positive logical sign translates to a clear executable sign bit. -/
@[simp] theorem modelSignBit_positive : modelSignBit .positive = false :=
  rfl

/-- Translating an executable sign bit to the logical model and back is the identity. -/
@[simp] theorem modelSignBit_modelSign (negative : Bool) :
    modelSignBit (modelSign negative) = negative := by
  cases negative <;> rfl

/-- View executable bits at the exactly equal width expected by Lean's model. -/
@[inline] def toModelBits {fmt : FloatFormat} (x : Model fmt) :
    BitVec (FloatFormat.toModel fmt).numBits :=
  x.bits

/-- Wrap packed Lean-model bits as an executable value of the corresponding format. -/
@[inline] def ofModelBits {fmt : FloatFormat}
    (bits : BitVec (FloatFormat.toModel fmt).numBits) : Model fmt :=
  ⟨bits⟩

/-- Wrapping Lean-model bits and viewing them again preserves every bit. -/
@[simp] theorem toModelBits_ofModelBits {fmt : FloatFormat}
    (bits : BitVec (FloatFormat.toModel fmt).numBits) :
    toModelBits (ofModelBits (fmt := fmt) bits) = bits :=
  rfl

/-- Viewing an executable value as Lean-model bits and wrapping them again is the identity. -/
@[simp] theorem ofModelBits_toModelBits {fmt : FloatFormat} (x : Model fmt) :
    ofModelBits (toModelBits x) = x := by
  cases x
  rfl

/-- Converting a one-bit vector to a logical sign and back preserves the bit vector. -/
private theorem sign_toBitVec_ofBitVec (bits : BitVec 1) :
    (Sign.ofBitVec bits).toBitVec = bits := by
  rcases BitVec.eq_zero_or_eq_one bits with hbits | hbits
  · simp [hbits, Sign.ofBitVec, Sign.toBitVec]
  · simp [hbits, Sign.ofBitVec, Sign.toBitVec]

/-- Splitting and recombining Lean-model components preserves the packed bit vector. -/
theorem packComponents_unpackComponents (spec : Float.Model.Format)
    (bits : BitVec spec.numBits) :
    packComponents spec (Sign.ofBitVec (unpackSign bits))
        (unpackExponent bits) (unpackMantissa bits) = bits := by
  unfold packComponents
  rw [sign_toBitVec_ofBitVec]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  by_cases hmantissa : i < spec.mantissaBitsWithoutImplicit
  · simp [hmantissa, unpackMantissa]
  · by_cases hexponent :
      i - spec.mantissaBitsWithoutImplicit < spec.exponentBits
    · have hindex :
          spec.mantissaBitsWithoutImplicit +
              (i - spec.mantissaBitsWithoutImplicit) = i := by
        omega
      simp [hmantissa, hexponent, unpackExponent, hindex]
    · have hsign :
          i = spec.mantissaBitsWithoutImplicit + spec.exponentBits := by
        omega
      subst i
      simp [unpackSign]

/-- Masking a widened natural bit vector agrees with widening the low-width vector. -/
private theorem ofNat_and_lowMask_eq_setWidth
    {width total : Nat} (hwidth : width ≤ total) (n : Nat) :
    BitVec.ofNat total n &&& BitVec.ofNat total (2 ^ width - 1) =
      (BitVec.ofNat width n).setWidth total := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have hpow : 2 ^ width ≤ 2 ^ total :=
    Nat.pow_le_pow_right (by decide) hwidth
  have hmask : 2 ^ width - 1 < 2 ^ total := by
    have hpos : 0 < 2 ^ width := Nat.two_pow_pos width
    omega
  rw [Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 hwidth)]
  rw [Nat.mod_eq_of_lt ((Nat.mod_lt n (Nat.two_pow_pos width)).trans_le hpow)]

/--
Packing explicit fields agrees with Lean's sign/exponent/fraction concatenation. Inputs are reduced
to their declared field widths by the corresponding `BitVec.ofNat`.
-/
theorem toModelBits_ofFields (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) :
    toModelBits (ofFields fmt sign exponent fraction) =
      packComponents (FloatFormat.toModel fmt) (modelSign sign)
        (BitVec.ofNat fmt.expWidth exponent)
        (BitVec.ofNat fmt.fracWidth fraction) := by
  let exponentBits : BitVec fmt.expWidth := BitVec.ofNat fmt.expWidth exponent
  let fractionBits : BitVec fmt.fracWidth := BitVec.ofNat fmt.fracWidth fraction
  have hExpWidth : fmt.expWidth ≤ fmt.bitWidth := by
    unfold FloatFormat.bitWidth
    omega
  have hFracWidth : fmt.fracWidth ≤ fmt.bitWidth := by
    unfold FloatFormat.bitWidth
    omega
  have hSignMask :
      FloatFormat.signMask fmt =
        (1#1).setWidth fmt.bitWidth <<< (fmt.expWidth + fmt.fracWidth) := by
    rw [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide)]
    apply BitVec.eq_of_toNat_eq
    have hindex : fmt.bitWidth - 1 = fmt.expWidth + fmt.fracWidth := by
      unfold FloatFormat.bitWidth
      omega
    have hshift : fmt.expWidth + fmt.fracWidth < fmt.bitWidth := by
      unfold FloatFormat.bitWidth
      omega
    have hpow :
        2 ^ (fmt.expWidth + fmt.fracWidth) < 2 ^ fmt.bitWidth :=
      Nat.pow_lt_pow_right (by decide) hshift
    have hone : 1 < 2 ^ fmt.bitWidth :=
      Nat.one_lt_two_pow (by
        unfold FloatFormat.bitWidth
        omega)
    unfold FloatFormat.signMask FloatFormat.signMaskNat
      FloatFormat.signBitIndex FloatFormat.ofWordNat
    simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
    rw [hindex, Nat.mod_eq_of_lt hpow, Nat.mod_eq_of_lt hone]
    simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hpow]
  have packed (signBits : BitVec 1) :
      signBits ++ exponentBits ++ fractionBits =
        (signBits.setWidth fmt.bitWidth <<< (fmt.expWidth + fmt.fracWidth)) |||
          (exponentBits.setWidth fmt.bitWidth <<< fmt.fracWidth) |||
            fractionBits.setWidth fmt.bitWidth := by
    simpa [FloatFormat.bitWidth] using
      (BitVec.setWidth_append_append_eq_shiftLeft_setWidth_or
        (b := signBits) (b' := exponentBits) (b'' := fractionBits)
        (w''' := fmt.bitWidth))
  change mkBits fmt sign exponent fraction =
    (modelSign sign).toBitVec ++ exponentBits ++ fractionBits
  rw [packed]
  unfold mkBits
  dsimp only
  unfold FloatFormat.expAllOnes FloatFormat.expAllOnesNat
    FloatFormat.fracMask FloatFormat.fracMaskNat FloatFormat.ofWordNat
  rw [ofNat_and_lowMask_eq_setWidth hExpWidth exponent]
  rw [ofNat_and_lowMask_eq_setWidth hFracWidth fraction]
  cases sign <;>
    simp [exponentBits, fractionBits, modelSign, Sign.toBitVec,
      hSignMask, BitVec.zero_shiftLeft]

/-!
## Agreement of packed fields

These lemmas are the representation boundary for the generic bridge. They show that the manual
field extractors used by the executable kernel and the extractors used by Lean's logical model
read the same raw bit vector. Arithmetic refinement proofs can therefore work with one decoded
sign, exponent, and mantissa rather than repeat bit-layout arguments for each format.
-/

/-- Packing and then extracting the one-bit sign field returns the original model sign. -/
@[simp] theorem unpackSign_packComponents (spec : Float.Model.Format)
    (sign : Float.Model.UnpackedFloat.Sign)
    (exponent : BitVec spec.exponentBits)
    (mantissa : BitVec spec.mantissaBitsWithoutImplicit) :
    Float.Model.UnpackedFloat.unpackSign
        (Float.Model.UnpackedFloat.packComponents spec sign exponent mantissa) =
      sign.toBitVec := by
  unfold Float.Model.UnpackedFloat.unpackSign
    Float.Model.UnpackedFloat.packComponents
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp only [BitVec.getLsbD_extractLsb']
  rw [BitVec.getLsbD_append]
  rw [BitVec.getLsbD_append]
  simp

/-- Lean's model and the executable decoder extract the same fraction field. -/
theorem unpackMantissa_toNat {fmt : FloatFormat} (x : Model fmt) :
    (Float.Model.UnpackedFloat.unpackMantissa
      (spec := FloatFormat.toModel fmt) (toModelBits x)).toNat = fracField x := by
  unfold Float.Model.UnpackedFloat.unpackMantissa
  rw [BitVec.extractLsb'_toNat]
  unfold fracField FloatFormat.fracMask FloatFormat.ofWordNat FloatFormat.fracMaskNat
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  cases fmt with
  | mk exponentWidth exponentWidthPos fractionWidth fractionWidthPos =>
    simp only [toModelBits, FloatFormat.toModel, FloatFormat.bitWidth]
    change
      (x.bits.toNat >>> 0) % 2 ^ fractionWidth =
        x.bits.toNat &&&
          ((2 ^ fractionWidth - 1) % 2 ^ (1 + exponentWidth + fractionWidth))
    rw [Nat.shiftRight_zero]
    have hmask : 2 ^ fractionWidth - 1 < 2 ^ (1 + exponentWidth + fractionWidth) := by
      have hpow : 0 < 2 ^ fractionWidth := Nat.pow_pos (by decide)
      have hle : 2 ^ fractionWidth ≤ 2 ^ (1 + exponentWidth + fractionWidth) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod]

/-- The decoded fraction field fits in exactly the number of bits declared by its format. -/
theorem fracField_lt_pow2 {fmt : FloatFormat} (x : Model fmt) :
    fracField x < 2 ^ fmt.fracWidth := by
  rw [← unpackMantissa_toNat x]
  exact (Float.Model.UnpackedFloat.unpackMantissa
    (spec := FloatFormat.toModel fmt) (toModelBits x)).isLt

/-- The all-ones exponent word of Lean's model is the executable all-ones exponent field. -/
theorem toNat_neg_one_exponentBits (fmt : FloatFormat) :
    (-1#(FloatFormat.toModel fmt).exponentBits).toNat = FloatFormat.expAllOnesNat fmt := by
  change (-1#fmt.expWidth).toNat = 2 ^ fmt.expWidth - 1
  rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]

/-- Lean's model and the executable decoder extract the same biased exponent field. -/
theorem unpackExponent_toNat {fmt : FloatFormat} (x : Model fmt) :
    (Float.Model.UnpackedFloat.unpackExponent
      (spec := FloatFormat.toModel fmt) (toModelBits x)).toNat = expField x := by
  unfold Float.Model.UnpackedFloat.unpackExponent
  rw [BitVec.extractLsb'_toNat]
  unfold expField FloatFormat.expAllOnes FloatFormat.ofWordNat
    FloatFormat.expAllOnesNat
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  cases fmt with
  | mk exponentWidth exponentWidthPos fractionWidth fractionWidthPos =>
    simp only [toModelBits, FloatFormat.toModel, FloatFormat.bitWidth]
    change
      (x.bits.toNat >>> fractionWidth) % 2 ^ exponentWidth =
        (x.bits.toNat >>> fractionWidth) &&&
          ((2 ^ exponentWidth - 1) % 2 ^ (1 + exponentWidth + fractionWidth))
    have hmask : 2 ^ exponentWidth - 1 < 2 ^ (1 + exponentWidth + fractionWidth) := by
      have hpow : 0 < 2 ^ exponentWidth := Nat.pow_pos (by decide)
      have hle : 2 ^ exponentWidth ≤ 2 ^ (1 + exponentWidth + fractionWidth) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod]

/-- The decoded biased exponent fits in exactly the number of bits declared by its format. -/
theorem expField_lt_pow2 {fmt : FloatFormat} (x : Model fmt) :
    expField x < 2 ^ fmt.expWidth := by
  rw [← unpackExponent_toNat x]
  exact (Float.Model.UnpackedFloat.unpackExponent
    (spec := FloatFormat.toModel fmt) (toModelBits x)).isLt

/--
An exponent field that is neither endpoint lies strictly inside the encoded range.

Native normal-number kernels use this fact after checking zero and the all-ones pattern. Keeping
the arithmetic here avoids repeating width-specific proofs for binary64, binary128, and future
fixed-width backends.
-/
theorem expField_interior_bounds {fmt : FloatFormat} (x : Model fmt)
    (hnonzero : expField x ≠ 0)
    (hnotAllOnes : expField x ≠ fmt.expAllOnesNat) :
    0 < expField x ∧ expField x < fmt.expAllOnesNat := by
  constructor
  · exact Nat.pos_of_ne_zero hnonzero
  · have hlt := expField_lt_pow2 x
    unfold FloatFormat.expAllOnesNat at hnotAllOnes ⊢
    omega

/-- Lean's one-bit sign field is exactly the most significant executable bit. -/
theorem unpackSign_eq_ofBool_msb {fmt : FloatFormat} (x : Model fmt) :
    Float.Model.UnpackedFloat.unpackSign
      (spec := FloatFormat.toModel fmt) (toModelBits x) = BitVec.ofBool x.bits.msb := by
  unfold Float.Model.UnpackedFloat.unpackSign
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp only [BitVec.getLsbD_extractLsb', decide_true,
    Bool.true_and, BitVec.getLsbD_ofBool]
  simp only [FloatFormat.toModel, toModelBits]
  simp only [Nat.zero_lt_one, decide_true, Bool.true_and, Nat.add_zero]
  rw [show fmt.fracWidth + fmt.expWidth = fmt.bitWidth - 1 by
    unfold FloatFormat.bitWidth
    omega]
  exact (BitVec.msb_eq_getLsbD_last x.bits).symm

/-- Lean's unpacked sign and the executable Boolean sign agree. -/
theorem modelSignBit_ofBitVec_unpackSign {fmt : FloatFormat} (x : Model fmt) :
    modelSignBit
      (Float.Model.UnpackedFloat.Sign.ofBitVec
        (Float.Model.UnpackedFloat.unpackSign
          (spec := FloatFormat.toModel fmt) (toModelBits x))) = signBit x := by
  rw [unpackSign_eq_ofBool_msb, signBit_eq_msb]
  cases x.bits.msb <;> rfl

/-- Packing explicit fields retains the low `fracWidth` bits of the fraction. -/
@[simp] theorem fracField_ofFields (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) :
    fracField (ofFields fmt sign exponent fraction) = fraction % 2 ^ fmt.fracWidth := by
  rw [← unpackMantissa_toNat, toModelBits_ofFields]
  simp [FloatFormat.toModel]

/-- Packing explicit fields retains the low `expWidth` bits of the biased exponent. -/
@[simp] theorem expField_ofFields (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) :
    expField (ofFields fmt sign exponent fraction) = exponent % 2 ^ fmt.expWidth := by
  rw [← unpackExponent_toNat, toModelBits_ofFields]
  simp [FloatFormat.toModel]

/-- Packing explicit fields preserves the requested sign bit. -/
@[simp] theorem signBit_ofFields (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) :
    signBit (ofFields fmt sign exponent fraction) = sign := by
  rw [← modelSignBit_ofBitVec_unpackSign, toModelBits_ofFields]
  cases sign <;>
    simp [FloatFormat.toModel, Sign.ofBitVec, Sign.toBitVec, modelSignBit]

/-- Repacking the fields extracted from a `Model` reconstructs its exact bit pattern. -/
theorem ofFields_signBit_expField_fracField {fmt : FloatFormat}
    (x : Model fmt) :
    ofFields fmt (signBit x) (expField x) (fracField x) = x := by
  have hbits :
      toModelBits (ofFields fmt (signBit x) (expField x) (fracField x)) =
        toModelBits x := by
    rw [toModelBits_ofFields]
    have hsign :
        modelSign (signBit x) =
          Sign.ofBitVec (unpackSign (toModelBits x)) := by
      rw [← modelSignBit_ofBitVec_unpackSign]
      cases Sign.ofBitVec (unpackSign (toModelBits x)) <;> rfl
    rw [hsign]
    have hexponent :
        BitVec.ofNat fmt.expWidth (expField x) =
          unpackExponent (toModelBits x) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (expField_lt_pow2 x)]
      exact (unpackExponent_toNat x).symm
    rw [hexponent]
    have hfraction :
        BitVec.ofNat fmt.fracWidth (fracField x) =
          unpackMantissa (toModelBits x) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (fracField_lt_pow2 x)]
      exact (unpackMantissa_toNat x).symm
    rw [hfraction, packComponents_unpackComponents]
  calc
    ofFields fmt (signBit x) (expField x) (fracField x) =
        ofModelBits (toModelBits
          (ofFields fmt (signBit x) (expField x) (fracField x))) :=
      (ofModelBits_toModelBits _).symm
    _ = ofModelBits (toModelBits x) := congrArg ofModelBits hbits
    _ = x := ofModelBits_toModelBits x

/-- Packing three zero fields produces positive zero. -/
@[simp] theorem ofFields_false_zero_zero (fmt : FloatFormat) :
    ofFields fmt false 0 0 = posZero fmt := by
  have hzero : FloatFormat.ofWordNat fmt 0 = 0 := by
    unfold FloatFormat.ofWordNat
    simp
  unfold ofFields mkBits posZero ofNatBits ofBits
  simp [hzero]

/-- Packing only the sign bit produces the IEEE negative-zero bit pattern. -/
@[simp] theorem ofFields_true_zero_zero (fmt : FloatFormat) :
    ofFields fmt true 0 0 = negZero fmt := by
  have hzero : FloatFormat.ofWordNat fmt 0 = 0 := by
    unfold FloatFormat.ofWordNat
    simp
  unfold ofFields mkBits negZero ofBits
  simp [hzero]

/-- An in-range fraction is recovered exactly after field packing. -/
theorem fracField_ofFields_of_lt (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (hfraction : fraction < 2 ^ fmt.fracWidth) :
    fracField (ofFields fmt sign exponent fraction) = fraction := by
  simp [Nat.mod_eq_of_lt hfraction]

/-- An in-range biased exponent is recovered exactly after field packing. -/
theorem expField_ofFields_of_lt (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (hexponent : exponent < 2 ^ fmt.expWidth) :
    expField (ofFields fmt sign exponent fraction) = exponent := by
  simp [Nat.mod_eq_of_lt hexponent]

/-- Interpret an arbitrary bit pattern using Lean's width-parameterized IEEE model. -/
@[inline] def toModel {fmt : FloatFormat} (x : Model fmt) : Float.Model.UnpackedFloat :=
  Float.Model.UnpackedFloat.unpack (FloatFormat.toModel fmt) (toModelBits x)

/-- Encode a Lean logical value at `fmt`'s field widths; NaNs use Lean's canonical payload. -/
@[inline] def ofModel (fmt : FloatFormat) (x : Float.Model.UnpackedFloat) : Model fmt :=
  ofModelBits (Float.Model.UnpackedFloat.pack (FloatFormat.toModel fmt) x)

/-- Whether the bits satisfy Lean's canonical-NaN invariant for packed model values. -/
def IsModelCanonical {fmt : FloatFormat} (x : Model fmt) : Prop :=
  (FloatFormat.toModel fmt).Valid (toModelBits x)

/-- Every value produced by model packing satisfies the model's canonical-NaN invariant. -/
theorem isModelCanonical_ofModel (fmt : FloatFormat) (x : Float.Model.UnpackedFloat) :
    IsModelCanonical (ofModel fmt x) :=
  Float.Model.UnpackedFloat.valid_pack

/-- Repacking through Lean's model canonicalizes bit patterns it interprets as IEEE NaNs. -/
@[inline] def canonicalizeModel {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  ofModel fmt (toModel x)

/-- Canonicalizing through Lean's model always establishes its packed-value invariant. -/
theorem isModelCanonical_canonicalizeModel {fmt : FloatFormat} (x : Model fmt) :
    IsModelCanonical (canonicalizeModel x) :=
  isModelCanonical_ofModel fmt (toModel x)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
