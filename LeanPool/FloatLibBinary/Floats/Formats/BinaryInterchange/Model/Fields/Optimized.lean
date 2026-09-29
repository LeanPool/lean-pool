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

public import Mathlib.Data.Nat.Bitwise
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Carrier

/-!
# Optimized field access for binary models

The public field operations in `Model.Carrier` use exact-width bit vectors, which expose the
storage layout cleanly to proofs. This module defines extensionally equal `Nat` implementations
and registers their compiler substitutions. Each field decoder reads the natural-number storage
pattern; packing constructs one natural-number pattern with an erased proof that it fits the
width.

The theorems here are execution certificates: they justify erased bounds or compiler rewrites.
Semantic facts about the public field operations belong in `Model.Fields.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

private theorem fracMaskNat_lt_storage (fmt : FloatFormat) :
    FloatFormat.fracMaskNat fmt < 2 ^ fmt.bitWidth := by
  unfold FloatFormat.fracMaskNat FloatFormat.bitWidth
  have hpow :
      2 ^ fmt.fracWidth ≤ 2 ^ (1 + fmt.expWidth + fmt.fracWidth) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos fmt.fracWidth
  omega

private theorem expAllOnesNat_lt_storage (fmt : FloatFormat) :
    FloatFormat.expAllOnesNat fmt < 2 ^ fmt.bitWidth := by
  unfold FloatFormat.expAllOnesNat FloatFormat.bitWidth
  have hpow :
      2 ^ fmt.expWidth ≤ 2 ^ (1 + fmt.expWidth + fmt.fracWidth) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos fmt.expWidth
  omega

private theorem signPower_lt_storage (fmt : FloatFormat) :
    2 ^ (fmt.expWidth + fmt.fracWidth) < 2 ^ fmt.bitWidth := by
  apply Nat.pow_lt_pow_right (by decide)
  unfold FloatFormat.bitWidth
  omega

private theorem fracMaskNat_lt_field (fmt : FloatFormat) :
    FloatFormat.fracMaskNat fmt < 2 ^ fmt.fracWidth := by
  unfold FloatFormat.fracMaskNat
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos fmt.fracWidth
  omega

private theorem expAllOnesNat_lt_field (fmt : FloatFormat) :
    FloatFormat.expAllOnesNat fmt < 2 ^ fmt.expWidth := by
  unfold FloatFormat.expAllOnesNat
  have hpos : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos fmt.expWidth
  omega

/-- Masked sign, exponent, and fraction fields always fit their declared storage word. -/
theorem packedFields_lt_storage (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) :
    (if sign then Nat.shiftLeft 1 (fmt.expWidth + fmt.fracWidth) else 0) |||
        Nat.shiftLeft (exponent &&& FloatFormat.expAllOnesNat fmt) fmt.fracWidth |||
          (fraction &&& FloatFormat.fracMaskNat fmt) <
      2 ^ fmt.bitWidth := by
  have hExponentField :
      exponent &&& FloatFormat.expAllOnesNat fmt < 2 ^ fmt.expWidth :=
    Nat.and_lt_two_pow exponent (expAllOnesNat_lt_field fmt)
  have hExponent :
      Nat.shiftLeft (exponent &&& FloatFormat.expAllOnesNat fmt) fmt.fracWidth <
        2 ^ fmt.bitWidth := by
    have hShifted := Nat.shiftLeft_lt (m := fmt.fracWidth) hExponentField
    exact hShifted.trans_le <|
      Nat.pow_le_pow_right (by decide) (by
        unfold FloatFormat.bitWidth
        omega)
  have hFractionField :
      fraction &&& FloatFormat.fracMaskNat fmt < 2 ^ fmt.fracWidth :=
    Nat.and_lt_two_pow fraction (fracMaskNat_lt_field fmt)
  have hFraction :
      fraction &&& FloatFormat.fracMaskNat fmt < 2 ^ fmt.bitWidth :=
    hFractionField.trans_le <|
      Nat.pow_le_pow_right (by decide) (by
        unfold FloatFormat.bitWidth
        omega)
  have hSign :
      (if sign then Nat.shiftLeft 1 (fmt.expWidth + fmt.fracWidth) else 0) <
        2 ^ fmt.bitWidth := by
    cases sign
    · exact Nat.two_pow_pos fmt.bitWidth
    · simpa [Nat.shiftLeft_eq] using signPower_lt_storage fmt
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow hSign hExponent) hFraction

/-- Read the sign directly from the natural-number storage pattern. -/
@[inline] def signBitImpl {fmt : FloatFormat} (x : Model fmt) : Bool :=
  x.toNatBits.testBit (fmt.expWidth + fmt.fracWidth)

/-- Decode the exponent after one conversion of the storage word to `Nat`. -/
@[inline] def expFieldImpl {fmt : FloatFormat} (x : Model fmt) : Nat :=
  (x.toNatBits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt

/-- Decode the fraction after one conversion of the storage word to `Nat`. -/
@[inline] def fracFieldImpl {fmt : FloatFormat} (x : Model fmt) : Nat :=
  x.toNatBits &&& FloatFormat.fracMaskNat fmt

/-- The direct natural-number sign decoder agrees with the public bit-vector definition. -/
theorem signBit_eq_signBitImpl_apply {fmt : FloatFormat} (x : Model fmt) :
    signBit x = signBitImpl x := by
  unfold signBit signBitImpl toNatBits
  let index := fmt.expWidth + fmt.fracWidth
  have hmask :
      (FloatFormat.signMask fmt).toNat = 2 ^ index := by
    unfold FloatFormat.signMask FloatFormat.signMaskNat
      FloatFormat.signBitIndex FloatFormat.ofWordNat
    rw [BitVec.toNat_ofNat]
    have hindex : fmt.bitWidth - 1 = index := by
      unfold index FloatFormat.bitWidth
      omega
    rw [hindex, Nat.mod_eq_of_lt (signPower_lt_storage fmt)]
  by_cases hzero : x.bits &&& FloatFormat.signMask fmt = 0
  · have hand : x.bits.toNat &&& 2 ^ index = 0 := by
      have h := congrArg BitVec.toNat hzero
      simpa [BitVec.toNat_and, hmask] using h
    have hbit : x.bits.toNat.testBit index = false := by
      rw [Nat.and_two_pow] at hand
      cases htest : x.bits.toNat.testBit index
      · rfl
      · simp [htest] at hand
    simp [hzero, hbit, index]
  · have hbit : x.bits.toNat.testBit index = true := by
      cases htest : x.bits.toNat.testBit index
      · exfalso
        apply hzero
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_and, hmask, Nat.and_two_pow, htest]
      · rfl
    rw [hbit]
    exact bne_iff_ne.mpr hzero

/-- The compiler reads the sign from the natural-number storage pattern. -/
@[csimp] theorem signBit_eq_signBitImpl :
    @signBit = @signBitImpl := by
  funext fmt x
  exact signBit_eq_signBitImpl_apply x

/-- The direct natural-number exponent decoder agrees with the public bit-vector definition. -/
theorem expField_eq_expFieldImpl_apply {fmt : FloatFormat} (x : Model fmt) :
    expField x = expFieldImpl x := by
  unfold expField expFieldImpl toNatBits
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight,
    FloatFormat.expAllOnes, FloatFormat.ofWordNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (expAllOnesNat_lt_storage fmt)]

/-- The compiler decodes the exponent through one conversion to `Nat`. -/
@[csimp] theorem expField_eq_expFieldImpl :
    @expField = @expFieldImpl := by
  funext fmt x
  exact expField_eq_expFieldImpl_apply x

/-- The direct natural-number fraction decoder agrees with the public bit-vector definition. -/
theorem fracField_eq_fracFieldImpl_apply {fmt : FloatFormat} (x : Model fmt) :
    fracField x = fracFieldImpl x := by
  unfold fracField fracFieldImpl toNatBits
  simp only [BitVec.toNat_and, FloatFormat.fracMask, FloatFormat.ofWordNat,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (fracMaskNat_lt_storage fmt)]

/-- The compiler decodes the fraction through one conversion to `Nat`. -/
@[csimp] theorem fracField_eq_fracFieldImpl :
    @fracField = @fracFieldImpl := by
  funext fmt x
  exact fracField_eq_fracFieldImpl_apply x

/--
Pack fields as one natural-number bit pattern known to fit the exact storage width.

The bound passed to `BitVec.ofNatLT` is erased from compiled code. Unlike `BitVec.ofNat`, this
avoids computing a redundant modulus after the masked fields have already established the width.
-/
@[inline] def mkBitsImpl (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) : FloatFormat.ExecWord fmt :=
  BitVec.ofNatLT
    ((if sign then Nat.shiftLeft 1 (fmt.expWidth + fmt.fracWidth) else 0) |||
      Nat.shiftLeft (exponent &&& FloatFormat.expAllOnesNat fmt) fmt.fracWidth |||
        (fraction &&& FloatFormat.fracMaskNat fmt))
    (packedFields_lt_storage fmt sign exponent fraction)

/-- The direct natural-number field packer agrees with the public mask-based definition. -/
theorem mkBits_eq_mkBitsImpl_apply (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) :
    mkBits fmt sign exponent fraction = mkBitsImpl fmt sign exponent fraction := by
  apply BitVec.eq_of_toNat_eq
  unfold mkBits mkBitsImpl
  simp only [BitVec.ofNatLT_eq_ofNat, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft,
    FloatFormat.signMask, FloatFormat.expAllOnes, FloatFormat.fracMask,
    FloatFormat.ofWordNat, BitVec.toNat_ofNat]
  have hexponent :
      ((exponent % 2 ^ fmt.bitWidth &&&
          FloatFormat.expAllOnesNat fmt % 2 ^ fmt.bitWidth) <<<
          fmt.fracWidth) % 2 ^ fmt.bitWidth =
        ((exponent &&& FloatFormat.expAllOnesNat fmt) <<<
          fmt.fracWidth) % 2 ^ fmt.bitWidth := by
    rw [← Nat.and_mod_two_pow]
    exact Nat.mod_two_pow_shiftLeft_mod_two_pow
  have hsign :
      FloatFormat.signMaskNat fmt % 2 ^ fmt.bitWidth =
        Nat.shiftLeft 1 (fmt.expWidth + fmt.fracWidth) % 2 ^ fmt.bitWidth := by
    unfold FloatFormat.signMaskNat FloatFormat.signBitIndex FloatFormat.bitWidth
    have hindex :
        1 + fmt.expWidth + fmt.fracWidth - 1 =
          fmt.expWidth + fmt.fracWidth := by
      omega
    rw [hindex]
    simp [Nat.shiftLeft_eq]
  rw [hexponent]
  cases sign <;>
    simp [Nat.or_mod_two_pow, Nat.and_mod_two_pow, hsign]

/-- The compiler packs fields as one natural-number bit pattern. -/
@[csimp] theorem mkBits_eq_mkBitsImpl :
    mkBits = mkBitsImpl := by
  funext fmt sign exponent fraction
  exact mkBits_eq_mkBitsImpl_apply fmt sign exponent fraction

/-- Construct a `Model` through the direct natural-number field packer. -/
@[inline] def ofFieldsImpl (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) : Model fmt :=
  ofBits (mkBitsImpl fmt sign exponent fraction)

/-- The compiler constructs explicit fields through the direct natural-number packer. -/
@[csimp] theorem ofFields_eq_ofFieldsImpl :
    ofFields = ofFieldsImpl := by
  funext fmt sign exponent fraction
  simp [ofFields, ofFieldsImpl, mkBits_eq_mkBitsImpl_apply]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
