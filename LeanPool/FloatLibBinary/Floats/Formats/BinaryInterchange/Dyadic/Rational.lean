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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rounding
public import LeanPool.FloatLibBinary.Numerics.Exact.RationalBinary

/-!
# Exact rational rounding

Division produces an exact rational rather than a dyadic. These routines round
`(num / den) * 2^exponent` directly, using integer quotient rounding and descriptor-derived normal,
subnormal, and overflow thresholds.

The leading exponent is computed before scaling, and a quotient below half the least subnormal is
recognized from that exponent alone, so a format with a very wide exponent range does not
materialize an enormous shifted numerator or denominator. Conventional IEEE descriptors use the
proof-facing thresholds where convenient; custom biases and finite encodings follow the general
path with the same one-rounding contract.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-! ## Exact rationals for division -/

/--
Round exact rational `(num/den) * 2^exponent` in a conventional IEEE descriptor.

The explicit `isIEEE` proof ensures that the layout-derived bias and exponent bounds agree with
the descriptor. Use `roundRatScaled` for a custom bias or a finite encoding; it selects the
appropriate rounder from the complete descriptor.

This is the division analogue of `roundDyadic`: the overflow, subnormal, and normal cases are the
same, and the mantissa is obtained by `roundQuotientEven` instead of the integer
`roundShiftRightEven`.

The normal-path mantissa scale is `fracWidth - ⌊log₂(num/den)⌋`: the external exponent cancels, so
wide-exponent formats do not materialize an enormous shifted numerator or denominator. A quotient
below half the least subnormal returns signed zero before any shift. A zero denominator is not a
rational value and returns the format's invalid-operation result.
-/
@[inline] def ieeeRoundRatScaled (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (exponent : Int) (_hfmt : fmt.isIEEE = true) : Model fmt :=
  let p := fmt.fracWidth
  let maxUnb : Int := Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)
  let minUnb : Int := FloatFormat.ieeeMinNormalExponent fmt
  let underK : Int := -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt)
  let subAlign : Nat := FloatFormat.subnormalAlignExp fmt
  let bias : Nat := fmt.bias
  if den == 0 then
    canonicalNaN fmt
  else if num == 0 then
    if sign then negZero fmt else posZero fmt
  else
    let rationalExponent : Int := Numerics.RationalBinary.floorLog2 num den
    let totalExponent : Int := rationalExponent + exponent
    if totalExponent > maxUnb then
      if sign then negInf fmt else posInf fmt
    else if totalExponent < underK then
      if sign then negZero fmt else posZero fmt
    else if totalExponent < minUnb then
      let (num', den') :=
        Numerics.RationalBinary.scaleByPowerOfTwo
          num den (exponent + Int.ofNat subAlign)
      let frac := roundQuotientEven num' den'
      if frac == 0 then
        if sign then negZero fmt else posZero fmt
      else
        match Nat.decLe (pow2 p) frac with
        | isTrue _ => ofFields fmt sign 1 0
        | isFalse _ => ofFields fmt sign 0 frac
    else
      let shift : Int := Int.ofNat p - rationalExponent
      let (num', den') :=
        Numerics.RationalBinary.scaleByPowerOfTwo num den shift
      let m := roundQuotientEven num' den'
      let k' : Int :=
        if m == pow2 (p + 1) then totalExponent + 1 else totalExponent
      let m' : Nat := if m == pow2 (p + 1) then pow2 p else m
      if k' > maxUnb then
        if sign then negInf fmt else posInf fmt
      else
        let expNat : Nat := Int.toNat (k' + Int.ofNat bias)
        let fracNat : Nat := m' - pow2 p
        ofFields fmt sign expNat fracNat

/--
Round exact rational `(num / den) * 2^exponent` according to the complete format descriptor.

A quotient below half the least subnormal returns the format's zero from the leading exponent alone,
without materializing the subnormal alignment shift. In the remaining paths, the shift is
controlled by the numerator and denominator sizes and the destination precision, rather than
the full exponent range.
-/
@[inline] def roundRatScaledGeneral (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  if den == 0 then
    invalidResult fmt
  else if num == 0 then
    zero fmt sign
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 num den
    let totalExponent := rationalExponent + exponent
    if totalExponent > fmt.maxNormalExponent then
      nativeOverflow fmt sign
    else if totalExponent + 1 < fmt.minSubnormalExponent then
      zero fmt sign
    else if totalExponent < fmt.minNormalExponent then
      let subnormalShift :=
        exponent + Int.ofNat (fmt.exponentBias + precision - 1)
      let (scaledNum, scaledDen) :=
        Numerics.RationalBinary.scaleByPowerOfTwo num den subnormalShift
      let fraction := roundQuotientEven scaledNum scaledDen
      packRoundedSubnormal fmt sign (zero fmt sign) fraction
    else
      let shift : Int := Int.ofNat precision - rationalExponent
      let (scaledNum, scaledDen) :=
        Numerics.RationalBinary.scaleByPowerOfTwo num den shift
      let rounded := roundQuotientEven scaledNum scaledDen
      packRoundedNormal fmt sign (nativeOverflow fmt sign) totalExponent rounded

/--
Round exact rational `(num / den) * 2^exponent` to `Model fmt` using nearest-even.
-/
@[inline] def roundRatScaled (fmt : FloatFormat) (sign : Bool) (num den : Nat)
    (exponent : Int) : Model fmt :=
  if hfmt : fmt.isIEEE = true then
    ieeeRoundRatScaled fmt sign num den exponent hfmt
  else
    roundRatScaledGeneral fmt sign num den exponent

/-- Round exact rational `num/den` to `Model fmt` with nearest-even rounding. -/
@[inline] def roundRat (fmt : FloatFormat) (sign : Bool) (num den : Nat) : Model fmt :=
  roundRatScaled fmt sign num den 0

/-- A zero denominator is rejected by scaled rational rounding. -/
@[simp] theorem roundRatScaled_den_zero (fmt : FloatFormat) (sign : Bool) (num : Nat)
    (exponent : Int) :
    roundRatScaled fmt sign num 0 exponent = invalidResult fmt := by
  by_cases hieee : fmt.isIEEE
  · simp [roundRatScaled, ieeeRoundRatScaled, hieee]
  · simp [roundRatScaled, roundRatScaledGeneral, hieee]

/-- A zero numerator rounds to the format's zero when the denominator is nonzero. -/
@[simp] theorem roundRatScaled_num_zero (fmt : FloatFormat) (sign : Bool) (den : Nat)
    (exponent : Int) (hden : den ≠ 0) :
    roundRatScaled fmt sign 0 den exponent = zero fmt sign := by
  by_cases hieee : fmt.isIEEE
  · simp [roundRatScaled, ieeeRoundRatScaled, hieee, hden, zero]
  · simp [roundRatScaled, roundRatScaledGeneral, hieee, hden]

/-- A zero denominator is rejected with the destination format's invalid-operation result. -/
@[simp] theorem roundRat_den_zero (fmt : FloatFormat) (sign : Bool) (num : Nat) :
    roundRat fmt sign num 0 = invalidResult fmt := by
  simp [roundRat]

/-- A zero rational rounds to the format's zero when the denominator is nonzero. -/
@[simp] theorem roundRat_num_zero (fmt : FloatFormat) (sign : Bool) (den : Nat)
    (hden : den ≠ 0) :
    roundRat fmt sign 0 den = zero fmt sign := by
  simp [roundRat, hden]


end Model

end FloatLib.Floats.Formats.BinaryInterchange
