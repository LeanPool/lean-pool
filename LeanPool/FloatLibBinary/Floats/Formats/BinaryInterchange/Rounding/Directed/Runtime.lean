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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Executable directed rounding

Exact rational intermediates support the four `IEEERoundingMode` choices; together with the
dyadic rounders of `Rounding.Directed.Dyadic`, they implement addition, subtraction,
multiplication, division, fused multiply-add, and square root.

Rounding thresholds, signed-zero behavior, and exceptional results follow the `FloatFormat`
descriptor. Real and extended-real correctness theorems are provided separately by
`DirectedSemantics` with their format and input hypotheses.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Directed rounding of exact rationals -/

/--
Round a scaled positive rational magnitude to the adjacent lower or upper representable magnitude.

`roundMagnitudeUp = false` selects the lower magnitude and `true` selects the upper magnitude.
The `sign` parameter supplies the sign to the format's packing, zero, and overflow constructors.
-/
def roundRatMagnitudeDirectedScaled (fmt : FloatFormat) (roundMagnitudeUp sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  let subnormalAlign := fmt.exponentBias + precision - 1
  if denominator == 0 then
    invalidResult fmt
  else if numerator == 0 then
    zero fmt sign
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let totalExponent := rationalExponent + exponent
    if totalExponent > maxNormal then
      directedOverflow fmt sign roundMagnitudeUp
    else if totalExponent < minSubnormal then
      if roundMagnitudeUp then
        if sign then negMinSubnormal fmt else posMinSubnormal fmt
      else
        zero fmt sign
    else if totalExponent < minNormal then
      let (scaledNumerator, scaledDenominator) :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent + Int.ofNat
          subnormalAlign)
      let fraction :=
        roundQuotDirected roundMagnitudeUp scaledNumerator scaledDenominator
      packRoundedSubnormal fmt sign (zero fmt sign) fraction
    else
      let shift : Int := Int.ofNat precision - rationalExponent
      let (scaledNumerator, scaledDenominator) := Numerics.RationalBinary.scaleByPowerOfTwo
        numerator denominator shift
      let roundedMantissa :=
        roundQuotDirected roundMagnitudeUp scaledNumerator scaledDenominator
      packRoundedNormal fmt sign (directedOverflow fmt sign roundMagnitudeUp)
        totalExponent roundedMantissa

/-- Round an exact scaled signed rational according to an IEEE rounding direction. -/
def roundRatWithRoundingScaled (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  match mode with
  | .nearestEven => roundRatScaled fmt sign numerator denominator exponent
  | .towardZero =>
      roundRatMagnitudeDirectedScaled fmt false sign numerator denominator exponent
  | .towardPositiveInfinity =>
      roundRatMagnitudeDirectedScaled fmt (!sign) sign numerator denominator exponent
  | .towardNegativeInfinity =>
      roundRatMagnitudeDirectedScaled fmt sign sign numerator denominator exponent

/-- Round an exact signed rational according to an IEEE rounding direction. -/
def roundRatWithRounding (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) : Model fmt :=
  roundRatWithRoundingScaled fmt mode sign numerator denominator 0

/-- Round an exact scaled signed rational toward negative infinity. -/
@[inline] def roundRatDownScaled (fmt : FloatFormat) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  roundRatWithRoundingScaled fmt .towardNegativeInfinity sign numerator denominator exponent

/-- Round an exact scaled signed rational toward positive infinity. -/
@[inline] def roundRatUpScaled (fmt : FloatFormat) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  roundRatWithRoundingScaled fmt .towardPositiveInfinity sign numerator denominator exponent

/-- Round an exact signed rational toward negative infinity. -/
@[inline] def roundRatDown (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat) :
    Model fmt :=
  roundRatWithRounding fmt .towardNegativeInfinity sign numerator denominator

/-- Round an exact signed rational toward positive infinity. -/
@[inline] def roundRatUp (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat) :
    Model fmt :=
  roundRatWithRounding fmt .towardPositiveInfinity sign numerator denominator

/-! ## Arithmetic under an explicit rounding direction -/

/-- Signed zero for an exact addition result under `mode`. -/
@[inline] def zeroForExactSum (fmt : FloatFormat) (mode : IEEERoundingMode)
    (leftSign rightSign : Bool) : Model fmt :=
  match mode with
  | .towardNegativeInfinity =>
      zero fmt (leftSign || rightSign)
  | .nearestEven | .towardZero | .towardPositiveInfinity =>
      zero fmt (leftSign && rightSign)

/-- IEEE addition under an explicit rounding direction. -/
def addWithRounding {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  match mode with
  | .nearestEven => add x y
  | .towardZero | .towardPositiveInfinity | .towardNegativeInfinity =>
      withNaNSelection (chooseNaN2 x y) fun hnan =>
        let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
        if hxInf : isInf x then
          if isInf y then
            if signBit x == signBit y then x else invalidResult fmt
          else
            x
        else if hyInf : isInf y then
          y
        else
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1
              (Bool.eq_false_of_not_eq_true hxInf)
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2
              (Bool.eq_false_of_not_eq_true hyInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let exact := addDyadic dx dy
          if exact.significand == 0 then
            zeroForExactSum fmt mode dx.negative dy.negative
          else
            roundDyadicWithRounding fmt mode exact

/-- IEEE subtraction under an explicit rounding direction. -/
@[inline] def subWithRounding {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  addWithRounding mode x (neg y)

/-- IEEE multiplication under an explicit rounding direction. -/
def mulWithRounding {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  match mode with
  | .nearestEven => mul x y
  | .towardZero | .towardPositiveInfinity | .towardNegativeInfinity =>
      withNaNSelection (chooseNaN2 x y) fun hnan =>
        let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
        if hxInf : isInf x then
          if isZero y then invalidResult fmt
          else nativeOverflow fmt (signBit x != signBit y)
        else if hyInf : isInf y then
          if isZero x then invalidResult fmt
          else nativeOverflow fmt (signBit x != signBit y)
        else
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1
              (Bool.eq_false_of_not_eq_true hxInf)
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2
              (Bool.eq_false_of_not_eq_true hyInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let exact : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          roundDyadicWithRounding fmt mode exact

/-- IEEE division under an explicit rounding direction. -/
def divWithRounding {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  match mode with
  | .nearestEven => div x y
  | .towardZero | .towardPositiveInfinity | .towardNegativeInfinity =>
      withNaNSelection (chooseNaN2 x y) fun hnan =>
        let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
        if hxInf : isInf x then
          if isInf y then invalidResult fmt
          else nativeOverflow fmt (signBit x != signBit y)
        else if hyInf : isInf y then
          zero fmt (signBit x != signBit y)
        else if isZero y then
          if isZero x then invalidResult fmt
          else nativeOverflow fmt (signBit x != signBit y)
        else
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1
              (Bool.eq_false_of_not_eq_true hxInf)
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2
              (Bool.eq_false_of_not_eq_true hyInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let sign := Bool.xor dx.negative dy.negative
          if dx.significand == 0 then
            zero fmt sign
          else
            roundRatWithRoundingScaled fmt mode sign dx.significand dy.significand
              (dx.exponent - dy.exponent)

/-- IEEE fused multiply-add under an explicit rounding direction. -/
def fmaWithRounding {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y z : Model fmt) : Model fmt :=
  match mode with
  | .nearestEven => fma x y z
  | .towardZero | .towardPositiveInfinity | .towardNegativeInfinity =>
      withNaNSelection (chooseNaN3 x y z) fun hnan =>
        let hnotNaN := (chooseNaN3_eq_none_iff x y z).1 hnan
        if hxyInf : isInf x || isInf y then
          if isZero x || isZero y then
            invalidResult fmt
          else
            let productSign := Bool.xor (signBit x) (signBit y)
            let productInfinity := nativeOverflow fmt productSign
            if isInf z then
              if signBit z != productSign then invalidResult fmt else productInfinity
            else
              productInfinity
        else if hzInf : isInf z then
          z
        else
          let hxInf : isInf x = false := by
            cases hx : isInf x
            · rfl
            · simp [hx] at hxyInf
          let hyInf : isInf y = false := by
            cases hy : isInf y
            · rfl
            · simp [hy] at hxyInf
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1 hxInf
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2.1 hyInf
          let hzFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false z hnotNaN.2.2
              (Bool.eq_false_of_not_eq_true hzInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let dz := finiteDyadic z hzFinite
          let product : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let exact := addDyadic product dz
          if exact.significand == 0 then
            zeroForExactSum fmt mode product.negative dz.negative
          else
            roundDyadicWithRounding fmt mode exact

/-! ## Directed square root -/

/-- Dyadic endpoint pair used to enclose a nonnegative square root. -/
structure SqrtDyadicBracket where
  /-- Lower endpoint. -/
  lower : Numerics.Dyadic
  /-- Upper endpoint. -/
  upper : Numerics.Dyadic

/-- Compute a dyadic enclosure of the square root of a nonnegative exact dyadic. -/
def sqrtDyadicBracket (fmt : FloatFormat) (value : Numerics.Dyadic) : SqrtDyadicBracket :=
  let exponentOdd := value.exponent % 2 != 0
  let mantissa := if exponentOdd then value.significand * 2 else value.significand
  let evenExponent := if exponentOdd then value.exponent - 1 else value.exponent
  let halfExponent := evenExponent / 2
  let leading := Nat.log2 mantissa
  let rootLeading := leading / 2
  let extraPrecision := fmt.fracWidth - rootLeading
  let scaled := Nat.shiftLeft mantissa (2 * extraPrecision)
  let lowerMantissa := Nat.sqrt scaled
  let remainder := scaled - lowerMantissa * lowerMantissa
  let endpointExponent := halfExponent - Int.ofNat extraPrecision
  { lower := { negative := false, significand := lowerMantissa, exponent := endpointExponent }
    upper :=
      { negative := false
        significand := if remainder == 0 then lowerMantissa else lowerMantissa + 1
        exponent := endpointExponent } }

/-- IEEE square root under an explicit rounding direction. -/
def sqrtWithRounding {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x : Model fmt) : Model fmt :=
  match mode with
  | .nearestEven => sqrt x
  | .towardZero | .towardPositiveInfinity | .towardNegativeInfinity =>
      withNaNSelection (chooseNaN1 x) fun hnan =>
        let hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
        if hxInf : isInf x then
          if signBit x then invalidResult fmt else nativeOverflow fmt false
        else if isZero x then
          x
        else if signBit x then
          invalidResult fmt
        else
          let hfinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN
              (Bool.eq_false_of_not_eq_true hxInf)
          let value := finiteDyadic x hfinite
          let bracket := sqrtDyadicBracket fmt value
          match mode with
          | .towardPositiveInfinity => roundDyadicUp fmt bracket.upper
          | .towardZero | .towardNegativeInfinity => roundDyadicDown fmt bracket.lower
          | .nearestEven => sqrt x

/-! ## Interval-friendly operation names -/

/-- Addition rounded toward negative infinity. -/
@[inline] def addDown {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  addWithRounding .towardNegativeInfinity x y

/-- Addition rounded toward positive infinity. -/
@[inline] def addUp {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  addWithRounding .towardPositiveInfinity x y

/-- Subtraction rounded toward negative infinity. -/
@[inline] def subDown {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  subWithRounding .towardNegativeInfinity x y

/-- Subtraction rounded toward positive infinity. -/
@[inline] def subUp {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  subWithRounding .towardPositiveInfinity x y

/-- Multiplication rounded toward negative infinity. -/
@[inline] def mulDown {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  mulWithRounding .towardNegativeInfinity x y

/-- Multiplication rounded toward positive infinity. -/
@[inline] def mulUp {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  mulWithRounding .towardPositiveInfinity x y

/-- Division rounded toward negative infinity. -/
@[inline] def divDown {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  divWithRounding .towardNegativeInfinity x y

/-- Division rounded toward positive infinity. -/
@[inline] def divUp {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  divWithRounding .towardPositiveInfinity x y

/-- Fused multiply-add rounded toward negative infinity. -/
@[inline] def fmaDown {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  fmaWithRounding .towardNegativeInfinity x y z

/-- Fused multiply-add rounded toward positive infinity. -/
@[inline] def fmaUp {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  fmaWithRounding .towardPositiveInfinity x y z

/-- Square root rounded toward negative infinity. -/
@[inline] def sqrtDown {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  sqrtWithRounding .towardNegativeInfinity x

/-- Square root rounded toward positive infinity. -/
@[inline] def sqrtUp {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  sqrtWithRounding .towardPositiveInfinity x

end Model
end FloatLib.Floats.Formats.BinaryInterchange
