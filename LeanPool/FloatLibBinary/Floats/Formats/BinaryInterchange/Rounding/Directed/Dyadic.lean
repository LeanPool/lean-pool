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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Mode

/-!
# Directed rounding of exact dyadics

Exact signed dyadics round into a binary format under each supported IEEE rounding direction.
Toward-zero, toward-positive, and toward-negative rounding are implemented by one pair of
magnitude rounders, `roundDyadicMagnitudeDown` and `roundDyadicMagnitudeUp`, that the sign of
the value selects between; nearest-even delegates to `Model.roundDyadic`.

Overflow follows `directedOverflow`: a magnitude carried upward becomes the format's native
overflow value and a magnitude carried downward becomes the largest finite value. The policy
entry points `Policy.roundDyadicGeneral` and `Policy.roundDyadic` in `Rounding.Policy.Runtime`
delegate to `roundDyadicWithRounding` for the four IEEE directions, so their packed results agree
with these rounders by definition. Additional rounding policies use a separate rational core
whose denominator is required to be nonzero.

Every threshold is derived from `FloatFormat`. The magnitude helpers require a positive
mantissa; the signed entry points handle zero before selecting a magnitude helper.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Directed rounding of exact dyadics -/

/-- `ceil(n / 2^shift)` for natural numbers. -/
@[inline] def shiftRightCeilPow2 (n shift : Nat) : Nat :=
  if shift == 0 then
    n
  else
    let quotient := Nat.shiftRight n shift
    let remainder := n - Nat.shiftLeft quotient shift
    if remainder == 0 then quotient else quotient + 1

/-- Round an exact positive magnitude downward, attaching `sign` to the result. -/
def roundDyadicMagnitudeDown (fmt : FloatFormat) (sign : Bool)
    (mantissa : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let leading := Nat.log2 mantissa
  let totalExponent := Int.ofNat leading + exponent
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  if totalExponent > maxNormal then
    maxFinite fmt sign
  else if totalExponent < minSubnormal then
    zero fmt sign
  else if totalExponent < minNormal then
    let fraction :=
      match exponent - minSubnormal with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => Nat.shiftRight mantissa (shift + 1)
    if fraction == 0 then zero fmt sign else ofFields fmt sign 0 fraction
  else
    let roundedMantissa :=
      if leading ≥ precision then
        Nat.shiftRight mantissa (leading - precision)
      else
        Nat.shiftLeft mantissa (precision - leading)
    let encodedExponent := Int.toNat (totalExponent + Int.ofNat fmt.exponentBias)
    let fraction := roundedMantissa - pow2 precision
    if encodedExponent > fmt.maxFiniteExpField ||
        (encodedExponent == fmt.maxFiniteExpField &&
          fraction > fmt.maxFiniteFracField) then
      maxFinite fmt sign
    else
      ofFields fmt sign encodedExponent fraction

/-- Round an exact positive magnitude upward, attaching `sign` to the result. -/
def roundDyadicMagnitudeUp (fmt : FloatFormat) (sign : Bool)
    (mantissa : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let leading := Nat.log2 mantissa
  let totalExponent := Int.ofNat leading + exponent
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  if totalExponent > maxNormal then
    nativeOverflow fmt sign
  else if totalExponent < minSubnormal then
    ofFields fmt sign 0 1
  else if totalExponent < minNormal then
    let fraction :=
      match exponent - minSubnormal with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => shiftRightCeilPow2 mantissa (shift + 1)
    packRoundedSubnormal fmt sign (ofFields fmt sign 0 1) fraction
  else
    let roundedMantissa :=
      if leading ≥ precision then
        shiftRightCeilPow2 mantissa (leading - precision)
      else
        Nat.shiftLeft mantissa (precision - leading)
    packRoundedNormal fmt sign (nativeOverflow fmt sign) totalExponent roundedMantissa

/-- Round a positive exact dyadic toward negative infinity. -/
@[inline] def roundDyadicPosDown
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  roundDyadicMagnitudeDown fmt false mantissa exponent

/-- Round a positive exact dyadic toward positive infinity. -/
@[inline] def roundDyadicPosUp
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  roundDyadicMagnitudeUp fmt false mantissa exponent

/-- Round an exact dyadic toward negative infinity. -/
def roundDyadicDown (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else if value.negative then
    roundDyadicMagnitudeUp fmt true value.significand value.exponent
  else
    roundDyadicMagnitudeDown fmt false value.significand value.exponent

/-- Round an exact dyadic toward positive infinity. -/
def roundDyadicUp (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else if value.negative then
    roundDyadicMagnitudeDown fmt true value.significand value.exponent
  else
    roundDyadicMagnitudeUp fmt false value.significand value.exponent

/-- Round an exact dyadic toward zero. -/
def roundDyadicTowardZero (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    roundDyadicMagnitudeDown fmt value.negative value.significand value.exponent

/-- Round an exact dyadic according to an IEEE rounding direction. -/
@[inline] def roundDyadicWithRounding (fmt : FloatFormat) (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) : Model fmt :=
  match mode with
  | .nearestEven => roundDyadic fmt value
  | .towardZero => roundDyadicTowardZero fmt value
  | .towardPositiveInfinity => roundDyadicUp fmt value
  | .towardNegativeInfinity => roundDyadicDown fmt value

end Model
end FloatLib.Floats.Formats.BinaryInterchange
