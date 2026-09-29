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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
public import LeanPool.FloatLibBinary.Numerics.IEEEStatus

/-!
# IEEE exception status for format-parameterized `Model`

The value operations remain pure and explicit about their rounding mode. This module pairs those
values with the five IEEE exception indicators. Tininess is detected after rounding, and underflow
is raised exactly when a tiny result is inexact.

Overflow is classified from the precision-rounded result with an unbounded exponent range, as in
IEEE 754-2019 §7.4 and the GNU MPFR manual's exception definition:
<https://doi.org/10.1109/IEEESTD.2019.8766229> and
<https://www.mpfr.org/mpfr-current/mpfr.html#Exceptions>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- The shared IEEE exception indicators, also used by decimal arithmetic. -/
abbrev IEEEStatus := Numerics.IEEEStatus

namespace IEEEStatus

/-- No exception was raised. -/
def clear : IEEEStatus := {}

end IEEEStatus

/-- A format-parameterized executable value paired with its IEEE exception status. -/
structure IEEEOutcome (fmt : FloatFormat) where
  /-- Delivered floating-point result. -/
  value : Model fmt
  /-- Exception indicators raised while computing `value`. -/
  status : IEEEStatus
  deriving Repr, DecidableEq, Inhabited

/--
Pair a value with either the invalid-operation flag or a clear status.

Exceptional arithmetic paths share this constructor so the value and the Boolean invalid
condition remain visible without duplicating conditional record construction.
-/
@[inline] def outcomeWithInvalid {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) : IEEEOutcome fmt :=
  { value
    status := if invalid then { invalid := true } else .clear }

/-- Whether a finite rounded result is zero or subnormal. -/
@[inline] def isTinyAfterRounding {fmt : FloatFormat} (x : Model fmt) : Bool :=
  isFinite x && expField x == 0

/-- Exact positive value of the smallest normal number in `fmt`. -/
def minNormalDyadic (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := pow2 fmt.fracWidth
    exponent := fmt.minSubnormalExponent }

/--
Largest positive number below `minNormalDyadic fmt` on the format's precision grid with an
unbounded exponent range. Its distance from the smallest normal is half one subnormal step.
-/
def underflowPredecessor (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := 2 * pow2 fmt.fracWidth - 1
    exponent := fmt.minSubnormalExponent - 1 }

/--
Positive boundary used by after-rounding tininess detection.

Tininess after rounding is determined by first rounding to the destination precision with an
unbounded exponent range. Immediately below the smallest normal value that unbounded grid has
half the subnormal spacing, so its midpoint is one quarter of a subnormal step below
`minNormal`. The midpoint itself rounds to the even `minNormal` significand and is not tiny.
-/
def underflowMidpoint (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := 4 * pow2 fmt.fracWidth - 1
    exponent := fmt.minSubnormalExponent - 2 }

/-- Whether a directed mode rounds a result with this sign away from zero. -/
@[inline] def roundsAwayFromZero (mode : IEEERoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .nearestEven | .towardZero => false
  | .towardPositiveInfinity => !negative
  | .towardNegativeInfinity => negative

/--
Whether a dyadic result is tiny after rounding to the destination precision with an unbounded
exponent range.

Most tiny results are visible directly as zero or subnormal encodings. A result delivered as
`minNormal` needs a mode-sensitive boundary:

* nearest-even uses the midpoint between `minNormal` and its unbounded-grid predecessor;
* rounding away from zero is tiny through that predecessor;
* rounding toward zero is tiny for every magnitude strictly below `minNormal`.
-/
def dyadicIsTinyAfterRounding (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (rounded : Model fmt) : Bool :=
  if isTinyAfterRounding rounded then
    true
  else
    let magnitude := { exact with negative := false }
    match mode with
    | .nearestEven =>
        cmpDyadic magnitude (underflowMidpoint fmt) == .lt
    | .towardZero =>
        cmpDyadic magnitude (minNormalDyadic fmt) == .lt
    | .towardPositiveInfinity | .towardNegativeInfinity =>
        if roundsAwayFromZero mode exact.negative then
          cmpDyadic magnitude (underflowPredecessor fmt) != .gt
        else
          cmpDyadic magnitude (minNormalDyadic fmt) == .lt

/-- Exact positive dyadic value of the largest finite number in `fmt`. -/
def maxFiniteDyadic (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := pow2 fmt.fracWidth + fmt.maxFiniteFracField
    exponent := fmt.maxNormalExponent - Int.ofNat fmt.fracWidth }

/-- Whether an exact dyadic magnitude exceeds the finite range of `fmt`. -/
def dyadicMagnitudeOverflows (fmt : FloatFormat) (exact : Numerics.Dyadic) : Bool :=
  cmpDyadic { exact with negative := false } (maxFiniteDyadic fmt) == .gt

/--
Positive midpoint between the largest finite value and the next magnitude on the same binary grid.

Nearest-even overflow is decided at this boundary. The midpoint itself overflows exactly when the
largest finite significand is odd, because the conceptual next significand is then even.
-/
def overflowMidpoint (fmt : FloatFormat) : Numerics.Dyadic :=
  let maximum := maxFiniteDyadic fmt
  { negative := false
    significand := 2 * maximum.significand + 1
    exponent := maximum.exponent - 1 }

/-- First grid magnitude beyond the largest finite value. -/
def overflowLimit (fmt : FloatFormat) : Numerics.Dyadic :=
  let maximum := maxFiniteDyadic fmt
  { negative := false
    significand := maximum.significand + 1
    exponent := maximum.exponent }

/-- Whether the largest finite significand is odd. -/
@[inline] def maxFiniteMantissaOdd (fmt : FloatFormat) : Bool :=
  (maxFiniteDyadic fmt).significand % 2 == 1

/-- Whether nearest-even rounding of an exact dyadic magnitude signals overflow. -/
def dyadicNearestEvenOverflows (fmt : FloatFormat) (exact : Numerics.Dyadic) : Bool :=
  match cmpDyadic { exact with negative := false } (overflowMidpoint fmt) with
  | .gt => true
  | .eq => maxFiniteMantissaOdd fmt
  | .lt => false

/-- Whether truncating an exact dyadic magnitude still exceeds the finite range. -/
def dyadicTruncationOverflows (fmt : FloatFormat) (exact : Numerics.Dyadic) : Bool :=
  cmpDyadic { exact with negative := false } (overflowLimit fmt) != .lt

/--
Whether rounding an exact dyadic signals overflow.

Nearest-even uses the top finite midpoint. A directed mode that increases the magnitude overflows
above `maxFinite`; a mode that decreases the magnitude overflows only at `overflowLimit`. For
conventional IEEE encodings, that limit starts the next binade. For encodings that reserve a
terminal fraction pattern, it can lie within the same binade.
-/
def dyadicRoundingOverflows (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) : Bool :=
  match mode with
  | .nearestEven => dyadicNearestEvenOverflows fmt exact
  | .towardZero => dyadicTruncationOverflows fmt exact
  | .towardPositiveInfinity =>
      if exact.negative then
        dyadicTruncationOverflows fmt exact
      else
        dyadicMagnitudeOverflows fmt exact
  | .towardNegativeInfinity =>
      if exact.negative then
        dyadicMagnitudeOverflows fmt exact
      else
        dyadicTruncationOverflows fmt exact

/--
Classify rounding an exact dyadic to `rounded` under `mode`.

Finite results use the proof-guided exact decoder. An exceptional `rounded` argument is classified
explicitly as overflow or invalid; it is never treated as a clear status.
-/
def dyadicRoundingStatus (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) : IEEEStatus :=
  if dyadicRoundingOverflows fmt mode exact then
    { overflow := true, inexact := true }
  else if hfinite : isFinite rounded = true then
    let actual := finiteDyadic rounded hfinite
    let inexact := cmpDyadic exact actual != .eq
    { underflow := dyadicIsTinyAfterRounding fmt mode exact rounded && inexact
      inexact := inexact }
  else if isInf rounded then
    { overflow := true, inexact := true }
  else
    { invalid := true }

/-- Exact equality between `(numerator / denominator) * 2^exponent` and a signed dyadic. -/
def rationalEqualsDyadicScaled (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (value : Numerics.Dyadic) : Bool :=
  Numerics.RationalBinary.compareDyadicScaledOption sign numerator denominator exponent value ==
    some .eq

/-- Whether a positive scaled rational magnitude exceeds the finite range of `fmt`. -/
def rationalMagnitudeOverflowsScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  if denominator == 0 || numerator == 0 then
    false
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let totalExponent := rationalExponent + exponent
    let maximumExponent := fmt.maxNormalExponent
    if totalExponent < maximumExponent then
      false
    else if totalExponent > maximumExponent then
      true
    else
      let maximum := maxFiniteDyadic fmt
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator
          (denominator * maximum.significand) (exponent - maximum.exponent)
      scaled.1 > scaled.2

/-- Whether a positive rational magnitude exceeds the finite range of `fmt`. -/
def rationalMagnitudeOverflows (fmt : FloatFormat) (numerator denominator : Nat) : Bool :=
  rationalMagnitudeOverflowsScaled fmt numerator denominator 0

/-- Whether nearest-even rounding of a positive scaled rational signals overflow. -/
def rationalNearestEvenOverflowsScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  match Numerics.RationalBinary.compareDyadicScaledOption false numerator denominator exponent
      (overflowMidpoint fmt) with
  | some .gt => true
  | some .eq => maxFiniteMantissaOdd fmt
  | some .lt | none => false

/-- Whether truncating a scaled rational magnitude still exceeds the finite range. -/
def rationalTruncationOverflowsScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  match Numerics.RationalBinary.compareDyadicScaledOption false numerator denominator exponent
      (overflowLimit fmt) with
  | some .gt | some .eq => true
  | some .lt | none => false

/--
Whether rounding an exact signed scaled rational signals overflow.

The sign determines whether a directed mode increases or decreases magnitude. Magnitude-increasing
rounding overflows above `maxFinite`; truncating rounding uses `overflowLimit`.
-/
def rationalRoundingOverflowsScaled (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) (numerator denominator : Nat) (exponent : Int) : Bool :=
  match mode with
  | .nearestEven => rationalNearestEvenOverflowsScaled fmt numerator denominator exponent
  | .towardZero =>
      rationalTruncationOverflowsScaled fmt numerator denominator exponent
  | .towardPositiveInfinity =>
      if sign then
        rationalTruncationOverflowsScaled fmt numerator denominator exponent
      else
        rationalMagnitudeOverflowsScaled fmt numerator denominator exponent
  | .towardNegativeInfinity =>
      if sign then
        rationalMagnitudeOverflowsScaled fmt numerator denominator exponent
      else
        rationalTruncationOverflowsScaled fmt numerator denominator exponent

/-- Whether rounding an exact rational signals overflow. -/
def rationalRoundingOverflows (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) (numerator denominator : Nat) : Bool :=
  rationalRoundingOverflowsScaled fmt mode sign numerator denominator 0

/--
Whether a scaled rational result is tiny after rounding to the destination precision with an
unbounded exponent range.

As with dyadics, an encoded zero or subnormal is tiny. A result delivered as `minNormal` uses the
nearest midpoint, the unbounded-grid predecessor, or `minNormal` itself according to the rounding
direction and sign.
-/
def rationalIsTinyAfterRoundingScaled (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (rounded : Model fmt) : Bool :=
  if isTinyAfterRounding rounded then
    true
  else
    let boundary :=
      match mode with
      | .nearestEven => underflowMidpoint fmt
      | .towardZero => minNormalDyadic fmt
      | .towardPositiveInfinity | .towardNegativeInfinity =>
          if roundsAwayFromZero mode sign then
            underflowPredecessor fmt
          else
            minNormalDyadic fmt
    match Numerics.RationalBinary.compareDyadicScaledOption
        false numerator denominator exponent boundary with
    | some .lt => true
    | some .eq => roundsAwayFromZero mode sign
    | some .gt | none => false

/--
Classify rounding an exact scaled signed rational to `rounded` under `mode`.

For a nonzero denominator, finite results are compared with the exact rational. Exceptional
results are classified as overflow or invalid, as in `dyadicRoundingStatus`. Division handles a
zero denominator before calling this classifier.
-/
def rationalRoundingStatusScaled (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) : IEEEStatus :=
  if rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent then
    { overflow := true, inexact := true }
  else if hfinite : isFinite rounded = true then
    let actual := finiteDyadic rounded hfinite
    let inexact :=
      !(rationalEqualsDyadicScaled sign numerator denominator exponent actual)
    { underflow :=
        rationalIsTinyAfterRoundingScaled fmt mode sign numerator denominator exponent rounded &&
          inexact
      inexact := inexact }
  else if isInf rounded then
    { overflow := true, inexact := true }
  else
    { invalid := true }

/-- Classify rounding an exact signed rational to `rounded` under `mode`. -/
def rationalRoundingStatus (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (rounded : Model fmt) : IEEEStatus :=
  rationalRoundingStatusScaled fmt mode sign numerator denominator 0 rounded

/-- Addition with an explicit rounding direction and IEEE exception status. -/
def addWithStatus {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  match toDyadicOption x, toDyadicOption y with
  | some dx, some dy =>
      let exact := addDyadic dx dy
      let value := addWithRounding mode x y
      { value, status := dyadicRoundingStatus fmt mode exact value }
  | _, _ =>
      let value := addWithRounding mode x y
      let hasNaN := isNaN x || isNaN y
      let generatedInvalid := isInf x && isInf y && signBit x != signBit y
      let invalid := isSNaN x || isSNaN y || (!hasNaN && generatedInvalid)
      outcomeWithInvalid value invalid

/-- Subtraction with an explicit rounding direction and IEEE exception status. -/
def subWithStatus {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  addWithStatus x (neg y) mode

/-- Multiplication with an explicit rounding direction and IEEE exception status. -/
def mulWithStatus {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  match toDyadicOption x, toDyadicOption y with
  | some dx, some dy =>
      let exact : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let value := mulWithRounding mode x y
      { value, status := dyadicRoundingStatus fmt mode exact value }
  | _, _ =>
      let value := mulWithRounding mode x y
      let hasNaN := isNaN x || isNaN y
      let generatedInvalid := (isInf x && isZero y) || (isInf y && isZero x)
      let invalid := isSNaN x || isSNaN y || (!hasNaN && generatedInvalid)
      outcomeWithInvalid value invalid

/-- Division with an explicit rounding direction and IEEE exception status. -/
def divWithStatus {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  match toDyadicOption x, toDyadicOption y with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dy.significand == 0 then
        if dx.significand == 0 then
          outcomeWithInvalid (invalidResult fmt) true
        else
          { value := nativeOverflow fmt sign
            status := { divideByZero := true } }
      else if dx.significand == 0 then
        { value := zero fmt sign, status := .clear }
      else
        let exponentDifference := dx.exponent - dy.exponent
        let value :=
          roundRatWithRoundingScaled fmt mode sign dx.significand dy.significand
            exponentDifference
        { value
          status :=
            rationalRoundingStatusScaled fmt mode sign dx.significand dy.significand
              exponentDifference value }
  | _, _ =>
      let value := divWithRounding mode x y
      let hasNaN := isNaN x || isNaN y
      let generatedInvalid := isInf x && isInf y
      let invalid := isSNaN x || isSNaN y || (!hasNaN && generatedInvalid)
      outcomeWithInvalid value invalid

/--
Fused multiply-add with an explicit rounding direction and IEEE exception status.

IEEE 754-2019 Section 7.2 leaves it implementation defined whether `fma(0, ∞, c)` signals invalid
when `c` is a quiet NaN. This implementation signals invalid for that case: the invalid product
`0 × ∞` is reported whether or not the addend is a quiet NaN, whereas `addWithStatus` and
`mulWithStatus` only report an operand-generated invalid operation when no operand is a NaN.
-/
def fmaWithStatus {fmt : FloatFormat} (x y z : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  match toDyadicOption x, toDyadicOption y, toDyadicOption z with
  | some dx, some dy, some dz =>
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let exact := addDyadic product dz
      let value := fmaWithRounding mode x y z
      { value, status := dyadicRoundingStatus fmt mode exact value }
  | _, _, _ =>
      let value := fmaWithRounding mode x y z
      let hasNaN := isNaN x || isNaN y || isNaN z
      let invalidProduct := (isInf x || isInf y) && (isZero x || isZero y)
      let productIsInf := (isInf x || isInf y) && !(isZero x || isZero y)
      let oppositeInfiniteAddend :=
        productIsInf && isInf z && signBit z != Bool.xor (signBit x) (signBit y)
      let invalid :=
        isSNaN x || isSNaN y || isSNaN z ||
          invalidProduct || (!hasNaN && oppositeInfiniteAddend)
      outcomeWithInvalid value invalid

/--
Whether a nonnegative dyadic has an exact dyadic square root.

When the exponent is odd, one factor of two moves into the significand. The square root is dyadic
exactly when the resulting significand is a perfect square.
-/
@[inline] def dyadicSquareRootIsExact (exact : Numerics.Dyadic) : Bool :=
  let exponentOdd := exact.exponent % 2 != 0
  let mantissa := if exponentOdd then exact.significand * 2 else exact.significand
  let root := Nat.sqrt mantissa
  root * root == mantissa

/-- Square root with an explicit rounding direction and IEEE exception status. -/
def sqrtWithStatus {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome fmt :=
  let value := sqrtWithRounding mode x
  if hnan : isNaN x then
    outcomeWithInvalid value (isSNaN x)
  else if isZero x then
    outcomeWithInvalid value false
  else if signBit x then
    outcomeWithInvalid value true
  else if hinf : isInf x then
    outcomeWithInvalid value false
  else
    let hfinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
        (Bool.eq_false_of_not_eq_true hnan)
        (Bool.eq_false_of_not_eq_true hinf)
    let exact := finiteDyadic x hfinite
    let inexact := !dyadicSquareRootIsExact exact
    -- On nonnegative inputs, comparing `sqrt exact` with a positive boundary is equivalent to
    -- comparing `exact` with its square, so no approximate square-root value enters the test.
    let tiny :=
      if isTinyAfterRounding value then
        true
      else
        let boundary :=
          match mode with
          | .nearestEven => underflowMidpoint fmt
          | .towardZero | .towardNegativeInfinity => minNormalDyadic fmt
          | .towardPositiveInfinity => underflowPredecessor fmt
        let boundarySquared : Numerics.Dyadic :=
          { negative := false
            significand := boundary.significand * boundary.significand
            exponent := boundary.exponent + boundary.exponent }
        match cmpDyadic { exact with negative := false } boundarySquared with
        | .lt => true
        | .eq => roundsAwayFromZero mode false
        | .gt => false
    { value
      status :=
        { underflow := tiny && inexact
          inexact := inexact } }

end Model
end FloatLib.Floats.Formats.BinaryInterchange
