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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Arithmetic.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Core

/-!
# Exact dyadic rounding

This is the executable one-rounding boundary for exact binary values. It classifies an exact
dyadic against descriptor-derived overflow, normal, and subnormal regions, retains only the target
significand bits, and applies nearest-even to the discarded part.

Conventional IEEE descriptors may reuse Lean's logical float model as a proof-facing route.
`roundDyadicGeneral` handles custom bias and every supported exceptional-value encoding directly.
The public selector keeps those implementations under one descriptor-level contract.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/--
Round an exact dyadic through Lean's conventional IEEE logical model.

This is the proof-facing specification for formats with ordinary IEEE bias and exceptional-value
encoding. `roundDyadic` below selects it only when `fmt.isIEEE`.
-/
@[inline] def ieeeRoundDyadic (fmt : FloatFormat) (d : Numerics.Dyadic) : Model fmt :=
  ofModel fmt <|
    Float.Model.UnpackedFloat.round (FloatFormat.toModel fmt)
      (modelSign d.negative) d.significand d.exponent

/-- Right shifts preserve a zero mantissa with clear round and sticky bits. -/
theorem zero_extendedMantissa_shiftRight (shift : Nat) :
    (({ mantissa := 0, roundBit := false, stickyBit := false } :
        Float.Model.UnpackedFloat.ExtendedMantissa) >>> shift) =
      { mantissa := 0, roundBit := false, stickyBit := false } := by
  induction shift with
  | zero => rfl
  | succ shift ih =>
      change Nat.repeat Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne shift _ = _ at ih
      change Nat.repeat Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne (Nat.succ shift)
        _ = _
      rw [Nat.repeat, ih]
      rfl

/-- Rounding in Lean's IEEE model preserves signed zero for every model format. -/
@[simp] theorem round_exact_zero
    (spec : Float.Model.Format) (sign : Float.Model.UnpackedFloat.Sign) (exponent : Int) :
    Float.Model.UnpackedFloat.round spec sign 0 exponent = .zero sign := by
  unfold Float.Model.UnpackedFloat.round Float.Model.UnpackedFloat.decreaseExponent
  simp only [Nat.zero_shiftLeft]
  unfold Float.Model.UnpackedFloat.roundWithAccuracy
    Float.Model.UnpackedFloat.shiftToTargetExponent Float.Model.UnpackedFloat.shiftToExponent
  simp (config := { zeta := true }) only [zero_extendedMantissa_shiftRight,
    Float.Model.UnpackedFloat.ExtendedMantissa.roundedMantissa,
    Float.Model.UnpackedFloat.ExtendedMantissa.accuracy,
    Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy,
    Float.Model.UnpackedFloat.Accuracy.roundToNearestEven]
  split
  · rfl
  · contradiction

/-- Rounding an exact zero through Lean's logical model packs the corresponding signed zero. -/
@[simp] theorem ieeeRoundDyadic_significand_zero (fmt : FloatFormat) (sign : Bool)
    (exponent : Int) :
    ieeeRoundDyadic fmt { negative := sign, significand := 0, exponent := exponent } =
      ofModel fmt (.zero (modelSign sign)) := by
  simp [ieeeRoundDyadic]

/-- Default overflow result: infinity, NaN, or saturation according to the encoding. -/
@[inline] def nativeOverflow (fmt : FloatFormat) (sign : Bool) : Model fmt :=
  match fmt.encoding with
  | .ieee => if sign then negInf fmt else posInf fmt
  | .finiteMaxNaN | .finiteUnsignedZero => invalidResult fmt
  | .finite => maxFinite fmt sign

/-- Conventional IEEE native overflow is the usual signed infinity. -/
@[simp] theorem nativeOverflow_eq_signedInf_of_isIEEE
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) :
    nativeOverflow fmt sign = if sign then negInf fmt else posInf fmt := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  cases sign <;> simp [nativeOverflow, hencoding]

/--
Overflow result for a signed magnitude under a known rounding direction.

IEEE 754-2019 Section 7.4 rounds an overflowing magnitude to the format's overflow value when
the direction carries the magnitude upward and to the largest finite value when it carries the
magnitude downward. `roundMagnitudeUp` records that direction after the sign has been taken into
account: toward zero never rounds up, toward positive infinity rounds a positive magnitude up, and
toward negative infinity rounds a negative magnitude up. Nearest modes always round up. The
directed and policy rounders share this definition so that a finite-with-NaN encoding saturates
in the truncating direction under both engines.
-/
@[inline] def directedOverflow (fmt : FloatFormat) (sign roundMagnitudeUp : Bool) :
    Model fmt :=
  if roundMagnitudeUp then nativeOverflow fmt sign else maxFinite fmt sign

/--
Pack a rounded subnormal significand.

The caller supplies the zero result because some directed algorithms know that a nonzero exact
input must round to the least subnormal, while rational rounding uses the format's zero policy.
Keeping the common boundary logic here prevents those algorithms from drifting apart.
-/
@[inline] def packRoundedSubnormal (fmt : FloatFormat) (sign : Bool)
    (zeroResult : Model fmt) (fraction : Nat) : Model fmt :=
  if fraction == 0 then
    zeroResult
  else if fraction ≥ pow2 fmt.fracWidth then
    ofFields fmt sign 1 0
  else
    ofFields fmt sign 0 fraction

/--
Pack a rounded normal significand, including carry into the exponent and descriptor-specific
overflow words.

This helper accepts an already rounded significand. Callers remain responsible for proving
that their rounding decision and supplied overflow result match the requested policy.
-/
@[inline] def packRoundedNormal (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt) (totalExponent : Int) (roundedMantissa : Nat) : Model fmt :=
  let carry := roundedMantissa == pow2 (fmt.fracWidth + 1)
  let normalizedExponent := if carry then totalExponent + 1 else totalExponent
  let normalizedMantissa := if carry then pow2 fmt.fracWidth else roundedMantissa
  if normalizedExponent > fmt.maxNormalExponent then
    overflow
  else
    let encodedExponent :=
      Int.toNat (normalizedExponent + Int.ofNat fmt.exponentBias)
    let encodedFraction := normalizedMantissa - pow2 fmt.fracWidth
    if encodedExponent > fmt.maxFiniteExpField ||
        (encodedExponent == fmt.maxFiniteExpField &&
          encodedFraction > fmt.maxFiniteFracField) then
      overflow
    else
      ofFields fmt sign encodedExponent encodedFraction

/--
Round an exact dyadic according to the complete format descriptor.

Only the retained significand and the discarded-bit rounding decision are materialized. The
implementation supports custom exponent bias and every `FloatFormat.Encoding`; it does not pass
through Lean's conventional IEEE model.
-/
@[inline] def roundDyadicGeneral (fmt : FloatFormat) (d : Numerics.Dyadic) : Model fmt :=
  if d.significand == 0 then
    zero fmt d.negative
  else
    let leading := d.significand.log2
    let totalExponent := (leading : Int) + d.exponent
    if totalExponent > fmt.maxNormalExponent then
      nativeOverflow fmt d.negative
    else if totalExponent < fmt.minNormalExponent then
      let fraction :=
        match d.exponent - fmt.minSubnormalExponent with
        | .ofNat shift => d.significand <<< shift
        | .negSucc shift => roundShiftRightEven d.significand (shift + 1)
      packRoundedSubnormal fmt d.negative (zero fmt d.negative) fraction
    else
      let roundedMantissa :=
        if fmt.fracWidth ≤ leading then
          roundShiftRightEven d.significand (leading - fmt.fracWidth)
        else
          d.significand <<< (fmt.fracWidth - leading)
      packRoundedNormal fmt d.negative (nativeOverflow fmt d.negative)
        totalExponent roundedMantissa

/--
Round an exact dyadic to `Model fmt` using round-to-nearest, ties-to-even.

Conventional IEEE formats retain the established logical-model specification and its checked
native implementation. Other static formats use the descriptor-aware integer algorithm directly.
-/
@[inline] def roundDyadic (fmt : FloatFormat) (d : Numerics.Dyadic) : Model fmt :=
  if fmt.isIEEE then ieeeRoundDyadic fmt d else roundDyadicGeneral fmt d

/--
Exact addition at the binary-format API boundary.

The implementation is shared with posit arithmetic and exact reductions through
`Numerics.Dyadic.add`; binary operations keep this name so their specifications read naturally.
No rounding occurs until the result is passed to `roundDyadic`.
-/
@[inline] def addDyadic (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  Numerics.Dyadic.add a b

end Model

end FloatLib.Floats.Formats.BinaryInterchange
