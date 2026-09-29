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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Basic

/-!
# Executable exact-dyadic comparison

The general comparator aligns significands at a common exponent. The `Internal.compareScalable`
variants first compare leading binary positions, avoiding shifts proportional to a potentially
huge exponent gap. `Comparison.Proof` connects the field-level entry points and normalization
tests to the general comparator; rational ordering laws are in `Dyadic.Order`.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace Dyadic

namespace Internal

/--
Compare two nonzero dyadic magnitudes without allocating across the full exponent gap.

Different leading binary positions decide the result immediately. Equal leading positions imply
that exponent alignment shifts by no more than the difference between the two significand
widths, even when the stored exponents themselves are enormous.
-/
@[inline] def compareNonzeroMagnitudes
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) : Ordering :=
  let leftLeading :=
    leftExponent + Int.ofNat leftSignificand.log2
  let rightLeading :=
    rightExponent + Int.ofNat rightSignificand.log2
  if leftLeading < rightLeading then
    .lt
  else if rightLeading < leftLeading then
    .gt
  else if leftExponent ≤ rightExponent then
    Ord.compare leftSignificand
      (Nat.shiftLeft rightSignificand
        (Int.toNat (rightExponent - leftExponent)))
  else
    Ord.compare
      (Nat.shiftLeft leftSignificand
        (Int.toNat (leftExponent - rightExponent)))
      rightSignificand

/--
Compare exact dyadic fields with alignment shifts bounded by significand widths.

Zero and opposite-sign cases need no magnitude comparison. Same-sign nonzero inputs use their
leading binary positions before any bounded alignment.
-/
@[inline] def compareScalableFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Ordering :=
  if leftSignificand == 0 then
    if rightSignificand == 0 then
      .eq
    else if rightNegative then
      .gt
    else
      .lt
  else if rightSignificand == 0 then
    if leftNegative then .lt else .gt
  else if leftNegative != rightNegative then
    if leftNegative then .lt else .gt
  else
    let magnitude :=
      compareNonzeroMagnitudes leftSignificand leftExponent
        rightSignificand rightExponent
    if leftNegative then magnitude.swap else magnitude

/-- Record-based entry point for exponent-scalable exact-dyadic comparison. -/
@[inline] def compareScalable (left right : Dyadic) : Ordering :=
  compareScalableFields left.negative left.significand left.exponent
    right.negative right.significand right.exponent

end Internal

/--
Compare exact dyadic scalar fields without first allocating either `Dyadic` record.

Format-specific decoders often already expose sign, significand, and exponent separately. This
entry point preserves that flattened representation through exact comparison.
-/
@[inline] def compareFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Ordering :=
  if leftSignificand == 0 && rightSignificand == 0 then
    .eq
  else
    let commonExponent :=
      if leftExponent ≤ rightExponent then leftExponent else rightExponent
    let leftShift := Int.toNat (leftExponent - commonExponent)
    let rightShift := Int.toNat (rightExponent - commonExponent)
    let leftMagnitude := Nat.shiftLeft leftSignificand leftShift
    let rightMagnitude := Nat.shiftLeft rightSignificand rightShift
    let leftInt :=
      if leftNegative then -Int.ofNat leftMagnitude else Int.ofNat leftMagnitude
    let rightInt :=
      if rightNegative then -Int.ofNat rightMagnitude else Int.ofNat rightMagnitude
    Ord.compare leftInt rightInt

/--
Compare two exact dyadic values.

The comparison aligns only to the smaller of the two exponents and then compares signed integers;
it never converts through a host floating-point value.
-/
@[inline] def compare (left right : Dyadic) : Ordering :=
  compareFields left.negative left.significand left.exponent
    right.negative right.significand right.exponent

/--
Compare two nonnegative significand/exponent pairs without constructing signed integers.

Posit and unsigned binary rounding spend most comparisons in this domain. Because the common
exponent is always one of the two input exponents, only the significand at the larger exponent
needs shifting.
-/
@[inline] def compareNonnegativeFields
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) : Ordering :=
  if leftSignificand == 0 && rightSignificand == 0 then
    .eq
  else if leftExponent ≤ rightExponent then
    Ord.compare leftSignificand
      (Nat.shiftLeft rightSignificand
        (Int.toNat (rightExponent - leftExponent)))
  else
    Ord.compare
      (Nat.shiftLeft leftSignificand
        (Int.toNat (leftExponent - rightExponent)))
      rightSignificand

/-- Executable strict comparison without conversion to `Rat` or a host floating-point value. -/
@[inline] def isLess (left right : Dyadic) : Bool :=
  left.compare right == .lt

/-- Executable strict comparison on flattened exact-dyadic fields. -/
@[inline] def isLessFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Bool :=
  compareFields leftNegative leftSignificand leftExponent
      rightNegative rightSignificand rightExponent == .lt

/-- Strict comparison specialized to known-nonnegative scalar fields. -/
@[inline] def isLessNonnegativeFields
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) : Bool :=
  compareNonnegativeFields leftSignificand leftExponent
      rightSignificand rightExponent == .lt

/--
Test whether a nonnegative dyadic is strictly below an integral power of two when the caller
already knows the significand's leading-bit index.

Rounding kernels compute this index to normalize their result fields. Reusing it here avoids an
alignment shift whose temporary size is proportional to the exponent gap.
-/
@[inline] def isLessPowerOfTwoAtLeading
    (significand : Nat) (exponent : Int) (leading : Nat) (power : Int) : Bool :=
  if significand == 0 then
    true
  else
    decide (exponent + Int.ofNat leading < power)

/-- Executable non-strict comparison, derived from the exact strict comparator. -/
@[inline] def isLessOrEqual (left right : Dyadic) : Bool :=
  !isLess right left

/--
Executable numerical equality for possibly unnormalized dyadics.

Structural equality is intentionally unsuitable here because the same number may have several
significand/exponent pairs.
-/
@[inline] def isEqual (left right : Dyadic) : Bool :=
  isLessOrEqual left right && isLessOrEqual right left

/-- Executable non-strict comparison on flattened exact-dyadic fields. -/
@[inline] def isLessOrEqualFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Bool :=
  !isLessFields rightNegative rightSignificand rightExponent
      leftNegative leftSignificand leftExponent

/-- Non-strict comparison specialized to known-nonnegative scalar fields. -/
@[inline] def isLessOrEqualNonnegativeFields
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) : Bool :=
  !isLessNonnegativeFields rightSignificand rightExponent
    leftSignificand leftExponent

end Dyadic
end FloatLib.Numerics
