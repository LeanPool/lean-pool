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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ProductRound.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime
public import Mathlib.Data.Rat.Cast.Order

/-!
# Native one-word finite multiplication

The executable normal multiplication path here serves conventional IEEE formats whose storage,
exponent, and significand intermediates fit in `UInt64`. Refinement proofs live in `Mul.Proof`.

The kernel declines exceptional, zero, and subnormal operands, products below the normal threshold
before rounding, and overflow after rounding. The dispatcher handles those cases with the generic
implementation. Each accepted result agrees with its correctly rounded finite-product result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordMul

open NativeSmallWord

/--
Capacity contract for exact `UInt64` normal multiplication.

Two normalized significands of at most 32 bits have an exact product of at most 64 bits. This is one
fraction bit wider
than the conservative contract shared with native division.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧
    fmt.bitWidth ≤ 64 ∧
    fmt.expWidth ≤ 30 ∧
    fmt.fracWidth ≤ 31

/--
Product eligibility is decided from the descriptor fields; the conditional form is inlined and
can be simplified for a closed format (see `NativeSmallWord.StorageEligible`).
-/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64 ∧ fmt.expWidth ≤ 30 ∧ fmt.fracWidth ≤ 31 then
    isTrue h
  else
    isFalse h

/-- Decline sentinel at bit 63, above every storage word admitted by `Eligible`. -/
@[inline] def declineWord : UInt64 :=
  (1 : UInt64) <<< 63

/--
Round an exact product of two normal finite significands in native words.

For eligible formats and normalized operands, `none` means the product is below the normal
threshold before rounding or overflows after rounding. These cases use the generic rounder.
-/
@[inline] def roundNormalProductOption (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64) :
    Option (Model fmt) :=
  let product := xMantissa * yMantissa
  let leading := product.log2
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold :=
    biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1
  if position < normalThreshold then
    none
  else
    let rounded :=
      FloatLib.Numerics.FixedWord.roundShiftRightEven product
        (leading - UInt64.ofNat fmt.fracWidth).toNat
    NativeWordProduct.finishOption fmt sign position rounded

/--
Word-valued execution view of `roundNormalProductOption`.

The high decline bit is reserved as a sentinel. Every successful result is normal and cannot use
that word for an eligible format.
-/
@[inline] def roundNormalProductWord (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64) : UInt64 :=
  let product := xMantissa * yMantissa
  let leading := product.log2
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold :=
    biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1
  if position < normalThreshold then
    declineWord
  else
    let rounded :=
      FloatLib.Numerics.FixedWord.roundShiftRightEven product
        (leading - UInt64.ofNat fmt.fracWidth).toNat
    NativeWordProduct.finishWord fmt declineWord sign position rounded

/--
Decode two normal finite values and try the reusable one-word product path.

Exceptional, zero, and subnormal operands return `none` before any significand arithmetic.
-/
@[inline] def mulNormalOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  NativeSmallWord.withNormalPairOption x y (roundNormalProductOption fmt)

/--
Word-valued execution view of `mulNormalOption`.

Successful results stay in native fields until the final packed word. `declineWord` means the
caller must use the general exact path.
-/
@[inline] def mulNormalWord {fmt : FloatFormat}
    (x y : Model fmt) : UInt64 :=
  let xBits := NativeSmallWord.toWord x
  let yBits := NativeSmallWord.toWord y
  let xExponent := NativeSmallWord.exponentField fmt xBits
  let yExponent := NativeSmallWord.exponentField fmt yBits
  let allOnes := NativeSmallWord.exponentMask fmt
  if xExponent == 0 || xExponent == allOnes ||
      yExponent == 0 || yExponent == allOnes then
    declineWord
  else
    let xMantissa :=
      NativeSmallWord.fractionField fmt xBits ||| hiddenBit fmt
    let yMantissa :=
      NativeSmallWord.fractionField fmt yBits ||| hiddenBit fmt
    roundNormalProductWord fmt
      (Bool.xor
        (NativeSmallWord.signField fmt xBits)
        (NativeSmallWord.signField fmt yBits))
      xExponent yExponent xMantissa yMantissa

end Model.NativeSmallWordMul
end FloatLib.Floats.Formats.BinaryInterchange
