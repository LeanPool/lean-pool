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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Runtime
import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Compiler
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Core.Runtime
public import Mathlib.Data.Rat.Cast.Order

/-!
# Native one-word finite division

The native normal-division path serves conventional IEEE formats whose storage and quotient
intermediates fit in `UInt64`. Refinement proofs and the exact-rational specification live in
`Div.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordDiv

open FloatLib.Numerics.FixedWord.RestoringQuotient

/--
Round and pack a normal quotient with `UInt64` significands and an `Int` exponent.

For nonzero significands within the eligible format's width, the function declines if the
leading exponent is outside the normal range before rounding or exceeds its upper bound after
rounding. The public dispatcher handles these cases. The normal exponent bounds
`1 - bias` and `bias` and the encoding offset come from `NativeSmallWord.biasInt`, so the
descriptor contributes no `Nat` power or shift per call.
-/
@[inline] def roundNormalNativeOption (fmt : FloatFormat) (sign : Bool)
    (num den : UInt64) (exponent : Int) : Option (Model fmt) :=
  let bias := NativeSmallWord.biasInt fmt
  let rationalExponent :=
    floorLog2RatWord num den
  let totalExponent := rationalExponent + exponent
  if totalExponent < (1 : Int) - bias || bias < totalExponent then
    none
  else
    let shift :=
      Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    let roundedMantissa :=
      roundScaledQuotient num den shift
    let carry :=
      roundedMantissa == NativeSmallWord.carryBit fmt
    let normalizedExponent :=
      if carry then totalExponent + 1 else totalExponent
    if bias < normalizedExponent then
      none
    else
      let normalizedMantissa :=
        if carry then NativeSmallWord.hiddenBit fmt else roundedMantissa
      let encodedExponent :=
        UInt64.ofNat (Int.toNat (normalizedExponent + bias))
      let fraction :=
        normalizedMantissa - NativeSmallWord.hiddenBit fmt
      some <| NativeSmallWord.ofWord <|
        NativeSmallWord.packFields fmt sign encodedExponent fraction

/--
Decode two normal finite operands and try the one-word quotient path.

The function deliberately declines for zero, subnormal, and exceptional operands. The public
dispatcher retains the exact arbitrary-precision implementation for every declined case.
-/
@[inline] def divNormalOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  NativeSmallWord.withNormalPairOption x y fun sign xExponent yExponent
      xMantissa yMantissa =>
    roundNormalNativeOption fmt sign xMantissa yMantissa
      (Int.ofNat (xExponent - 1).toNat -
        Int.ofNat (yExponent - 1).toNat)

end Model.NativeSmallWordDiv
end FloatLib.Floats.Formats.BinaryInterchange
