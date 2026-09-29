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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ProductRound.Runtime

/-!
# Native two-word finite multiplication

This is the executable `64 x 64 -> 128` normal-product tier for one-word IEEE formats whose
significand product needs two words. Refinement proofs live in `TwoWordMul.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeTwoWordMul

open NativeSmallWord

/-- Capacity contract for a one-storage-word format whose product needs two native words. -/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧
    fmt.bitWidth ≤ 64 ∧
    32 ≤ fmt.fracWidth ∧
    fmt.fracWidth ≤ 62

/--
Two-word eligibility is decided from the descriptor fields; the conditional form is inlined and
can be simplified for a closed format (see `NativeSmallWord.StorageEligible`).
-/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64 ∧ 32 ≤ fmt.fracWidth ∧ fmt.fracWidth ≤ 62 then
    isTrue h
  else
    isFalse h

/-- Leading-bit position `2 * fracWidth` or `2 * fracWidth + 1` of a normalized two-word product. -/
@[inline] def productLeading (fmt : FloatFormat)
    (product : FloatLib.Numerics.FixedWord.UInt128) : UInt64 :=
  let lower := UInt64.ofNat (2 * fmt.fracWidth)
  let threshold :=
    (1 : UInt64) <<<
      UInt64.ofNat (2 * fmt.fracWidth + 1 - 64)
  if product.hi < threshold then lower else lower + 1

/-- Round an exact two-word product of two normal finite significands. -/
@[inline] def roundNormalProductOption (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : UInt64) :
    Option (Model fmt) :=
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let leading := productLeading fmt product
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold :=
    UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1)
  if position < normalThreshold then
    none
  else
    let rounded :=
      product.roundShiftRightEven
        (leading - UInt64.ofNat fmt.fracWidth).toNat
    NativeWordProduct.finishOption fmt sign position rounded

/-- Decode two normal finite values and try the reusable two-word product path. -/
@[inline] def mulNormalOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  NativeSmallWord.withNormalPairOption x y (roundNormalProductOption fmt)

end Model.NativeTwoWordMul
end FloatLib.Floats.Formats.BinaryInterchange
