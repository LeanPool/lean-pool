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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Optimized
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Runtime

/-!
# Two-word multiplication runtime

The partial four-limb product kernel multiplies normal operands in every eligible two-word
layout. The operation dispatcher owns the exact baseline for declined cases. Refinement proofs
are isolated in `Multiplication.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Round and pack a four-limb normal product whose leading set bit is at position `leading`.

The product of two normal significands, or the aligned sum used by fused multiply-add, is
rounded to `fracWidth + 1` bits by shifting out `leading - fracWidth` bits with ties to even. A
magnitude below the normal range, or a rounded result above the largest finite exponent, is
declined.
-/
@[inline] def roundNormalProductOption {fmt : FloatFormat} (sign : Bool) (xExponent yExponent :
  UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt256) (leading : UInt64) : Option (Model fmt) :=
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  if position < UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 1) then
    none
  else
    let rounded :=
      product.roundShiftRightEven128 (leading - UInt64.ofNat fmt.fracWidth).toNat
    let carry := isCarry fmt rounded
    let normalizedPosition := if carry then position + 1 else position
    if UInt64.ofNat (3 * fmt.bias + 2 * fmt.fracWidth - 2) < normalizedPosition then
      none
    else
      some <| packNormal fmt sign
        (normalizedPosition - UInt64.ofNat (fmt.bias + 2 * fmt.fracWidth - 2))
        (normalizeCarry fmt carry rounded)

/-- Multiply two decoded normal significands in fixed limbs. -/
@[inline] def roundNormalLimbOption {fmt : FloatFormat} (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa : FloatLib.Numerics.FixedWord.UInt128) : Option (Model fmt) :=
  let product := FloatLib.Numerics.FixedWord.mul128 xMantissa yMantissa
  roundNormalProductOption sign xExponent yExponent product (UInt64.ofNat product.log2)

/--
Decode two values and try the fixed-limb normal product.

Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def mulNormalLimbOption {fmt : FloatFormat} (x y : Model fmt) : Option (Model
  fmt) :=
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  if xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent == 0 || yExponent == expAllOnes fmt then
    none
  else
    roundNormalLimbOption
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      xExponent yExponent
      (normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo)
      (normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
