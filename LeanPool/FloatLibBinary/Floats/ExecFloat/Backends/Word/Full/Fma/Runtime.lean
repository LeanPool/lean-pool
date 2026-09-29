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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Runtime

/-!
# Native binary64 fused multiply-add runtime

The accepted paths align finite normal operands in two native limbs and round the exact sum or
difference once. Declined cases retain the generic exact finite kernel. Correctness proofs are
isolated in `Fma.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

/-- Shift a normal binary64 significand into the product's two-word coordinate. -/
@[inline] def alignFmaAddend (mantissa : UInt64) : FloatLib.Numerics.FixedWord.UInt128 :=
  FloatLib.Numerics.FixedWord.UInt128.shiftLeft { hi := 0, lo := mantissa } 52

/-- Leading-bit position of a binary64 FMA magnitude, which needs at most 107 bits. -/
@[inline] def fmaLeading (magnitude : FloatLib.Numerics.FixedWord.UInt128) : UInt64 :=
  UInt64.ofNat (FloatLib.Numerics.FixedWord.UInt128.log2 magnitude)

/--
Try the aligned normal binary64 FMA path when the product and addend have the same sign.

The accepted exact magnitude is
`xMantissa * yMantissa + zMantissa * 2^52`. The final result is still rounded only once.
-/
@[inline] def fmaNormalSameSignAlignedOption (x y z : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let zBits := toUInt64 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  if xExponent == 0 || xExponent == 0x7ff ||
      yExponent == 0 || yExponent == 0x7ff ||
      zExponent == 0 || zExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let zMantissa := finiteMantissa zExponent (fracField zBits)
    let productScale := finiteScale xExponent + finiteScale yExponent
    let zProductScale := finiteScale zExponent + 1074
    let productSign := Bool.xor (signBit xBits) (signBit yBits)
    let zSign := signBit zBits
    if productSign != zSign || productScale + 52 != zProductScale then
      none
    else
      let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
      let sum := FloatLib.Numerics.FixedWord.add128 product (alignFmaAddend zMantissa)
      if sum.carry != 0 then
        none
      else
        roundNormalProductOption productSign xExponent yExponent sum.value
          (fmaLeading sum.value)

/--
Try the aligned normal binary64 FMA path when the product and addend have opposite signs.

Exact cancellation and differences with leading-bit position below 53 are declined. The product
rounder checks the result exponent; declined cases use the generic finite kernel.
-/
@[inline] def fmaNormalOppositeSignAlignedOption (x y z : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let zBits := toUInt64 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  if xExponent == 0 || xExponent == 0x7ff ||
      yExponent == 0 || yExponent == 0x7ff ||
      zExponent == 0 || zExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let zMantissa := finiteMantissa zExponent (fracField zBits)
    let productScale := finiteScale xExponent + finiteScale yExponent
    let zProductScale := finiteScale zExponent + 1074
    let productSign := Bool.xor (signBit xBits) (signBit yBits)
    let zSign := signBit zBits
    if productSign == zSign || productScale + 52 != zProductScale then
      none
    else
      let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
      let aligned := alignFmaAddend zMantissa
      if product == aligned then
        none
      else
        let productLess := FloatLib.Numerics.FixedWord.UInt128.less product aligned
        let magnitude :=
          if productLess then
            FloatLib.Numerics.FixedWord.UInt128.sub aligned product
          else
            FloatLib.Numerics.FixedWord.UInt128.sub product aligned
        let leading := fmaLeading magnitude
        if leading < 53 then
          none
        else
          roundNormalProductOption (if productLess then zSign else productSign)
            xExponent yExponent magnitude leading

/-- Use both native aligned paths before the existing exact finite FMA kernel. -/
@[inline] def fmaFiniteFastImplOption (x y z : Value) : Option Value :=
  match fmaNormalSameSignAlignedOption x y z with
  | some result => some result
  | none =>
      match fmaNormalOppositeSignAlignedOption x y z with
      | some result => some result
      | none => fmaFiniteImplOption x y z

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
