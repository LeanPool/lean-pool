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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Multiplication.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime

/-!
# Two-word fused multiply-add runtime

Normal inputs whose product and addend have the same sign and the supported alignment use a
four-word exact sum and one nearest-even rounding step. The complete finite candidate chain then
uses the width-generic exact
kernel for other finite inputs. Correctness proofs live in `Fma.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/-- Shift a normal significand by `fracWidth` bits into the product's four-word coordinate. -/
@[inline] def alignFmaAddend (fmt : FloatFormat)
    (mantissa : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt256 :=
  FloatLib.Numerics.FixedWord.UInt256.ofUInt128ShiftedLeft mantissa fmt.fracWidth

/--
Try the all-native same-sign, exactly aligned normal FMA path.

The sign test uses the public carrier's most-significant bit before native-word decoding, keeping
declined opposite-sign cases cheap. The addend is accepted when its scale equals the product scale
plus `fracWidth`, so both operands share the four-word coordinate of the product rounder.
-/
@[inline] def fmaNormalSameSignAlignedOption {fmt : FloatFormat} (x y z : Model fmt) :
    Option (Model fmt) :=
  let productSign := Bool.xor x.bits.msb y.bits.msb
  let zSign := z.bits.msb
  if productSign != zSign then
    none
  else
    let xWords := toWords x
    let yWords := toWords y
    let zWords := toWords z
    let xExponent := expField fmt xWords.hi
    let yExponent := expField fmt yWords.hi
    let zExponent := expField fmt zWords.hi
    if xExponent == 0 || xExponent == expAllOnes fmt ||
        yExponent == 0 || yExponent == expAllOnes fmt ||
        zExponent == 0 || zExponent == expAllOnes fmt then
      none
    else
      let productScale := (xExponent - 1) + (yExponent - 1)
      let zProductScale := (zExponent - 1) + UInt64.ofNat (fmt.bias + fmt.fracWidth - 1)
      if productScale + UInt64.ofNat fmt.fracWidth != zProductScale then
        none
      else
        let xMantissa := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
        let yMantissa := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
        let zMantissa := normalMantissa fmt (fracHigh fmt zWords.hi) zWords.lo
        let product := FloatLib.Numerics.FixedWord.mul128 xMantissa yMantissa
        let sum :=
          FloatLib.Numerics.FixedWord.add256 product (alignFmaAddend fmt zMantissa)
        if sum.carry != 0 then
          none
        else
          roundNormalProductOption productSign xExponent yExponent sum.value
            (UInt64.ofNat sum.value.log2)

/--
Evaluate finite two-word fused multiply-add.

The aligned fixed-limb kernel is attempted first. Every remaining finite case uses the generic
one-rounding exact kernel; exceptional inputs are reported as `none` to the dispatcher.
Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def fmaFiniteOption {fmt : FloatFormat} (x y z : Model fmt) : Option (Model
  fmt) :=
  match fmaNormalSameSignAlignedOption x y z with
  | some result => some result
  | none => FiniteKernel.fmaRuntimeFlatOption x y z

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
