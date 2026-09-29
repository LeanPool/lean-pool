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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Finite.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Rounding.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.SignedMagnitude.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rounding

/-!
# Native-word addition for generic binary32

The nonzero finite path extracts fields and packs the result with `UInt32` and `UInt64`. Non-finite
IEEE policy remains outside this module; the entry points return `none` when
either operand is a NaN or infinity. Correctness lives in `Addition.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/--
Finite binary32 addition through exact dyadic coordinates.

`none` means at least one operand is a NaN or infinity; the caller applies the generic IEEE
special-value policy in that case.
-/
@[inline] def addFiniteOption (x y : Value) : Option Value :=
  match toDyadicOption (toUInt32 x), toDyadicOption (toUInt32 y) with
  | some dx, some dy =>
      some (ofUInt32 (roundDyadic (Model.addDyadic dx dy)))
  | _, _ => none

/--
Machine-word implementation of finite binary32 addition.

When exponent alignment fits in 39 bits, both exact significands and their sum fit in one
`UInt64`. At larger gaps the smaller finite significand is strictly below half an ulp, so
nearest-even rounding returns the dominant operand directly.
-/
@[inline] def addFiniteImplOption (x y : Value) : Option Value :=
  let xBits := toUInt32 x
  let yBits := toUInt32 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0xff || yExponent == 0xff then
    none
  else
    let xSign := signBit xBits
    let ySign := signBit yBits
    let xFraction := fracField xBits
    let yFraction := fracField yBits
    let xMantissa := finiteMantissa xExponent xFraction
    let yMantissa := finiteMantissa yExponent yFraction
    let xScale := finiteScale xExponent
    let yScale := finiteScale yExponent
    if xMantissa == 0 || yMantissa == 0 then
      addFiniteOption x y
    else if xScale ≤ yScale then
      let shift := yScale - xScale
      if shift ≤ 39 then
        let sum := FloatLib.Numerics.FixedWord.addSignedMagnitudes
          xSign ySign xMantissa (yMantissa <<< shift)
        some (ofUInt32 (roundProduct sum.1 sum.2 (xScale + 149)))
      else
        some y
    else
      let shift := xScale - yScale
      if shift ≤ 39 then
        let sum := FloatLib.Numerics.FixedWord.addSignedMagnitudes
          xSign ySign (xMantissa <<< shift) yMantissa
        some (ofUInt32 (roundProduct sum.1 sum.2 (yScale + 149)))
      else
        some x

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
