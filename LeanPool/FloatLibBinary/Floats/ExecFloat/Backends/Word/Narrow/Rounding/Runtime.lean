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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime

/-!
# Native binary32 product rounding

The machine-word product rounder serves multiplication, aligned addition, and fused
multiply-add. Its correctness theorem lives in `Rounding.Proof`, keeping execution-only imports
independent of the proof development.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/--
Round the signed magnitude `product * 2^(scale - 298)` to binary32, with sign `sign` and
subtraction in `Int`.

Correctness holds for every `UInt64` magnitude when `scale ≤ 506`; callers establish this bound.
In particular, finite multiplication supplies a product below `2^48`.
-/
@[inline] def roundProduct (sign : Bool) (product scale : UInt64) : UInt32 :=
  if product == 0 then
    if sign then 0x80000000 else 0
  else
    let leading := product.log2
    let position := leading + scale
    if position < 172 then
      let fraction :=
        if scale < 149 then
          FloatLib.Numerics.FixedWord.roundShiftRightEven product (149 - scale).toNat
        else
          product <<< (scale - 149)
      if fraction == 0 then
        if sign then 0x80000000 else 0
      else if fraction == 0x800000 then
        mkBits sign 1 0
      else
        mkBits sign 0 fraction.toNat
    else
      let roundedMantissa :=
        if leading < 23 then
          product <<< (23 - leading)
        else
          FloatLib.Numerics.FixedWord.roundShiftRightEven product (leading - 23).toNat
      let carry := roundedMantissa == 0x1000000
      let normalizedPosition := if carry then position + 1 else position
      if normalizedPosition > 425 then
        if sign then 0xff800000 else 0x7f800000
      else
        let normalizedMantissa := if carry then 0x800000 else roundedMantissa
        let encodedExponent := normalizedPosition - 171
        let fraction := normalizedMantissa.toNat - 0x800000
        mkBits sign encodedExponent.toNat fraction

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
