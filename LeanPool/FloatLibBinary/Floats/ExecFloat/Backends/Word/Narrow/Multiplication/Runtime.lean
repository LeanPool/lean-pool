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

/-!
# Native-word finite multiplication for generic binary32

Finite binary32 significands occupy at most 24 bits, so their exact product fits in one `UInt64`.
Special-value policy remains outside this module; both entry points return `none` for a NaN or
infinity. Correctness lives in `Multiplication.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Finite multiplication through exact dyadic coordinates. -/
@[inline] def mulFiniteOption (x y : Value) : Option Value :=
  match toDyadicOption (toUInt32 x), toDyadicOption (toUInt32 y) with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dx.significand == 0 || dy.significand == 0 then
        some (ofUInt32 (if sign then 0x80000000 else 0))
      else
        some (ofUInt32 (roundDyadic {
          negative := sign
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }))
  | _, _ => none

/--
Machine-word implementation of finite binary32 multiplication.

Each operand magnitude is `mantissa * 2^(scale - 149)`, with subtraction interpreted in `Int`.
The runtime uses unsigned scales throughout normalization and rounding.
-/
@[inline] def mulFiniteImplOption (x y : Value) : Option Value :=
  let xBits := toUInt32 x
  let yBits := toUInt32 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0xff || yExponent == 0xff then
    none
  else
    let sign := Bool.xor (signBit xBits) (signBit yBits)
    let xFraction := fracField xBits
    let yFraction := fracField yBits
    let xMantissa := finiteMantissa xExponent xFraction
    let yMantissa := finiteMantissa yExponent yFraction
    let xScale := finiteScale xExponent
    let yScale := finiteScale yExponent
    some (ofUInt32 (roundProduct sign (xMantissa * yMantissa) (xScale + yScale)))

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
