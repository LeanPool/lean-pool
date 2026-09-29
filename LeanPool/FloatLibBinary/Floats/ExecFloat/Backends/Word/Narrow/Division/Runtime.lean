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
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Native-word division for binary32

Finite division uses native-word significands and quotient arithmetic, with `Int` exponents and
natural-number coordinates for final packing. Finite division by zero is handled here;
`divFiniteImplOption` returns `none` for NaN or infinity operands so the caller can apply their
policy.
Correctness lives in `Division.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
open FloatLib.Numerics.FixedWord.RestoringQuotient

/--
Round the signed magnitude `(num / den) * 2^exponent` to binary32 with native quotient
arithmetic and an `Int` exponent.

Callers supply significands below `2^24`; the proof module establishes that every shift and
division stays within `UInt64`.
-/
@[inline] def roundRatScaledWord
    (sign : Bool) (num den : UInt64) (exponent : Int) : UInt32 :=
  if den == 0 then
    0x7fc00000
  else if num == 0 then
    if sign then 0x80000000 else 0
  else
    let rationalExponent := floorLog2RatWord num den
    let totalExponent := rationalExponent + exponent
    if totalExponent > 127 then
      if sign then 0xff800000 else 0x7f800000
    else if totalExponent < -150 then
      if sign then 0x80000000 else 0
    else if totalExponent < -126 then
      let scaled :=
        match exponent + 149 with
        | .ofNat shift => (num <<< UInt64.ofNat shift, den)
        | .negSucc shift => (num, den <<< UInt64.ofNat (shift + 1))
      let fraction := FloatLib.Numerics.FixedWord.roundQuotientEven scaled.1 scaled.2
      if fraction == 0 then
        if sign then 0x80000000 else 0
      else if fraction ≥ 0x800000 then
        mkBits sign 1 0
      else
        mkBits sign 0 fraction.toNat
    else
      let shift := Int.toNat (23 - rationalExponent)
      let scaledNumerator := num <<< UInt64.ofNat shift
      let roundedMantissa := FloatLib.Numerics.FixedWord.roundQuotientEven scaledNumerator den
      let carry := roundedMantissa == 0x1000000
      let normalizedExponent := if carry then totalExponent + 1 else totalExponent
      let normalizedMantissa := if carry then 0x800000 else roundedMantissa
      if normalizedExponent > 127 then
        if sign then 0xff800000 else 0x7f800000
      else
        let encodedExponent := Int.toNat (normalizedExponent + 127)
        let fraction := normalizedMantissa.toNat - 0x800000
        mkBits sign encodedExponent fraction

/--
Fast finite binary32 division using one-word significands and the native-word rounder.

`none` means at least one operand is a NaN or infinity; the caller applies the generic policy.
-/
@[inline] def divFiniteImplOption (x y : Value) : Option Value :=
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
    if yMantissa == 0 then
      if xMantissa == 0 then
        some (ofUInt32 0x7fc00000)
      else
        some (ofUInt32 (if sign then 0xff800000 else 0x7f800000))
    else if xMantissa == 0 then
      some (ofUInt32 (if sign then 0x80000000 else 0))
    else
      let exponent := Int.ofNat xScale.toNat - Int.ofNat yScale.toNat
      some (ofUInt32 (roundRatScaledWord sign xMantissa yMantissa exponent))

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
