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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Subtraction.Runtime

/-!
# Native binary64 addition and subtraction runtime

The executable binary64 dispatchers combine equal-exponent addition with signed Sterbenz
subtraction. Their refinement proofs are isolated in `Addition.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

/--
Try native same-sign addition of normal binary64 operands with the same exponent.

The sum of two 53-bit significands is rounded once to nearest-even and packed directly.
-/
@[inline] def addNormalSameExponentOption (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  let xSign := signBit xBits
  let ySign := signBit yBits
  if xSign != ySign || xExponent == 0 || xExponent == 0x7ff ||
      yExponent != xExponent then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let rounded :=
      FloatLib.Numerics.FixedWord.roundShiftRightEven (xMantissa + yMantissa) 1
    let resultExponent := xExponent + 1
    if 0x7ff ≤ resultExponent then
      none
    else
      some <| ofUInt64 <|
        packFieldsWord xSign resultExponent
          (rounded - 0x0010000000000000)

/-- Try native equal-exponent addition before the exact finite binary64 implementation. -/
@[inline] def addFiniteFastImplOption (x y : Value) : Option Value :=
  match addNormalSameExponentOption x y with
  | some sum => some sum
  | none => addFiniteImplOption x y

/--
Try signed Sterbenz subtraction first, then reuse native same-exponent addition for opposite-sign
subtraction. Every declined case retains the exact finite component kernel.
-/
@[inline] def subFiniteFastImplOption (x y : Value) : Option Value :=
  match subSignedSterbenzOption x y with
  | some difference => some difference
  | none => addFiniteFastImplOption x (negate y)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
