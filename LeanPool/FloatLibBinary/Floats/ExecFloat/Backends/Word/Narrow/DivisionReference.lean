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

/-!
# Exact-rational reference division for native binary32 words

The exact-rational reference divider specifies the result against which the direct binary32 word
divider is refined. It decodes finite binary32 operands, handles finite division by zero
according to IEEE binary32, and delegates nonzero quotients to the exact rational rounder.

The optimized one-word divider and its proof live in `Narrow.Division.Runtime` and
`Narrow.Division.Proof`. Keeping the reference
operation independent prevents division-only clients from depending on the much larger
addition/FMA implementation core.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Finite binary32 division through the generic exact-rational rounder. -/
@[inline] def divFiniteOption (x y : Value) : Option Value :=
  match toDyadicOption (toUInt32 x), toDyadicOption (toUInt32 y) with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dy.significand == 0 then
        if dx.significand == 0 then
          some (ofUInt32 0x7fc00000)
        else
          some (ofUInt32 (if sign then 0xff800000 else 0x7f800000))
      else if dx.significand == 0 then
        some (ofUInt32 (if sign then 0x80000000 else 0))
      else
        some <|
          ofUInt32 <|
            roundRatScaled sign dx.significand dy.significand
              (dx.exponent - dy.exponent)
  | _, _ => none

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
