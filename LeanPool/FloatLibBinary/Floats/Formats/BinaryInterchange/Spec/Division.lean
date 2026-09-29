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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Division specification

This exact-rational reference operation defines the proof target for every validated
`FloatFormat`.

Finite operands with a nonzero divisor are divided as an exact scaled rational and rounded to
nearest with ties to even.
Special operands and division by zero follow the descriptor's encoding policy. This module defines
the value-only reference operation; explicit rounding directions and status flags belong to the
separate directed and status APIs. Word and arbitrary-width division kernels refine this same
reference definition.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Spec

/-- Division result when at least one operand is non-finite. -/
@[inline] def divSpecial {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match chooseNaN2 x y with
  | some nan => nan
  | none =>
      if isInf x then
        if isInf y then invalidResult fmt
        else nativeOverflow fmt (signBit x != signBit y)
      else if isInf y then
        zero fmt (signBit x != signBit y)
      else
        invalidResult fmt

/-- Exact rational division followed by nearest-even rounding in the destination descriptor. -/
@[inline] def div {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match toDyadicOption x, toDyadicOption y with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dy.significand == 0 then
        if dx.significand == 0 then invalidResult fmt
        else nativeOverflow fmt sign
      else if dx.significand == 0 then
        zero fmt sign
      else
        roundRatScaled fmt sign dx.significand dy.significand (dx.exponent - dy.exponent)
  | _, _ => divSpecial x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.Spec
