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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic

/-!
# Executable normalization for directed dyadic rounding

These helpers scale a positive mantissa to a requested leading-bit position. Downward
normalization discards low bits; upward normalization rounds them toward positive infinity and
may carry into the next bit.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Floor a positive mantissa while moving its leading bit to `leadingBit`. -/
def roundMantissaToLeadingBitDown (mantissa leadingBit : Nat) : Nat :=
  if leadingBit ≤ mantissa.log2 then
    Nat.shiftRight mantissa (mantissa.log2 - leadingBit)
  else
    Nat.shiftLeft mantissa (leadingBit - mantissa.log2)

/-- Scale a positive mantissa to `leadingBit` and round up, possibly carrying into the next bit. -/
def roundMantissaToLeadingBitUp (mantissa leadingBit : Nat) : Nat :=
  if leadingBit ≤ mantissa.log2 then
    shiftRightCeilPow2 mantissa (mantissa.log2 - leadingBit)
  else
    Nat.shiftLeft mantissa (leadingBit - mantissa.log2)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
