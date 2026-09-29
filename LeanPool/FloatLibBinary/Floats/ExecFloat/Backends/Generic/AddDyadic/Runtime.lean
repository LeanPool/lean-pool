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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Basic

/-!
# Executable signed-magnitude dyadic addition

Exact dyadic addition uses separate signs and natural-number magnitudes. Correctness proofs and
the compiler substitution live in `AddDyadic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Add two nonzero signed magnitudes at a shared dyadic exponent. -/
@[inline] def addDyadicMagnitudes
    (leftSign rightSign : Bool) (left right : Nat) (exponent : Int) : Numerics.Dyadic :=
  if leftSign == rightSign then
    { negative := leftSign, significand := left + right, exponent := exponent }
  else if left == right then
    { negative := leftSign && rightSign, significand := 0, exponent := 0 }
  else if left < right then
    { negative := rightSign, significand := right - left, exponent := exponent }
  else
    { negative := leftSign, significand := left - right, exponent := exponent }

/--
Exact dyadic addition using separate signs and natural-number magnitudes.

Zero operands are handled before alignment. For two nonzero operands, the significand with the
larger exponent is shifted to the smaller exponent before the magnitudes are combined. No
rounding occurs here.
-/
@[inline] def addDyadicImpl (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  if a.significand == 0 then
    if b.significand == 0 then
      { negative := a.negative && b.negative, significand := 0, exponent := 0 }
    else
      b
  else if b.significand == 0 then
    a
  else if a.exponent ≤ b.exponent then
    let shift := Int.toNat (b.exponent - a.exponent)
    addDyadicMagnitudes a.negative b.negative a.significand
      (Nat.shiftLeft b.significand shift) a.exponent
  else
    let shift := Int.toNat (a.exponent - b.exponent)
    addDyadicMagnitudes a.negative b.negative
      (Nat.shiftLeft a.significand shift) b.significand b.exponent

end FloatLib.Floats.Formats.BinaryInterchange.Model
