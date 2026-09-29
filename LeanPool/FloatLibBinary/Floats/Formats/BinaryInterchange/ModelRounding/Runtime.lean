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

public import Init.Data.Float.Model.Unpacked.Operations.Div
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Executable normalization for binary interchange formats

These computations normalize exact integer mantissas with round-to-nearest, ties-to-even.
Mantissa widths and target exponents are parameters; no named binary format is selected.

Proofs relating these computations to Lean's logical floating-point model are kept in
`ModelRounding.Proof`, so executable clients can import this module without the large semantic
proof layer.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Section 4.3.1.
- Lean 4, `Init.Data.Float.Model.Unpacked.Round`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Numerics

/-- Round an exact integer mantissa after expressing it at `targetExponent`. -/
def roundMantissaAtExponentEven
    (mantissa : Nat) (exponent targetExponent : Int) : Nat :=
  if exponent ≤ targetExponent then
    roundShiftRightEven mantissa (targetExponent - exponent).toNat
  else
    mantissa <<< (exponent - targetExponent).toNat

/-- Round a positive integer mantissa to the precision specified by `leadingBit + 1`;
a rounding carry can produce one extra bit. -/
def roundMantissaToLeadingBitEven (mantissa leadingBit : Nat) : Nat :=
  if leadingBit ≤ mantissa.log2 then
    roundShiftRightEven mantissa (mantissa.log2 - leadingBit)
  else
    mantissa <<< (leadingBit - mantissa.log2)

/-- Complete model rounding after the first rounded mantissa and exponent are known. -/
def finishRoundedMantissa
    (spec : Float.Model.Format) (sign : Sign) (rounded : Nat × Int) :
    Float.Model.UnpackedFloat :=
  let final := Float.Model.UnpackedFloat.shiftToTargetExponent
    spec rounded.1 rounded.2 .exact
  if h : final.1.mantissa = 0 then
    .zero sign
  else
    .finite sign final.1.mantissa final.2 (Nat.pos_of_ne_zero h)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
