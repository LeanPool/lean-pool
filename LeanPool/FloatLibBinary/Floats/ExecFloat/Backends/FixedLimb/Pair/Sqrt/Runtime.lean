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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.RestoringSqrt.Runtime
import LeanPool.FloatLibBinary.Kernels.FixedWord.RestoringSqrt.Compiler

/-!
# Two-word square-root runtime

The proved restoring loop computes the exact floor square root and remainder for a positive normal
input of any eligible two-word layout whose fraction has at most 124 bits and whose bias exceeds
the fraction width. Correctness proofs live in `Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord.RestoringSquareRoot

/-- Shift a normal significand by `shift` bits into four words. -/
@[inline] def alignSqrtRadicand
    (mantissa : FloatLib.Numerics.FixedWord.UInt128)
    (shift : Nat) : FloatLib.Numerics.FixedWord.UInt256 :=
  FloatLib.Numerics.FixedWord.UInt256.ofUInt128ShiftedLeft mantissa shift

/--
Try the fixed-word square root for one positive normal value.

The radicand is the significand shifted by `fracWidth` or `fracWidth + 1` bits, chosen so that the
result exponent is integral, and the root is extracted with `fracWidth + 1` base-four digits. The
kernel declines formats whose fraction exceeds 124 bits, outside the proved bound on the
two-word remainder state, and formats whose bias is at most the fraction width, outside the
hypotheses of the exponent lemmas in `SqrtArithmetic`. The dispatcher handles these cases.
Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def sqrtNormalOption {fmt : FloatFormat} (x : Model fmt) : Option (Model fmt) :=
  if x.bits.msb then
    none
  else if fmt.bias < fmt.fracWidth + 1 || 124 < fmt.fracWidth then
    none
  else
    let words := toWords x
    let exponent := expField fmt words.hi
    if exponent == 0 || exponent == expAllOnes fmt then
      none
    else
      let mantissa := normalMantissa fmt (fracHigh fmt words.hi) words.lo
      let shift := if (exponent &&& 1) == 1 then fmt.fracWidth else fmt.fracWidth + 1
      let radicand := alignSqrtRadicand mantissa shift
      let state := rootAndRemainder radicand (fmt.fracWidth + 1)
      let rounded := roundRoot state
      let carry := isCarry fmt rounded
      let resultExponent :=
        (exponent + UInt64.ofNat fmt.bias) / 2 + if carry then 1 else 0
      some <| packNormal fmt false resultExponent (normalizeCarry fmt carry rounded)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
