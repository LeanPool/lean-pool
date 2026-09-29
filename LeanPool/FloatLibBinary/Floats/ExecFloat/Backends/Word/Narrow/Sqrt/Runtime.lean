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
public import LeanPool.FloatLibBinary.Kernels.FixedWord.IntegerSquareRoot.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Runtime

/-!
# Native binary32 square root

Positive finite inputs are scaled to a 47- or 48-bit radicand, so the exact floor square root and
nearest-even decision fit entirely in `UInt64`. The complete operation retains IEEE NaN,
infinity, negative-input, and signed-zero behavior. Correctness lives in `Sqrt.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/--
Round the square root of a positive finite binary32 mantissa and scale.

For `0 < mantissa < 2^24` and `scale ≤ 253`, the input value is
`mantissa * 2^(scale - 149)`, with subtraction in `Int`. The selected shift places its square root
in the 24-bit binary32 significand range before the final nearest-even decision.
-/
@[inline] def sqrtPositiveFiniteCore (mantissa scale : UInt64) : UInt32 :=
  let leading := mantissa.log2
  let position := leading + scale
  let shift := if position % 2 == 0 then 47 - leading else 46 - leading
  let scaledMantissa := mantissa <<< shift
  let root := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt scaledMantissa
  let remainder := scaledMantissa - root * root
  let roundedRoot := if remainder ≤ root then root else root + 1
  let carry := roundedRoot == 0x1000000
  let encodedExponent := (position + 105) / 2 + if carry then 1 else 0
  let roundedMantissa := if carry then 0x800000 else roundedRoot
  mkBits false encodedExponent.toNat (roundedMantissa - 0x800000).toNat

/-- Decode binary32 fields and run the bounded positive-finite square-root kernel. -/
@[inline] def sqrtPositiveFinite (exponent fraction : UInt32) : UInt32 :=
  sqrtPositiveFiniteCore
    (finiteMantissa exponent fraction)
    (finiteScale exponent)

/-- Native binary32 square root, including IEEE exceptional-value behavior. -/
@[inline] def sqrt (x : Value) : Value :=
  let bits := toUInt32 x
  let exponent := expField bits
  let fraction := fracField bits
  if exponent == 0xff then
    if fraction == 0 then
      if signBit bits then ofUInt32 0x7fc00000 else x
    else
      ofUInt32 (bits ||| 0x00400000)
  else if exponent == 0 && fraction == 0 then
    x
  else if signBit bits then
    ofUInt32 0x7fc00000
  else
    ofUInt32 (sqrtPositiveFinite exponent fraction)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
