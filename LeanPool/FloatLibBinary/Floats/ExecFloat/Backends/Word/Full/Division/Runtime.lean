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

import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Compiler

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Core.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Quotient.Runtime

/-!
# Native binary64 division runtime

The normal-result binary64 path performs restoring division on `UInt64`. Inputs outside the
normal-result kernel fall back to the exact generic finite implementation. Correctness proofs are
isolated in `Division.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord.RestoringQuotient
open FloatLib.Numerics.FixedWord

/--
Try the common finite division path whose rounded result is normal.

Returning `none` delegates zeros, subnormals, overflow boundaries, and exceptional encodings to
the generic exact-rational implementation.
-/
@[inline] def divNormalOption (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0x7ff || yExponent == 0x7ff then
    none
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    if xMantissa == 0 || yMantissa == 0 then
      none
    else
      let exponent :=
        Int.ofNat (finiteScale xExponent).toNat -
          Int.ofNat (finiteScale yExponent).toNat
      let rationalExponent :=
        floorLog2RatWord xMantissa yMantissa
      let totalExponent := rationalExponent + exponent
      if totalExponent < -1022 || 1023 < totalExponent then
        none
      else
        let shift := Int.toNat (52 - rationalExponent)
        let roundedMantissa :=
          roundScaledQuotient xMantissa yMantissa shift
        let carry := roundedMantissa == 0x0020000000000000
        let normalizedExponent :=
          if carry then totalExponent + 1 else totalExponent
        if 1023 < normalizedExponent then
          none
        else
          let normalizedMantissa :=
            if carry then 0x0010000000000000 else roundedMantissa
          let encodedExponent :=
            UInt64.ofNat (Int.toNat (normalizedExponent + 1023))
          let fraction := normalizedMantissa - 0x0010000000000000
          some <| ofUInt64 <|
            packFieldsWord
              (Bool.xor (signBit xBits) (signBit yBits))
              encodedExponent fraction

/--
Use the native normal-result divider when it accepts the operands, otherwise retain the exact
generic finite binary64 implementation.
-/
@[inline] def divFiniteFastImplOption (x y : Value) : Option Value :=
  match divNormalOption x y with
  | some quotient => some quotient
  | none => NativeBinary64.divFiniteImplOption x y

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
