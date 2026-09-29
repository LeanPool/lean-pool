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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Catalog

/-!
# Native-storage binary64 runtime

Binary64 is represented publicly by the same generic `Model` as every binary-interchange format,
but its payload fits exactly in a `UInt64`. These adapters expose that native storage to finite
kernels without introducing a second user-visible value type.

Field extraction, packing, and exact intermediate arithmetic are kept here in the runtime layer.
Exceptional IEEE behavior remains in the shared dispatcher, and `Core.Proof` shows that the
native-word routines agree with the generic model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

/-- The generic binary64 carrier. -/
abbrev Value := Model FloatFormat.binary64

/-- View generic binary64 storage as a native word. -/
@[inline] def toUInt64 (x : Value) : UInt64 :=
  UInt64.ofBitVec x.bits

/-- Rewrap a native binary64 word in the generic carrier. -/
@[inline] def ofUInt64 (bits : UInt64) : Value :=
  Model.ofBits bits.toBitVec

/-- Toggle the binary64 sign bit without generic `BitVec` arithmetic. -/
@[inline] def negate (x : Value) : Value :=
  ofUInt64 (toUInt64 x ^^^ 0x8000000000000000)

/-- Extract the binary64 sign from a native word. -/
@[inline] def signBit (bits : UInt64) : Bool :=
  (bits &&& 0x8000000000000000) != 0

/-- Extract the binary64 biased exponent from a native word. -/
@[inline] def expField (bits : UInt64) : UInt64 :=
  (bits >>> 52) &&& 0x7ff

/-- Extract the binary64 fraction from a native word. -/
@[inline] def fracField (bits : UInt64) : UInt64 :=
  bits &&& 0x000fffffffffffff

/-- Pack binary64 fields directly into their native storage word. -/
@[inline] def packFieldsWord
    (sign : Bool) (exponent fraction : UInt64) : UInt64 :=
  (if sign then (1 : UInt64) <<< 63 else 0) |||
    ((exponent &&& 0x7ff) <<< 52) |||
    (fraction &&& 0x000fffffffffffff)

/-- Decode the finite binary64 significand, including the implicit bit for normal values. -/
@[inline] def finiteMantissa (exponent fraction : UInt64) : UInt64 :=
  if exponent == 0 then fraction else fraction ||| 0x0010000000000000

/-- Round a normalized two-limb product once its leading-bit position is known. -/
@[inline] def roundNormalProductOption (sign : Bool) (xExponent yExponent : UInt64)
    (product : FloatLib.Numerics.FixedWord.UInt128) (leading : UInt64) : Option Value :=
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  if position < 1126 then
    none
  else
    let rounded :=
      product.roundShiftRightEven (leading - 52).toNat
    let carry := rounded == 0x0020000000000000
    let normalizedPosition := if carry then position + 1 else position
    if 3171 < normalizedPosition then
      none
    else
      let normalizedMantissa :=
        if carry then (0x0010000000000000 : UInt64) else rounded
      let exponent := normalizedPosition.toNat - 1125
      let fraction := normalizedMantissa.toNat - 0x0010000000000000
      some <| ofFields FloatFormat.binary64 sign exponent fraction

/--
Form the exact product of decoded normal binary64 significands in native limbs, then round it.

The path declines when the leading exponent is below the normal range before rounding, or when
rounding would overflow. Those cases use the generic exact rounder.
-/
@[inline] def roundNormalLimbOption (sign : Bool) (xExponent yExponent : UInt64)
    (xMantissa yMantissa : UInt64) : Option Value :=
  let product := FloatLib.Numerics.FixedWord.mul64 xMantissa yMantissa
  let leading : UInt64 :=
    if product.hi < ((1 : UInt64) <<< 41) then 104 else 105
  roundNormalProductOption sign xExponent yExponent product leading

/-- Decode two binary64 values and try the fixed-limb normal product pipeline. -/
@[inline] def mulNormalLimbOption (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0 || xExponent == 0x7ff ||
      yExponent == 0 || yExponent == 0x7ff then
    none
  else
    roundNormalLimbOption
      (Bool.xor (signBit xBits) (signBit yBits))
      xExponent yExponent
      (fracField xBits ||| 0x0010000000000000)
      (fracField yBits ||| 0x0010000000000000)

/-- Decode binary64 fields with native storage into compact finite components. -/
@[inline] def decodeOption (x : Value) : Option FiniteKernel.Components :=
  let bits := toUInt64 x
  let exponent := expField bits
  if exponent == 0x7ff then
    none
  else
    let fraction := fracField bits
    some {
      sign := signBit bits
      exponent := exponent.toNat
      mantissa := (finiteMantissa exponent fraction).toNat }

/--
Native-storage finite addition through the compiled unsigned-scale component kernel.

The body names `FiniteKernel.addComponentsImpl`, the compiled twin of the exact-dyadic
`addComponents`. Their equality is proved in `Kernel.Proof`, which a runtime module cannot import,
so naming the compiled kernel here keeps the exact-dyadic body out of the binary64 hot path.
-/
@[inline] def addFiniteImplOption (x y : Value) : Option Value :=
  match decodeOption x, decodeOption y with
  | some dx, some dy =>
      some <| FiniteKernel.addComponentsImpl FloatFormat.binary64 dx dy
  | _, _ => none

/-- Finite binary64 multiplication with flat native field decoding. -/
@[inline] def mulFiniteImplOption (x y : Value) : Option Value :=
  let xBits := toUInt64 x
  let yBits := toUInt64 y
  let xExponent := expField xBits
  let yExponent := expField yBits
  if xExponent == 0x7ff || yExponent == 0x7ff then
    none
  else
    let xFraction := fracField xBits
    let yFraction := fracField yBits
    some <| FiniteProductRound.round FloatFormat.binary64
      (Bool.xor (signBit xBits) (signBit yBits))
      ((finiteMantissa xExponent xFraction).toNat *
        (finiteMantissa yExponent yFraction).toNat)
      ((FloatLib.Numerics.FixedWord.finiteScale xExponent).toNat +
        (FloatLib.Numerics.FixedWord.finiteScale yExponent).toNat)

/-- Native-storage finite division using the shared exact component kernel. -/
@[inline] def divFiniteImplOption (x y : Value) : Option Value :=
  match decodeOption x, decodeOption y with
  | some dx, some dy =>
      some <| FiniteKernel.divComponents FloatFormat.binary64 dx dy
  | _, _ => none

/--
Native-storage finite fused multiply-add through the compiled unsigned-scale component kernel.

As for `addFiniteImplOption`, the body names `FiniteKernel.fmaComponentsImpl` so that the compiled
binary64 path uses the unsigned-scale kernel instead of the exact-dyadic `fmaComponents` body.
-/
@[inline] def fmaFiniteImplOption (x y z : Value) : Option Value :=
  match decodeOption x, decodeOption y, decodeOption z with
  | some dx, some dy, some dz =>
      some <| FiniteKernel.fmaComponentsImpl FloatFormat.binary64 dx dy dz
  | _, _, _ => none

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
