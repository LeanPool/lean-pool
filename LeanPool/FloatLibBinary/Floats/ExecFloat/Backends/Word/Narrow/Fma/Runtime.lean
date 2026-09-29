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
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Rounding.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.SignedMagnitude.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rounding

/-!
# Native-word fused multiply-add for generic binary32

The fast path combines a product of at most 48 bits with the addend in one `UInt64` when
alignment permits it. A same-sign addend dominating the product by more than 48 scale bits is
returned unchanged. Remaining gaps use exact dyadic alignment to preserve tie-breaking.
Special-value policy remains outside this module. Correctness lives in `Fma.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- Finite binary32 fused multiply-add through exact dyadic coordinates. -/
@[inline] def fmaFiniteOption (x y z : Value) : Option Value :=
  match toDyadicOption (toUInt32 x), toDyadicOption (toUInt32 y), toDyadicOption (toUInt32 z) with
  | some dx, some dy, some dz =>
      let product : Numerics.Dyadic := {
        negative := Bool.xor dx.negative dy.negative,
        significand := dx.significand * dy.significand,
        exponent := dx.exponent + dy.exponent }
      some (ofUInt32 (roundDyadic (Model.addDyadic product dz)))
  | _, _, _ => none

/--
General exact finite binary32 FMA path using components already decoded by the native kernel.

This retains arbitrary-gap alignment while avoiding a second decode and significand product.
-/
@[inline] def fmaExactFiniteOption
    (productSign zSign : Bool)
    (product productScale zMantissa zProductScale : UInt64) : Option Value :=
  some <| ofUInt32 <| roundDyadic <|
    Model.addDyadic
      { negative := productSign
        significand := product.toNat
        exponent := Int.ofNat productScale.toNat - 298 }
      { negative := zSign
        significand := zMantissa.toNat
        exponent := Int.ofNat zProductScale.toNat - 298 }

/--
Machine-word implementation of finite binary32 fused multiply-add.

The exact product occupies at most 48 bits. When exponent alignment also fits in one `UInt64`, the
product and addend are combined without constructing dyadics. An addend dominating a same-sign
product by more than 48 scale bits is returned unchanged. Other gaps retain the generic exact
path, including its tie-breaking behavior when a tiny addend perturbs a halfway product.
-/
@[inline] def fmaFiniteImplOption (x y z : Value) : Option Value :=
  let xBits := toUInt32 x
  let yBits := toUInt32 y
  let zBits := toUInt32 z
  let xExponent := expField xBits
  let yExponent := expField yBits
  let zExponent := expField zBits
  if xExponent == 0xff || yExponent == 0xff || zExponent == 0xff then
    fmaFiniteOption x y z
  else
    let xMantissa := finiteMantissa xExponent (fracField xBits)
    let yMantissa := finiteMantissa yExponent (fracField yBits)
    let zMantissa := finiteMantissa zExponent (fracField zBits)
    let xScale := finiteScale xExponent
    let yScale := finiteScale yExponent
    let zScale := finiteScale zExponent
    let productSign := Bool.xor (signBit xBits) (signBit yBits)
    let zSign := signBit zBits
    let product := xMantissa * yMantissa
    let productScale := xScale + yScale
    let zProductScale := zScale + 149
    if product == 0 || zMantissa == 0 then
      fmaFiniteOption x y z
    else if productScale ≤ zProductScale then
      let shift := zProductScale - productScale
      if shift ≤ 39 then
        let sum := FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign product (zMantissa <<< shift)
        some (ofUInt32 (roundProduct sum.1 sum.2 productScale))
      else if 48 < shift && productSign == zSign then
        some z
      else
        fmaExactFiniteOption
          productSign zSign product productScale zMantissa zProductScale
    else
      let shift := productScale - zProductScale
      if shift ≤ 15 then
        let sum := FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign (product <<< shift) zMantissa
        some (ofUInt32 (roundProduct sum.1 sum.2 zProductScale))
      else
        fmaExactFiniteOption
          productSign zSign product productScale zMantissa zProductScale

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
