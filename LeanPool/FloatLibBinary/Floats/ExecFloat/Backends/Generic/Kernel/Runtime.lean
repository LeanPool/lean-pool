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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ScaleAdd.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Runtime

/-!
# Executable width-generic finite arithmetic

Arbitrary-precision kernels decode finite fields into a compact unsigned-scale representation.
Compiled arithmetic uses their allocation-reduced entry points for addition, multiplication,
division, and fused multiply-add. Refinement theorems live in `Kernel.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel

/--
Decoded finite fields before conversion to a signed dyadic exponent.

For a nonzero value, the magnitude is
`mantissa * 2^(scale exponent - finiteScaleOffset fmt)`, with the subtraction interpreted in `Int`.
The separate sign field determines its sign.
-/
structure Components where
  /-- Sign bit of the encoded value. -/
  sign : Bool
  /-- Biased exponent field; zero also identifies zeros and subnormals. -/
  exponent : Nat
  /-- Integer significand, including the implicit bit for a normal value. -/
  mantissa : Nat
  deriving Repr, DecidableEq

/-- Nonnegative scale associated with a finite exponent field. -/
@[inline] def scale (exponent : Nat) : Nat :=
  if exponent == 0 then 0 else exponent - 1

/-- Common nonnegative offset used by the compact finite-field scale. -/
@[inline] def finiteScaleOffset (fmt : FloatFormat) : Nat :=
  fmt.exponentBias + fmt.fracWidth - 1

/-- Signed dyadic exponent associated with a finite exponent field, including subnormals. -/
@[inline] def dyadicExponent (fmt : FloatFormat) (encoded : Nat) : Int :=
  if encoded == 0 then
    fmt.minSubnormalExponent
  else
    Int.ofNat encoded - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth

/--
Decode the integer significand from finite exponent and fraction fields.

Subnormal values use the stored fraction directly. Normal values restore the implicit leading bit.
The formula is width-generic and shared by every natural-number finite decoder.
-/
@[inline] def decodeMantissa (fmt : FloatFormat) (exponent fraction : Nat) : Nat :=
  if exponent == 0 then fraction else pow2 fmt.fracWidth + fraction

/-- Convert compact finite components to the exact dyadic representation used by proofs. -/
@[inline] def Components.toDyadic (fmt : FloatFormat) (value : Components) : Numerics.Dyadic :=
  if value.mantissa == 0 then
    { negative := value.sign, significand := 0, exponent := 0 }
  else
    { negative := value.sign
      significand := value.mantissa
      exponent := dyadicExponent fmt value.exponent }

/--
Decode the sign, exponent, and significand of a finite value.

`none` means the complete format descriptor classifies the input as non-finite. No
precision-specific constant occurs here.
-/
@[inline] def decodeOption {fmt : FloatFormat} (x : Model fmt) : Option Components :=
  if !isFinite x then
    none
  else
    let encodedExponent := expField x
    let fraction := fracField x
    let mantissa := decodeMantissa fmt encodedExponent fraction
    some { sign := signBit x, exponent := encodedExponent, mantissa }

/--
Run `k` on scalar fields when `x` is finite.

The IEEE branch converts the storage word to `Nat` once and does not allocate an intermediate
`Components` value. Other encodings retain the descriptor-aware decoder.
-/
@[inline] def withFiniteOption {fmt : FloatFormat} {α : Type}
    (x : Model fmt) (k : Bool → Nat → Nat → Option α) : Option α :=
  if fmt.isIEEE then
    let bits := x.toNatBits
    let exponent :=
      (bits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt
    if exponent == FloatFormat.expAllOnesNat fmt then
      none
    else
      let fraction := bits &&& FloatFormat.fracMaskNat fmt
      let mantissa := decodeMantissa fmt exponent fraction
      k (bits.testBit (fmt.expWidth + fmt.fracWidth)) exponent mantissa
  else
    match decodeOption x with
    | none => none
    | some value => k value.sign value.exponent value.mantissa

/--
Compiled finite addition aligns unsigned field scales before entering the rounder.

For non-IEEE descriptors it evaluates the same exact-dyadic definition used in the logic.
-/
@[inline] def addComponentsImpl
    (fmt : FloatFormat) (x y : Components) : Model fmt :=
  if fmt.isIEEE then
    FiniteScaleAdd.roundSum fmt (finiteScaleOffset fmt)
      x.sign y.sign x.mantissa (scale x.exponent)
      y.mantissa (scale y.exponent)
  else
    roundDyadicImpl fmt <| addDyadic (x.toDyadic fmt) (y.toDyadic fmt)

/--
Add two already-decoded finite values and round once to `fmt`.

The exact dyadic sum is rounded by the descriptor-generic integer implementation. Importing
`Kernel.Proof` also enables the verified compiler substitution to `addComponentsImpl`, which
uses unsigned scale alignment on IEEE descriptors.
-/
def addComponents
    (fmt : FloatFormat) (x y : Components) : Model fmt :=
  roundDyadicImpl fmt <| addDyadic (x.toDyadic fmt) (y.toDyadic fmt)

/--
Finite addition through the compact decoder.

The component operation is kept separate so fixed-width storage backends can reuse the same exact
dyadic addition and rounding policy after a cheaper field decode.
-/
@[inline] def addOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  match decodeOption x, decodeOption y with
  | some dx, some dy => some <| addComponents fmt dx dy
  | _, _ => none

/--
Finite multiplication using compact field scales.

The exact significand product remains a `Nat`, preserving arbitrary precision. Only the two
operand decodes and exponent algebra are fused; final rounding still uses the generic rounder.
-/
@[inline] def mulOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  match decodeOption x, decodeOption y with
  | some dx, some dy =>
      let sign := Bool.xor dx.sign dy.sign
      if dx.mantissa == 0 || dy.mantissa == 0 then
        some (zero fmt sign)
      else
        let product := dx.mantissa * dy.mantissa
        let productScale := scale dx.exponent + scale dy.exponent
        if fmt.isIEEE then
          some <| FiniteProductRound.round fmt sign product productScale
        else
          some <| roundDyadicImpl fmt {
            negative := sign
            significand := product
            exponent :=
              Int.ofNat productScale -
                Int.ofNat (2 * finiteScaleOffset fmt) }
  | _, _ => none

/--
Finite division using compact field scales.

The format-dependent exponent offset cancels between numerator and denominator. The quotient still
uses the exact arbitrary-precision rational rounder; only decoding and exponent construction are
fused.
-/
@[inline] def divComponents
    (fmt : FloatFormat) (x y : Components) : Model fmt :=
  let sign := Bool.xor x.sign y.sign
  if y.mantissa == 0 then
    if x.mantissa == 0 then
      invalidResult fmt
    else
      nativeOverflow fmt sign
  else if x.mantissa == 0 then
    zero fmt sign
  else
    roundRatScaled fmt sign x.mantissa y.mantissa
      (Int.ofNat (scale x.exponent) - Int.ofNat (scale y.exponent))

/-- Decode finite operands once, then apply `divComponents`. -/
@[inline] def divOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  match decodeOption x, decodeOption y with
  | some dx, some dy => some <| divComponents fmt dx dy
  | _, _ => none

/--
Exact product used by the finite fused-multiply-add kernel.

The exponent is expressed with nonnegative field scales. When either significand is zero this
exponent is observationally irrelevant: `addDyadic` identifies a zero from its mantissa and applies
the same signed-zero rule as the public dyadic path.
-/
@[inline] def productDyadic (fmt : FloatFormat) (x y : Components) : Numerics.Dyadic :=
  { negative := Bool.xor x.sign y.sign
    significand := x.mantissa * y.mantissa
    exponent :=
      Int.ofNat (scale x.exponent + scale y.exponent) -
        Int.ofNat (2 * finiteScaleOffset fmt) }

/--
Compiled finite FMA adds the exact product and addend in one unsigned scale coordinate.

The addend scale receives one format offset so both operands use the product rounder's
two-offset coordinate. No intermediate dyadic exponent is allocated on the IEEE fast path.
-/
@[inline] def fmaComponentsImpl
    (fmt : FloatFormat) (x y z : Components) : Model fmt :=
  if fmt.isIEEE then
    FiniteScaleAdd.roundSum fmt 0
      (Bool.xor x.sign y.sign) z.sign
      (x.mantissa * y.mantissa) (scale x.exponent + scale y.exponent)
      z.mantissa (scale z.exponent + finiteScaleOffset fmt)
  else
    roundDyadicImpl fmt <| addDyadic (productDyadic fmt x y) (z.toDyadic fmt)

/--
Exact finite fused multiply-add from three already-decoded values.

The exact dyadic result is rounded once by the descriptor-generic integer implementation.
Importing `Kernel.Proof` also enables the verified compiler substitution to `fmaComponentsImpl`,
which uses unsigned scale alignment on IEEE descriptors.
-/
def fmaComponents
    (fmt : FloatFormat) (x y z : Components) : Model fmt :=
  roundDyadicImpl fmt <| addDyadic (productDyadic fmt x y) (z.toDyadic fmt)

/--
Finite fused multiply-add using compact field scales for the exact product.

All three inputs are decoded once. The product and addend remain exact dyadics and the result is
rounded only once, so this is still a true fused operation at every supported precision.
-/
@[inline] def fmaOption {fmt : FloatFormat}
    (x y z : Model fmt) : Option (Model fmt) :=
  match decodeOption x, decodeOption y, decodeOption z with
  | some dx, some dy, some dz => some <| fmaComponents fmt dx dy dz
  | _, _, _ => none

/-! ## Scalar-field compiled entry points -/

/-- Add finite scalar fields without materializing decoded component records on IEEE formats. -/
@[inline] def addFields
    (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : Nat)
    (ySign : Bool) (yExponent yMantissa : Nat) : Model fmt :=
  if fmt.isIEEE then
    FiniteScaleAdd.roundSum fmt (finiteScaleOffset fmt)
      xSign ySign xMantissa (scale xExponent)
      yMantissa (scale yExponent)
  else
    addComponents fmt
      { sign := xSign, exponent := xExponent, mantissa := xMantissa }
      { sign := ySign, exponent := yExponent, mantissa := yMantissa }

/-- Compiled finite addition with scalar field decoding. -/
@[inline] def addRuntimeOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  withFiniteOption x fun xSign xExponent xMantissa =>
    withFiniteOption y fun ySign yExponent yMantissa =>
      some <| addFields fmt
        xSign xExponent xMantissa ySign yExponent yMantissa

/-- Multiply finite scalar fields using the compact product scale. -/
@[inline] def mulFields
    (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : Nat)
    (ySign : Bool) (yExponent yMantissa : Nat) : Model fmt :=
  let sign := Bool.xor xSign ySign
  if xMantissa == 0 || yMantissa == 0 then
    zero fmt sign
  else
    let product := xMantissa * yMantissa
    let productScale := scale xExponent + scale yExponent
    if fmt.isIEEE then
      FiniteProductRound.round fmt sign product productScale
    else
      roundDyadicImpl fmt {
        negative := sign
        significand := product
        exponent :=
          Int.ofNat productScale -
            Int.ofNat (2 * finiteScaleOffset fmt) }

/-- Compiled finite multiplication with scalar field decoding. -/
@[inline] def mulRuntimeOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  withFiniteOption x fun xSign xExponent xMantissa =>
    withFiniteOption y fun ySign yExponent yMantissa =>
      some <| mulFields fmt
        xSign xExponent xMantissa ySign yExponent yMantissa

/-- Divide finite scalar fields using the compact exponent difference. -/
@[inline] def divFields
    (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : Nat)
    (ySign : Bool) (yExponent yMantissa : Nat) : Model fmt :=
  let sign := Bool.xor xSign ySign
  if yMantissa == 0 then
    if xMantissa == 0 then
      invalidResult fmt
    else
      nativeOverflow fmt sign
  else if xMantissa == 0 then
    zero fmt sign
  else
    roundRatScaled fmt sign xMantissa yMantissa
      (Int.ofNat (scale xExponent) - Int.ofNat (scale yExponent))

/-- Compiled finite division with scalar field decoding. -/
@[inline] def divRuntimeOption {fmt : FloatFormat}
    (x y : Model fmt) : Option (Model fmt) :=
  withFiniteOption x fun xSign xExponent xMantissa =>
    withFiniteOption y fun ySign yExponent yMantissa =>
      some <| divFields fmt
        xSign xExponent xMantissa ySign yExponent yMantissa

/-- FMA on finite scalar fields without allocating decoded component records on IEEE formats. -/
@[inline] def fmaFields
    (fmt : FloatFormat)
    (xSign : Bool) (xExponent xMantissa : Nat)
    (ySign : Bool) (yExponent yMantissa : Nat)
    (zSign : Bool) (zExponent zMantissa : Nat) : Model fmt :=
  if fmt.isIEEE then
    FiniteScaleAdd.roundSum fmt 0
      (Bool.xor xSign ySign) zSign
      (xMantissa * yMantissa) (scale xExponent + scale yExponent)
      zMantissa (scale zExponent + finiteScaleOffset fmt)
  else
    fmaComponents fmt
      { sign := xSign, exponent := xExponent, mantissa := xMantissa }
      { sign := ySign, exponent := yExponent, mantissa := yMantissa }
      { sign := zSign, exponent := zExponent, mantissa := zMantissa }

/-- Compiled finite FMA with scalar field decoding. -/
@[inline] def fmaRuntimeOption {fmt : FloatFormat}
    (x y z : Model fmt) : Option (Model fmt) :=
  withFiniteOption x fun xSign xExponent xMantissa =>
    withFiniteOption y fun ySign yExponent yMantissa =>
      withFiniteOption z fun zSign zExponent zMantissa =>
        some <| fmaFields fmt
          xSign xExponent xMantissa ySign yExponent yMantissa
          zSign zExponent zMantissa

/--
Straight-line IEEE FMA decoder.

This calls the same `fmaFields` kernel as `fmaRuntimeOption`, with the three decodes written
directly
instead of through nested continuations. `fmaRuntimeFlat_eq` proves their equality.
-/
@[inline] def fmaRuntimeFlatOption {fmt : FloatFormat}
    (x y z : Model fmt) : Option (Model fmt) :=
  if fmt.isIEEE then
    let xBits := x.toNatBits
    let xExponent :=
      (xBits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt
    if xExponent == FloatFormat.expAllOnesNat fmt then
      none
    else
      let xFraction := xBits &&& FloatFormat.fracMaskNat fmt
      let xMantissa :=
        if xExponent == 0 then xFraction else pow2 fmt.fracWidth + xFraction
      let yBits := y.toNatBits
      let yExponent :=
        (yBits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt
      if yExponent == FloatFormat.expAllOnesNat fmt then
        none
      else
        let yFraction := yBits &&& FloatFormat.fracMaskNat fmt
        let yMantissa :=
          if yExponent == 0 then yFraction else pow2 fmt.fracWidth + yFraction
        let zBits := z.toNatBits
        let zExponent :=
          (zBits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt
        if zExponent == FloatFormat.expAllOnesNat fmt then
          none
        else
          let zFraction := zBits &&& FloatFormat.fracMaskNat fmt
          let zMantissa :=
            if zExponent == 0 then zFraction else pow2 fmt.fracWidth + zFraction
          some <| fmaFields fmt
            (xBits.testBit (fmt.expWidth + fmt.fracWidth))
              xExponent xMantissa
            (yBits.testBit (fmt.expWidth + fmt.fracWidth))
              yExponent yMantissa
            (zBits.testBit (fmt.expWidth + fmt.fracWidth))
              zExponent zMantissa
  else
    fmaRuntimeOption x y z

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteKernel
