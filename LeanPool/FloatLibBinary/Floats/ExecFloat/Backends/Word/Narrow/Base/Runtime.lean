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


public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Core
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Catalog
public import LeanPool.FloatLibBinary.Numerics.Exact.RationalBinary

/-!
# Native binary32 storage and rounding primitives

`Model FloatFormat.binary32` remains the theorem-facing representation. Narrow-word kernels share
a `UInt32` view, direct field operations, exact finite decoding, and rounding primitives
defined here.

Operation-specific kernels and their refinements live in sibling modules. Keeping this base small
prevents representation-only clients from importing the much larger addition and fused-operation
proof developments.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Clauses 3.4, 4.3.1, 5.4.1, and 6.2,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
- Lean, `Init.Data.Float.Model`, for the kernel-visible logical floating-point model used by
  the surrounding agreement development.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/-- The generic binary32 carrier. -/
abbrev Value := Model FloatFormat.binary32

/-- View generic binary32 storage as a native word. -/
@[inline] def toUInt32 (x : Value) : UInt32 :=
  UInt32.ofBitVec x.bits

/-- Rewrap a native binary32 word in the generic carrier. -/
@[inline] def ofUInt32 (bits : UInt32) : Value :=
  Model.ofBits bits.toBitVec

/-! Native storage operations -/

/-- Toggle the binary32 sign bit without passing through generic `BitVec` arithmetic. -/
@[inline] def negate (x : Value) : Value :=
  ofUInt32 (toUInt32 x ^^^ 0x80000000)

/-- Extract the binary32 sign from a native word. -/
@[inline] def signBit (bits : UInt32) : Bool :=
  (bits &&& 0x80000000) != 0

/-- Extract the binary32 biased exponent from a native word. -/
@[inline] def expField (bits : UInt32) : UInt32 :=
  (bits >>> 23) &&& 0xff

/-- Extract the binary32 fraction from a native word. -/
@[inline] def fracField (bits : UInt32) : UInt32 :=
  bits &&& 0x007fffff

/-- Decode a finite binary32 native word to the generic exact dyadic representation. -/
@[inline] def toDyadicOption (bits : UInt32) : Option Numerics.Dyadic :=
  let exponent := expField bits
  let fraction := fracField bits
  if exponent == 0xff then
    none
  else
    let sign := signBit bits
    if exponent == 0 then
      if fraction == 0 then
        some { negative := sign, significand := 0, exponent := 0 }
      else
        some { negative := sign, significand := fraction.toNat, exponent := -149 }
    else
      some {
        negative := sign
        significand := Model.pow2 23 + fraction.toNat
        exponent := Int.ofNat exponent.toNat - 150 }

/-- Convert natural-number fields to native words, then mask and pack the binary32 fields. -/
@[inline] def mkBits (sign : Bool) (exponent fraction : Nat) : UInt32 :=
  let signBits : UInt32 := if sign then (1 : UInt32) <<< 31 else 0
  let exponentBits : UInt32 := (UInt32.ofNat exponent &&& 0xff) <<< 23
  let fractionBits : UInt32 := UInt32.ofNat fraction &&& 0x007fffff
  signBits ||| exponentBits ||| fractionBits

/-- Round an exact dyadic to a native binary32 word, using nearest-even rounding. -/
@[inline] def roundDyadic (value : Numerics.Dyadic) : UInt32 :=
  if value.significand == 0 then
    if value.negative then 0x80000000 else 0
  else
    let leading := Nat.log2 value.significand
    let totalExponent := Int.ofNat leading + value.exponent
    if totalExponent < -126 then
      let fraction :=
        match value.exponent + 149 with
        | .ofNat shift => Nat.shiftLeft value.significand shift
        | .negSucc shift => Numerics.roundShiftRightEven value.significand (shift + 1)
      if fraction == 0 then
        if value.negative then 0x80000000 else 0
      else if fraction == Model.pow2 23 then
        mkBits value.negative 1 0
      else
        mkBits value.negative 0 fraction
    else
      let roundedMantissa :=
        if 23 ≤ leading then
          Numerics.roundShiftRightEven value.significand (leading - 23)
        else
          Nat.shiftLeft value.significand (23 - leading)
      let carry := roundedMantissa == Model.pow2 24
      let normalizedExponent := if carry then totalExponent + 1 else totalExponent
      if normalizedExponent > 127 then
        if value.negative then 0xff800000 else 0x7f800000
      else
        let normalizedMantissa :=
          if carry then Model.pow2 23 else roundedMantissa
        let encodedExponent := Int.toNat (normalizedExponent + 127)
        let fraction := normalizedMantissa - Model.pow2 23
        mkBits value.negative encodedExponent fraction

/--
Round the signed magnitude `(num / den) * 2^exponent` to a native binary32 word; a zero
denominator produces canonical NaN.

The exact quotient calculations remain format-independent natural-number arithmetic. Only the
binary32 thresholds and final field packing are specialized.
-/
@[inline] def roundRatScaled (sign : Bool) (num den : Nat) (exponent : Int) : UInt32 :=
  if den == 0 then
    0x7fc00000
  else if num == 0 then
    if sign then 0x80000000 else 0
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 num den
    let totalExponent := rationalExponent + exponent
    if totalExponent > 127 then
      if sign then 0xff800000 else 0x7f800000
    else if totalExponent < -150 then
      if sign then 0x80000000 else 0
    else if totalExponent < -126 then
      let scaled := Numerics.RationalBinary.scaleByPowerOfTwo num den (exponent + 149)
      let fraction := Numerics.roundQuotientEven scaled.1 scaled.2
      if fraction == 0 then
        if sign then 0x80000000 else 0
      else
        match Nat.decLe (Model.pow2 23) fraction with
        | isTrue _ => mkBits sign 1 0
        | isFalse _ => mkBits sign 0 fraction
    else
      let shift := 23 - rationalExponent
      let scaled := Numerics.RationalBinary.scaleByPowerOfTwo num den shift
      let roundedMantissa := Numerics.roundQuotientEven scaled.1 scaled.2
      let carry := roundedMantissa == Model.pow2 24
      let normalizedExponent := if carry then totalExponent + 1 else totalExponent
      let normalizedMantissa :=
        if carry then Model.pow2 23 else roundedMantissa
      if normalizedExponent > 127 then
        if sign then 0xff800000 else 0x7f800000
      else
        let encodedExponent := Int.toNat (normalizedExponent + 127)
        let fraction := normalizedMantissa - Model.pow2 23
        mkBits sign encodedExponent fraction

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
