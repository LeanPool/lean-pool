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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Lean
public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Basic
public import LeanPool.FloatLibBinary.Numerics.Quantization.Deterministic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Optimized

/-!
# Exact dyadic decoding primitives

Finite binary interchange values decode exactly to a sign, natural significand, and integral
power-of-two exponent. This module defines that bridge and the exact comparison used by
arithmetic, conversions, and rounding.

The decoding layer is intentionally independent of any arithmetic operation. Addition,
multiplication, FMA, conversion, and directed rounding can all share the same exact domain and
prove their own final packing step.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-- Exact negation with the zero convention selected by the destination format. -/
@[inline] def negDyadic (fmt : FloatFormat) (value : Numerics.Dyadic) : Numerics.Dyadic :=
  if value.significand == 0 && !fmt.supportsSignedZero then
    Numerics.Dyadic.zero
  else
    value.neg

/-- Exact dyadic value represented by a finite value in Lean's logical float model. -/
def unpackedToDyadicOption : Float.Model.UnpackedFloat → Option Numerics.Dyadic
  | .notANumber | .infinity _ => none
  | .zero sign =>
      some { negative := modelSignBit sign, significand := 0, exponent := 0 }
  | .finite sign mantissa exponent _ =>
      some
        { negative := modelSignBit sign
          significand := mantissa
          exponent }

/-- `2^k` as a `Nat`. -/
@[inline] def pow2 (k : Nat) : Nat :=
  Nat.shiftLeft 1 k

/-- The executable shift definition of a power of two agrees with natural exponentiation. -/
theorem pow2_eq_two_pow (k : Nat) : pow2 k = 2 ^ k := by
  simp [pow2, Nat.shiftLeft_eq]

/--
Exact comparison of two dyadics by aligning their exponents and comparing signed mantissas.

This lives with the decoding primitives because finite-value comparison does not depend on any
rounding operation.
-/
def cmpDyadic (a b : Numerics.Dyadic) : Ordering :=
  if a.significand == 0 && b.significand == 0 then
    .eq
  else
    let e : Int := if a.exponent ≤ b.exponent then a.exponent else b.exponent
    let shA : Nat := Int.toNat (a.exponent - e)
    let shB : Nat := Int.toNat (b.exponent - e)
    let aNat : Nat := Nat.shiftLeft a.significand shA
    let bNat : Nat := Nat.shiftLeft b.significand shB
    let aInt : Int := if a.negative then -(Int.ofNat aNat) else Int.ofNat aNat
    let bInt : Int := if b.negative then -(Int.ofNat bNat) else Int.ofNat bNat
    compare aInt bInt

/--
Decode an IEEE bit pattern into an exact dyadic.

- NaN / Inf → `none`
- ±0 → `mant = 0`, `exp = 0` (sign preserved)
- subnormal → `mant = frac`, `exp = ieeeMinSubnormalExponent fmt`
- normal → `mant = 2^fracWidth + frac`, `exp = e_biased - (bias + fracWidth)`

Every threshold is derived from `fmt`; no fixed-width constants are used.
-/
@[inline] def ieeeToDyadicOption {fmt : FloatFormat} (x : Model fmt) : Option Numerics.Dyadic :=
  if IEEE.isNaN x || IEEE.isInf x then
    none
  else
    let s := signBit x
    let e := expField x
    let f := fracField x
    if e == 0 then
      if f == 0 then
        some { negative := s, significand := 0, exponent := 0 }
      else
        some
          { negative := s
            significand := f
            exponent := FloatFormat.ieeeMinSubnormalExponent fmt }
    else
      let significand := pow2 fmt.fracWidth + f
      let exp : Int :=
        Int.ofNat e - Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt)
      some { negative := s, significand, exponent := exp }

/--
Compiled IEEE finite decoder.

The storage word is converted to `Nat` once, then all three fields are extracted from that shared
value. The exponent field alone determines whether an IEEE encoding is exceptional, so the
decoder also avoids the repeated masks and shifts performed by `IEEE.isNaN` and `IEEE.isInf`.
-/
@[inline] def ieeeToDyadicImplOption {fmt : FloatFormat} (x : Model fmt) : Option Numerics.Dyadic :=
  let bits := x.toNatBits
  let e := (bits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt
  if e == FloatFormat.expAllOnesNat fmt then
    none
  else
    let s := bits.testBit (fmt.expWidth + fmt.fracWidth)
    let f := bits &&& FloatFormat.fracMaskNat fmt
    if e == 0 then
      if f == 0 then
        some { negative := s, significand := 0, exponent := 0 }
      else
        some
          { negative := s
            significand := f
            exponent := FloatFormat.ieeeMinSubnormalExponent fmt }
    else
      let significand := pow2 fmt.fracWidth + f
      let exp : Int :=
        Int.ofNat e - Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt)
      some { negative := s, significand, exponent := exp }

/-- The compiler uses the single-pass field decoder while proofs retain `ieeeToDyadicOption`. -/
@[csimp] theorem toDyadic_eq_toDyadicImpl :
    @ieeeToDyadicOption = @ieeeToDyadicImplOption := by
  funext fmt x
  change ieeeToDyadicOption x =
    (let e := expFieldImpl x
     if e == FloatFormat.expAllOnesNat fmt then
       none
     else
       let s := signBitImpl x
       let f := fracFieldImpl x
       if e == 0 then
         if f == 0 then
           some { negative := s, significand := 0, exponent := 0 }
         else
           some
             { negative := s
               significand := f
               exponent := FloatFormat.ieeeMinSubnormalExponent fmt }
       else
         let significand := pow2 fmt.fracWidth + f
         let exp : Int :=
           Int.ofNat e - Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt)
         some { negative := s, significand, exponent := exp })
  rw [← expField_eq_expFieldImpl_apply x, ← signBit_eq_signBitImpl_apply x,
    ← fracField_eq_fracFieldImpl_apply x]
  by_cases he : expField x = FloatFormat.expAllOnesNat fmt
  · simp [ieeeToDyadicOption, IEEE.isNaN, IEEE.isInf, he]
  · simp [ieeeToDyadicOption, IEEE.isNaN, IEEE.isInf, he]


end Model

end FloatLib.Floats.Formats.BinaryInterchange
