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

public import Mathlib.Data.Rat.Cast.Order
public import Init.Data.Dyadic.Basic

/-!
# Exact dyadic values

A `FloatLib.Numerics.Dyadic` stores a sign, natural significand, and integral power-of-two scale.
Arithmetic and rounding can work on these fields without rational normalization.

Lean core's `_root_.Dyadic`, defined in `Init.Data.Dyadic.Basic`, normalizes nonzero values to
an odd integer times a power of two and has a single zero. The FloatLib record retains an
unnormalized significand and scale, together with a separate sign for IEEE signed-zero rules.
Its `toRat` identifies both zero signs; formats with a single zero discard that sign on encoding.
`toCore` converts to Lean's normalized carrier and preserves the rational value.

The carrier provides integer conversions and rational denotation. Arithmetic and order follow in
their respective modules.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
An exact signed integer multiple of an integral power of two.

`significand = 0` denotes zero for every sign and exponent. Families that distinguish signed zero
can preserve that distinction in their semantics and rounding rules; `toRat` identifies both zeros.
-/
structure Dyadic where
  /-- `true` means negative. -/
  negative : Bool
  /-- Nonnegative integer significand. -/
  significand : Nat
  /-- Integral power-of-two scale. -/
  exponent : Int
  deriving DecidableEq, Repr

namespace Dyadic

/-- Exact dyadics are equal when all three stored scalar fields are equal. -/
@[ext] theorem ext {left right : Dyadic}
    (hnegative : left.negative = right.negative)
    (hsignificand : left.significand = right.significand)
    (hexponent : left.exponent = right.exponent) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Exact zero with the conventional nonnegative canonical fields. -/
@[inline] def zero : Dyadic :=
  { negative := false, significand := 0, exponent := 0 }

/-- Canonical exact zero has a nonnegative sign field. -/
@[simp, grind =] theorem zero_negative : zero.negative = false := rfl

/-- Canonical exact zero has a zero significand. -/
@[simp, grind =] theorem zero_significand : zero.significand = 0 := rfl

/-- Canonical exact zero uses exponent zero. -/
@[simp, grind =] theorem zero_exponent : zero.exponent = 0 := rfl

/--
Represent `coefficient * 2 ^ exponent` by extracting the integer's sign and magnitude.
Fixed-point accumulators use this conversion before rounding, without rational normalization.
-/
@[inline] def ofScaledInt (coefficient : Int) (exponent : Int) : Dyadic :=
  { negative := coefficient < 0
    significand := coefficient.natAbs
    exponent }

/-- Signed integer significand before the power-of-two scale is applied. -/
@[inline] def signedSignificand (value : Dyadic) : Int :=
  if value.negative then
    -Int.ofNat value.significand
  else
    Int.ofNat value.significand

/-- Taking the absolute value of the signed significand recovers its stored magnitude. -/
@[simp, grind =] theorem natAbs_signedSignificand (value : Dyadic) :
    value.signedSignificand.natAbs = value.significand := by
  cases hnegative : value.negative <;>
    simp [signedSignificand, hnegative]

/-- Exact rational denotation of a dyadic value. -/
@[inline] def toRat (value : Dyadic) : Rat :=
  Rat.ofInt value.signedSignificand * (2 : Rat) ^ value.exponent

/-- Normalize into Lean's dyadic carrier, identifying the two representations of zero. -/
def toCore (value : Dyadic) : _root_.Dyadic :=
  _root_.Dyadic.ofIntWithPrec value.signedSignificand (-value.exponent)

/-- Converting to Lean's normalized dyadics preserves the exact rational value. -/
@[simp, grind =] theorem toRat_toCore (value : Dyadic) :
    value.toCore.toRat = value.toRat := by
  simp only [toCore, _root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, neg_neg,
    toRat, Rat.ofInt_eq_cast]

/-- A dyadic with a clear sign field denotes its magnitude times its power-of-two scale. -/
theorem toRat_mk_false (significand : Nat) (exponent : Int) :
    (Dyadic.mk false significand exponent).toRat =
      (significand : Rat) * 2 ^ exponent :=
  rfl

/-- Any dyadic record with zero significand denotes rational zero. -/
@[simp, grind =] theorem toRat_mk_zero (negative : Bool) (exponent : Int) :
    (Dyadic.mk negative 0 exponent).toRat = 0 := by
  cases negative <;> simp [toRat, signedSignificand]

/--
Reverse the sign, including the sign of zero. Formats with a single zero apply that policy when
encoding the result.
-/
@[inline] def neg (value : Dyadic) : Dyadic :=
  { value with negative := !value.negative }

/-- Negation flips only the stored sign field. -/
@[simp, grind =] theorem neg_eq (value : Dyadic) :
    value.neg =
      { negative := !value.negative
        significand := value.significand
        exponent := value.exponent } := rfl

/-- Negation complements the stored sign. -/
@[simp, grind =] theorem neg_negative (value : Dyadic) :
    value.neg.negative = !value.negative := rfl

/-- Negation preserves the stored significand. -/
@[simp, grind =] theorem neg_significand (value : Dyadic) :
    value.neg.significand = value.significand := rfl

/-- Negation preserves the stored exponent. -/
@[simp, grind =] theorem neg_exponent (value : Dyadic) :
    value.neg.exponent = value.exponent := rfl

end Dyadic
end FloatLib.Numerics
