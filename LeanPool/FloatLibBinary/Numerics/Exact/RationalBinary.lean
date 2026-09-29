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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Basic

/-!
# Exact rational scaling by powers of two

Binary formats repeatedly need the same small collection of exact operations: locate a positive
rational between consecutive powers of two, move a binary exponent into a numerator or
denominator, and compare a signed rational with a dyadic without constructing an enormous shifted
integer.

These operations belong to the exact numerical layer rather than to any one floating-point
format. IEEE interchange, P3109, posits, and application-defined binary quantizers may therefore
share them without importing one another's encoding or exceptional-value policy.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace RationalBinary

/-- Test `numerator / denominator < 2^exponent` for a positive denominator, using integers. -/
@[inline] def lessThanPowerOfTwo
    (numerator denominator : Nat) (exponent : Int) : Bool :=
  match exponent with
  | .ofNat shift => numerator < Nat.shiftLeft denominator shift
  | .negSucc shift => Nat.shiftLeft numerator (shift + 1) < denominator

/-- Nonnegative exponents shift the denominator in the strict comparison. -/
@[simp, grind =] theorem lessThanPowerOfTwo_ofNat
    (numerator denominator shift : Nat) :
    lessThanPowerOfTwo numerator denominator (Int.ofNat shift) =
      decide (numerator < Nat.shiftLeft denominator shift) :=
  rfl

/-- A natural exponent shifts the denominator in the strict comparison. -/
@[simp, grind =] theorem lessThanPowerOfTwo_natCast
    (numerator denominator shift : Nat) :
    lessThanPowerOfTwo numerator denominator (shift : Int) =
      decide (numerator < Nat.shiftLeft denominator shift) :=
  rfl

/-- Negative exponents shift the numerator in the strict comparison. -/
@[simp, grind =] theorem lessThanPowerOfTwo_negSucc
    (numerator denominator shift : Nat) :
    lessThanPowerOfTwo numerator denominator (Int.negSucc shift) =
      decide (Nat.shiftLeft numerator (shift + 1) < denominator) :=
  rfl

/-- Test `numerator / denominator ≥ 2^exponent` for a positive denominator, using integers. -/
@[inline] def atLeastPowerOfTwo
    (numerator denominator : Nat) (exponent : Int) : Bool :=
  match exponent with
  | .ofNat shift => numerator ≥ Nat.shiftLeft denominator shift
  | .negSucc shift => Nat.shiftLeft numerator (shift + 1) ≥ denominator

/-- Nonnegative exponents shift the denominator in the non-strict comparison. -/
@[simp, grind =] theorem atLeastPowerOfTwo_ofNat
    (numerator denominator shift : Nat) :
    atLeastPowerOfTwo numerator denominator (Int.ofNat shift) =
      decide (numerator ≥ Nat.shiftLeft denominator shift) :=
  rfl

/-- A natural exponent shifts the denominator in the non-strict comparison. -/
@[simp, grind =] theorem atLeastPowerOfTwo_natCast
    (numerator denominator shift : Nat) :
    atLeastPowerOfTwo numerator denominator (shift : Int) =
      decide (numerator ≥ Nat.shiftLeft denominator shift) :=
  rfl

/-- Negative exponents shift the numerator in the non-strict comparison. -/
@[simp, grind =] theorem atLeastPowerOfTwo_negSucc
    (numerator denominator shift : Nat) :
    atLeastPowerOfTwo numerator denominator (Int.negSucc shift) =
      decide (Nat.shiftLeft numerator (shift + 1) ≥ denominator) :=
  rfl

/--
Compute `⌊log₂(numerator / denominator)⌋`.

The intended mathematical preconditions are positive numerator and denominator. Keeping the
kernel total makes it convenient inside executable quantizers; proofs establish the preconditions
where logarithmic bounds are used.
-/
@[inline] def floorLog2 (numerator denominator : Nat) : Int :=
  let initial :=
    Int.ofNat numerator.log2 - Int.ofNat denominator.log2
  let lower :=
    if lessThanPowerOfTwo numerator denominator initial then
      initial - 1
    else
      initial
  if atLeastPowerOfTwo numerator denominator (lower + 1) then
    lower + 1
  else
    lower

/--
Represent `(numerator / denominator) * 2^exponent` as a ratio of natural numbers.

Positive exponents shift the numerator and negative exponents shift the denominator. No division
or approximation occurs.
-/
@[inline] def scaleByPowerOfTwo
    (numerator denominator : Nat) : Int → Nat × Nat
  | .ofNat shift => (Nat.shiftLeft numerator shift, denominator)
  | .negSucc shift =>
      (numerator, Nat.shiftLeft denominator (shift + 1))

/-- Scaling by a nonnegative exponent shifts only the numerator. -/
@[simp, grind =] theorem scaleByPowerOfTwo_ofNat
    (numerator denominator shift : Nat) :
    scaleByPowerOfTwo numerator denominator (Int.ofNat shift) =
      (Nat.shiftLeft numerator shift, denominator) :=
  rfl

/-- Scaling by a natural exponent shifts only the numerator. -/
@[simp, grind =] theorem scaleByPowerOfTwo_natCast
    (numerator denominator shift : Nat) :
    scaleByPowerOfTwo numerator denominator (shift : Int) =
      (Nat.shiftLeft numerator shift, denominator) :=
  rfl

/-- Scaling by `2^0` leaves both sides of the exact quotient unchanged. -/
@[simp, grind =] theorem scaleByPowerOfTwo_zero
    (numerator denominator : Nat) :
    scaleByPowerOfTwo numerator denominator 0 =
      (numerator, denominator) := by
  simp [scaleByPowerOfTwo]

/-- Scaling by a negative exponent shifts only the denominator. -/
@[simp, grind =] theorem scaleByPowerOfTwo_negSucc
    (numerator denominator shift : Nat) :
    scaleByPowerOfTwo numerator denominator (Int.negSucc shift) =
      (numerator, Nat.shiftLeft denominator (shift + 1)) :=
  rfl

/-- A nonzero numerator remains nonzero after exact binary scaling. -/
theorem scaleByPowerOfTwo_fst_ne_zero
    (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) :
    (scaleByPowerOfTwo numerator denominator exponent).1 ≠ 0 := by
  cases exponent with
  | ofNat shift =>
      simp only [scaleByPowerOfTwo_ofNat]
      exact mt Nat.shiftLeft_eq_zero_iff.mp hnumerator
  | negSucc shift =>
      simpa using hnumerator

/-- A nonzero denominator remains nonzero after exact binary scaling. -/
theorem scaleByPowerOfTwo_snd_ne_zero
    (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    (scaleByPowerOfTwo numerator denominator exponent).2 ≠ 0 := by
  cases exponent with
  | ofNat shift =>
      simpa using hdenominator
  | negSucc shift =>
      simp only [scaleByPowerOfTwo_negSucc]
      exact mt Nat.shiftLeft_eq_zero_iff.mp hdenominator

/--
Compare `(numerator / denominator) * 2^exponent`, with the supplied sign, against a dyadic.

A zero denominator returns `none`. After multiplying the denominator by the dyadic significand,
a leading-position test often decides the result. Only equal leading positions require exponent
alignment; that shift is then bounded by the integer operand widths.
-/
def compareDyadicScaledOption (negative : Bool) (numerator denominator : Nat)
    (exponent : Int) (value : Dyadic) : Option Ordering :=
  if denominator == 0 then
    none
  else if numerator == 0 then
    if value.significand == 0 then some .eq
    else if value.negative then some .gt else some .lt
  else if value.significand == 0 then
    if negative then some .lt else some .gt
  else if negative != value.negative then
    if negative then some .lt else some .gt
  else
    let relativeExponent := exponent - value.exponent
    let scaledDenominator := denominator * value.significand
    let leadingExponent :=
      floorLog2 numerator scaledDenominator + relativeExponent
    let magnitudeOrder :=
      if leadingExponent < 0 then
        .lt
      else if leadingExponent > 0 then
        .gt
      else
        let scaled :=
          scaleByPowerOfTwo numerator scaledDenominator relativeExponent
        compare scaled.1 scaled.2
    some (if negative then magnitudeOrder.swap else magnitudeOrder)

/-- Compare an exact signed rational with a dyadic. -/
def compareDyadicOption (negative : Bool) (numerator denominator : Nat)
    (value : Dyadic) : Option Ordering :=
  compareDyadicScaledOption negative numerator denominator 0 value

end RationalBinary
end FloatLib.Numerics
