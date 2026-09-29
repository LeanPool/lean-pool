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
# Executable exact-dyadic arithmetic

These routines compute exact multiplication, addition, subtraction, and fused multiply-add before
any target-format rounding occurs. Record entry points are convenient in specifications; matching
field-level entry points let packed decoders reuse the same semantics without constructing
short-lived input records.

The representation is not normalized after every operation. Alignment uses the smaller exponent,
which leaves normalization to the target-format rounder. `Proof` establishes that the field-level
operations agree with their record-based counterparts and preserve rational denotation.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace Dyadic

/--
Exact product from scalar dyadic fields.

Packed decoders expose these fields individually. Keeping this operation below the record boundary
lets verified execution kernels avoid allocating two short-lived input records while returning the
same single exact result consumed by rounding.
-/
@[inline] def mulFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Dyadic :=
  { negative := Bool.xor leftNegative rightNegative
    significand := leftSignificand * rightSignificand
    exponent := leftExponent + rightExponent }

/-- Exact product of two dyadic values. -/
@[inline] def mul (left right : Dyadic) : Dyadic :=
  mulFields left.negative left.significand left.exponent
    right.negative right.significand right.exponent

/--
Exact addition from scalar dyadic fields by alignment at the smaller exponent.

If the mathematical sum is zero, the result retains a negative sign only when both operands were
negative. This agrees with the usual nearest-even signed-zero convention while remaining harmless
for formats, such as posits, that have a unique zero.
-/
@[inline] def addFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Dyadic :=
  if leftSignificand == 0 then
    if rightSignificand == 0 then
      { negative := leftNegative && rightNegative, significand := 0, exponent := 0 }
    else
      {
        negative := rightNegative
        significand := rightSignificand
        exponent := rightExponent
      }
  else if rightSignificand == 0 then
    {
      negative := leftNegative
      significand := leftSignificand
      exponent := leftExponent
    }
  else if leftExponent ≤ rightExponent then
    let shift := Int.toNat (rightExponent - leftExponent)
    let leftInt :=
      if leftNegative then -Int.ofNat leftSignificand else Int.ofNat leftSignificand
    let shiftedRight := Nat.shiftLeft rightSignificand shift
    let rightInt :=
      if rightNegative then -Int.ofNat shiftedRight else Int.ofNat shiftedRight
    let sum := leftInt + rightInt
    if sum == 0 then
      { negative := leftNegative && rightNegative, significand := 0, exponent := 0 }
    else
      { negative := sum < 0, significand := sum.natAbs, exponent := leftExponent }
  else
    let shift := Int.toNat (leftExponent - rightExponent)
    let shiftedLeft := Nat.shiftLeft leftSignificand shift
    let leftInt :=
      if leftNegative then -Int.ofNat shiftedLeft else Int.ofNat shiftedLeft
    let rightInt :=
      if rightNegative then -Int.ofNat rightSignificand else Int.ofNat rightSignificand
    let sum := leftInt + rightInt
    if sum == 0 then
      { negative := leftNegative && rightNegative, significand := 0, exponent := 0 }
    else
      { negative := sum < 0, significand := sum.natAbs, exponent := rightExponent }

/-- Exact addition of two dyadic values. -/
@[inline] def add (left right : Dyadic) : Dyadic :=
  addFields left.negative left.significand left.exponent
    right.negative right.significand right.exponent

/-- Exact subtraction from scalar dyadic fields. -/
@[inline] def subFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Dyadic :=
  addFields leftNegative leftSignificand leftExponent
    (!rightNegative) rightSignificand rightExponent

/-- Exact subtraction, expressed through exact negation and addition. -/
@[inline] def sub (left right : Dyadic) : Dyadic :=
  subFields left.negative left.significand left.exponent
    right.negative right.significand right.exponent

/--
Exact fused multiply-add from scalar dyadic fields.

The product is never rounded before addition. Only the single returned exact dyadic is intended to
cross into a format-specific rounder.
-/
@[inline] def fmaFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int)
    (addendNegative : Bool) (addendSignificand : Nat) (addendExponent : Int) :
    Dyadic :=
  addFields
    (Bool.xor leftNegative rightNegative)
    (leftSignificand * rightSignificand)
    (leftExponent + rightExponent)
    addendNegative addendSignificand addendExponent

end Dyadic
end FloatLib.Numerics
