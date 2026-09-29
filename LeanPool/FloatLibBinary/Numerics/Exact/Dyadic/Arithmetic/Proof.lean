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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Order
import Mathlib.Data.Int.NatAbs

/-!
# Rational semantics of dyadic arithmetic

Field-level multiplication and fused multiply-add agree with their record-based expressions.
Addition and subtraction preserve rational denotation, including when the exact result is zero.

For addition, align the operands at the smaller exponent and add their signed integer
significands. The main argument shows that recovering the sign and magnitude with `natAbs`
preserves that sum.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace Dyadic

/-! ## Field-level operations -/

/-- Multiplication combines the three stored dyadic fields independently. -/
theorem mul_eq (left right : Dyadic) :
    left.mul right =
      {
        negative := Bool.xor left.negative right.negative
        significand := left.significand * right.significand
        exponent := left.exponent + right.exponent
      } :=
  rfl

/-- Multiplication combines stored signs by exclusive-or. -/
@[simp, grind =] theorem mul_negative (left right : Dyadic) :
    (left.mul right).negative =
      Bool.xor left.negative right.negative := rfl

/-- Multiplication multiplies the stored significands. -/
@[simp, grind =] theorem mul_significand (left right : Dyadic) :
    (left.mul right).significand =
      left.significand * right.significand := rfl

/-- Multiplication adds the stored binary exponents. -/
@[simp, grind =] theorem mul_exponent (left right : Dyadic) :
    (left.mul right).exponent =
      left.exponent + right.exponent := rfl

/-- Scalar-field multiplication is exactly record-based dyadic multiplication. -/
theorem mulFields_eq
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    mulFields leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      mul
        {
          negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent
        }
        {
          negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent
        } :=
  rfl

/-- Scalar-field addition is exactly record-based dyadic addition. -/
theorem addFields_eq
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    addFields leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      add
        {
          negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent
        }
        {
          negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent
        } :=
  rfl

/-- Scalar-field subtraction is exactly record-based dyadic subtraction. -/
theorem subFields_eq
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    subFields leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      sub
        {
          negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent
        }
        {
          negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent
        } :=
  rfl

/-- Scalar-field FMA is multiplication followed by exact addition, with no intermediate rounding. -/
theorem fmaFields_eq
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int)
    (addendNegative : Bool) (addendSignificand : Nat) (addendExponent : Int) :
    fmaFields leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent =
      add
        (mul
          {
            negative := leftNegative
            significand := leftSignificand
            exponent := leftExponent
          }
          {
            negative := rightNegative
            significand := rightSignificand
            exponent := rightExponent
          })
        {
          negative := addendNegative
          significand := addendSignificand
          exponent := addendExponent
      } :=
  rfl

/-! ## Structural addition laws -/

/--
Normalize addition when the left operand stores zero.

A nonzero right operand is returned unchanged. If both operands store zero, the result uses the
canonical zero exponent and the shared signed-zero rule. In either case the left exponent is
irrelevant.
-/
@[simp] theorem add_of_left_significand_eq_zero
    (left right : Dyadic)
    (hleft : left.significand = 0) :
    add left right =
      if right.significand = 0 then
        { negative := left.negative && right.negative
          significand := 0
          exponent := 0 }
      else
        right := by
  simp [add, addFields, hleft]

/--
Normalize addition when the right operand stores zero.

This is the symmetric form of `add_of_left_significand_eq_zero`; in particular, the right
exponent never affects the result.
-/
@[simp] theorem add_of_right_significand_eq_zero
    (left right : Dyadic)
    (hright : right.significand = 0) :
    add left right =
      if left.significand = 0 then
        { negative := left.negative && right.negative
          significand := 0
          exponent := 0 }
      else
        left := by
  simp [add, addFields, hright]

/--
Adding two stored zeros returns the canonical zero exponent and preserves a negative sign only
when both inputs are negative.
-/
theorem add_of_significands_eq_zero
    (left right : Dyadic)
    (hleft : left.significand = 0) (hright : right.significand = 0) :
    add left right =
      { negative := left.negative && right.negative
        significand := 0
        exponent := 0 } := by
  simp [hleft, hright]

/-- Equal-exponent, same-sign addition only adds the two nonzero significands. -/
theorem add_same_sign_same_exponent
    (sign : Bool) (left right : Nat) (exponent : Int)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    add
        { negative := sign, significand := left, exponent }
        { negative := sign, significand := right, exponent } =
      { negative := sign, significand := left + right, exponent } := by
  cases sign
  · have hpositive : 0 < (left : Int) + right := by omega
    simp [add, addFields, hleft, hright, hpositive.le, hpositive.ne',
      Int.natAbs_add_of_nonneg]
  · have hnegative : -(left : Int) + -right < 0 := by omega
    simp [add, addFields, hleft, hright, hnegative, hnegative.ne,
      Int.natAbs_add_of_nonpos]

/--
At a shared exponent, opposite signs subtract magnitudes and retain the sign of the larger left
operand.
-/
theorem add_opposite_sign_same_exponent_large_left
    (largeSign smallSign : Bool) (large small : Nat) (exponent : Int)
    (hlarge : large ≠ 0) (hsmall : small ≠ 0)
    (hsign : largeSign ≠ smallSign) (hlt : small < large) :
    add
        { negative := largeSign, significand := large, exponent }
        { negative := smallSign, significand := small, exponent } =
      { negative := largeSign, significand := large - small, exponent } := by
  cases largeSign <;> cases smallSign
  · contradiction
  · have hpositive : (large : Int) + -small > 0 := by omega
    have hnatAbs : ((large : Int) + -small).natAbs = large - small := by
      simpa [Int.sub_eq_add_neg] using
        Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt hlt)
    simp [add, addFields, hlarge, hsmall, hpositive.ne', hnatAbs, hlt.le]
  · have hnegative : -(large : Int) + small < 0 := by omega
    have hnatAbs : (-(large : Int) + small).natAbs = large - small := by
      rw [show -(large : Int) + small = -((large : Int) - small) by omega,
        Int.natAbs_neg]
      exact Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt hlt)
    simp [add, addFields, hlarge, hsmall, hnegative, hnegative.ne, hnatAbs]
  · contradiction

/--
Exact addition is structurally commutative, including the signed-zero convention.

This is stronger than commutativity of rational denotation: both sides produce the same stored
zero sign and exponent.
-/
theorem add_comm (left right : Dyadic) :
    add left right = add right left := by
  rcases left with ⟨leftNegative, leftSignificand, leftExponent⟩
  rcases right with ⟨rightNegative, rightSignificand, rightExponent⟩
  unfold add addFields
  simp only [beq_iff_eq]
  by_cases hleft : leftSignificand = 0
  · by_cases hright : rightSignificand = 0
    · simp [hleft, hright, Bool.and_comm]
    · simp [hleft, hright]
  · by_cases hright : rightSignificand = 0
    · simp [hleft, hright]
    · by_cases hleftRight : leftExponent ≤ rightExponent
      · by_cases hrightLeft : rightExponent ≤ leftExponent
        · have hexponents : leftExponent = rightExponent :=
            le_antisymm hleftRight hrightLeft
          subst rightExponent
          simp [hleft, hright, Int.add_comm, Bool.and_comm]
        · simp [hleft, hright, hleftRight, hrightLeft, Int.add_comm, Bool.and_comm]
      · have hrightLeft : rightExponent ≤ leftExponent := by omega
        simp [hleft, hright, hleftRight, hrightLeft, Int.add_comm, Bool.and_comm]

/--
At a shared exponent, opposite signs subtract magnitudes and retain the sign of the larger right
operand.
-/
theorem add_opposite_sign_same_exponent_large_right
    (smallSign largeSign : Bool) (small large : Nat) (exponent : Int)
    (hsmall : small ≠ 0) (hlarge : large ≠ 0)
    (hsign : smallSign ≠ largeSign) (hlt : small < large) :
    add
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent } =
      { negative := largeSign, significand := large - small, exponent } := by
  calc
    add
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent } =
      add
        { negative := largeSign, significand := large, exponent }
        { negative := smallSign, significand := small, exponent } :=
      add_comm _ _
    _ = { negative := largeSign, significand := large - small, exponent } :=
      add_opposite_sign_same_exponent_large_left
        largeSign smallSign large small exponent hlarge hsmall hsign.symm hlt

/-- Equal nonzero magnitudes with opposite signs cancel to canonical positive zero. -/
theorem add_opposite_sign_same_exponent_eq_zero
    (leftSign rightSign : Bool) (magnitude : Nat) (exponent : Int)
    (hmagnitude : magnitude ≠ 0) (hsign : leftSign ≠ rightSign) :
    add
        { negative := leftSign, significand := magnitude, exponent }
        { negative := rightSign, significand := magnitude, exponent } =
      { negative := false, significand := 0, exponent := 0 } := by
  cases leftSign <;> cases rightSign <;>
    simp_all [add, addFields]

/--
Align a nonzero right operand at the smaller left exponent before exact addition.

This is the mathematical bridge used by bounded-word kernels that perform the shift explicitly.
-/
theorem add_align_right_to_left_exponent
    (leftNegative rightNegative : Bool)
    (leftSignificand rightSignificand : Nat)
    (leftExponent rightExponent : Int)
    (hleft : leftSignificand ≠ 0) (hright : rightSignificand ≠ 0)
    (hexponents : leftExponent ≤ rightExponent) :
    add
        { negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent }
        { negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent } =
      add
        { negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent }
        { negative := rightNegative
          significand :=
            rightSignificand.shiftLeft
              (Int.toNat (rightExponent - leftExponent))
          exponent := leftExponent } := by
  have haligned :
      rightSignificand.shiftLeft
          (Int.toNat (rightExponent - leftExponent)) ≠ 0 := by
    simp [Nat.shiftLeft_eq, hright]
  have hself : Int.toNat (leftExponent - leftExponent) = 0 := by
    omega
  unfold add addFields
  simp only [beq_iff_eq, hleft, hright, ite_false, hexponents, ite_true,
    haligned, le_refl, hself]
  rfl

/-- Align a nonzero left operand at the smaller right exponent before exact addition. -/
theorem add_align_left_to_right_exponent
    (leftNegative rightNegative : Bool)
    (leftSignificand rightSignificand : Nat)
    (leftExponent rightExponent : Int)
    (hleft : leftSignificand ≠ 0) (hright : rightSignificand ≠ 0)
    (hexponents : rightExponent < leftExponent) :
    add
        { negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent }
        { negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent } =
      add
        { negative := leftNegative
          significand :=
            leftSignificand.shiftLeft
              (Int.toNat (leftExponent - rightExponent))
          exponent := rightExponent }
        { negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent } := by
  calc
    add
        { negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent }
        { negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent } =
      add
        { negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent }
        { negative := leftNegative
          significand := leftSignificand
          exponent := leftExponent } :=
      add_comm _ _
    _ = add
        { negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent }
        { negative := leftNegative
          significand :=
            leftSignificand.shiftLeft
              (Int.toNat (leftExponent - rightExponent))
          exponent := rightExponent } :=
      add_align_right_to_left_exponent
        rightNegative leftNegative rightSignificand leftSignificand
        rightExponent leftExponent hright hleft hexponents.le
    _ = add
        { negative := leftNegative
          significand :=
            leftSignificand.shiftLeft
              (Int.toNat (leftExponent - rightExponent))
          exponent := rightExponent }
        { negative := rightNegative
          significand := rightSignificand
          exponent := rightExponent } :=
      add_comm _ _

/--
Subtract an opposite-sign magnitude one exponent below a larger left operand.

Alignment doubles the higher-exponent significand, after which this is ordinary equal-exponent
subtraction. The theorem is independent of any concrete floating-point width.
-/
theorem add_opposite_sign_adjacent_exponent_large_left
    (largeSign smallSign : Bool) (large small : Nat) (exponent : Int)
    (hlarge : large ≠ 0) (hsmall : small ≠ 0)
    (hsign : largeSign ≠ smallSign) (hlt : small < large.shiftLeft 1) :
    add
        { negative := largeSign, significand := large, exponent := exponent + 1 }
        { negative := smallSign, significand := small, exponent } =
      { negative := largeSign
        significand := large.shiftLeft 1 - small
        exponent } := by
  have hshift : Int.toNat ((exponent + 1) - exponent) = 1 := by
    omega
  have haligned : large.shiftLeft 1 ≠ 0 := by
    simp [Nat.shiftLeft_eq, hlarge]
  rw [add_align_left_to_right_exponent
    largeSign smallSign large small (exponent + 1) exponent
    hlarge hsmall (by omega)]
  simp only [hshift]
  exact add_opposite_sign_same_exponent_large_left
    largeSign smallSign (large.shiftLeft 1) small exponent
    haligned hsmall hsign hlt

/-- Symmetric adjacent-exponent subtraction with the larger magnitude on the right. -/
theorem add_opposite_sign_adjacent_exponent_large_right
    (smallSign largeSign : Bool) (small large : Nat) (exponent : Int)
    (hsmall : small ≠ 0) (hlarge : large ≠ 0)
    (hsign : smallSign ≠ largeSign) (hlt : small < large.shiftLeft 1) :
    add
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent := exponent + 1 } =
      { negative := largeSign
        significand := large.shiftLeft 1 - small
        exponent } := by
  calc
    add
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent := exponent + 1 } =
      add
        { negative := largeSign, significand := large, exponent := exponent + 1 }
        { negative := smallSign, significand := small, exponent } :=
      add_comm _ _
    _ = { negative := largeSign
          significand := large.shiftLeft 1 - small
          exponent } :=
      add_opposite_sign_adjacent_exponent_large_left
        largeSign smallSign large small exponent
        hlarge hsmall hsign.symm hlt

/-! ## Rational denotation of aligned arithmetic -/

private theorem signedSignificand_shiftLeft (value : Dyadic) (shift : Nat) :
    Rat.ofInt
        ({ negative := value.negative
           significand := Nat.shiftLeft value.significand shift
           exponent := 0 } : Dyadic).signedSignificand =
      Rat.ofInt value.signedSignificand * (2 : Rat) ^ (Int.ofNat shift) := by
  cases hnegative : value.negative <;>
    simp [signedSignificand, hnegative, Nat.shiftLeft_eq]

private theorem toRat_of_natAbs (value : Int) (exponent : Int) :
    ({ negative := decide (value < 0)
       significand := value.natAbs
       exponent } : Dyadic).toRat =
      Rat.ofInt value * (2 : Rat) ^ exponent := by
  cases value <;> simp [toRat, signedSignificand]

private theorem add_toRat_of_significand_ne_zero_of_le
    (left right : Dyadic)
    (hleft : left.significand ≠ 0)
    (hright : right.significand ≠ 0)
    (hexponents : left.exponent ≤ right.exponent) :
    (add left right).toRat = left.toRat + right.toRat := by
  let shift := Int.toNat (right.exponent - left.exponent)
  have hdifference :
      right.exponent - left.exponent = (shift : Int) := by
    simpa [shift] using
      (Int.toNat_of_nonneg
        (a := right.exponent - left.exponent)
        (sub_nonneg.mpr hexponents)).symm
  have hrightExponent :
      right.exponent = left.exponent + (shift : Int) := by
    omega
  let leftInt := left.signedSignificand
  let rightInt :=
    ({ negative := right.negative
       significand := Nat.shiftLeft right.significand shift
       exponent := 0 } : Dyadic).signedSignificand
  let sum := leftInt + rightInt
  have hadd :
      add left right =
        if sum == 0 then
          { negative := left.negative && right.negative
            significand := 0
            exponent := 0 }
        else
          { negative := decide (sum < 0)
            significand := sum.natAbs
            exponent := left.exponent } := by
    simp (config := { zeta := true })
      [add, addFields, hleft, hright, hexponents, shift, leftInt, rightInt, sum,
        signedSignificand]
  have hleftRat :
      left.toRat =
        Rat.ofInt leftInt * (2 : Rat) ^ left.exponent := by
    simp [toRat, leftInt]
  have hrightRat :
      right.toRat =
        Rat.ofInt rightInt * (2 : Rat) ^ left.exponent := by
    rw [toRat, hrightExponent,
      zpow_add₀ (by simp : (2 : Rat) ≠ 0)]
    calc
      Rat.ofInt right.signedSignificand *
          ((2 : Rat) ^ left.exponent * (2 : Rat) ^ (shift : Int)) =
          (Rat.ofInt right.signedSignificand * (2 : Rat) ^ (shift : Int)) *
            (2 : Rat) ^ left.exponent := by ac_rfl
      _ = Rat.ofInt rightInt * (2 : Rat) ^ left.exponent := by
        congr 1
        simpa [rightInt] using (signedSignificand_shiftLeft right shift).symm
  have hsum :
      left.toRat + right.toRat =
        Rat.ofInt sum * (2 : Rat) ^ left.exponent := by
    rw [hleftRat, hrightRat]
    rw [show Rat.ofInt sum = Rat.ofInt leftInt + Rat.ofInt rightInt by
      exact Int.cast_add leftInt rightInt]
    exact (add_mul _ _ _).symm
  by_cases hsumZero : sum = 0
  · rw [hadd]
    simp only [hsumZero, beq_self_eq_true, ite_true]
    rw [hsum, hsumZero]
    simp [toRat, signedSignificand]
  · have hsumBool : (sum == 0) = false :=
      (beq_eq_false_iff_ne).2 hsumZero
    have hresult :
        ({ negative := decide (sum < 0)
           significand := sum.natAbs
           exponent := left.exponent } : Dyadic).toRat =
          Rat.ofInt sum * (2 : Rat) ^ left.exponent :=
      toRat_of_natAbs sum left.exponent
    rw [hadd]
    simp only [hsumBool, Bool.false_eq_true, ite_false]
    rw [hresult, ← hsum]

private theorem add_toRat_of_significand_ne_zero
    (left right : Dyadic)
    (hleft : left.significand ≠ 0)
    (hright : right.significand ≠ 0) :
    (add left right).toRat = left.toRat + right.toRat := by
  by_cases hexponents : left.exponent ≤ right.exponent
  · exact add_toRat_of_significand_ne_zero_of_le
      left right hleft hright hexponents
  · have hreverse : right.exponent ≤ left.exponent :=
      le_of_not_ge hexponents
    calc
      (add left right).toRat = (add right left).toRat :=
        congrArg toRat (add_comm left right)
      _ = right.toRat + left.toRat :=
        add_toRat_of_significand_ne_zero_of_le
          right left hright hleft hreverse
      _ = left.toRat + right.toRat := Rat.add_comm _ _

/-! ## Public arithmetic contracts -/

/-- Exact dyadic addition commutes with rational denotation. -/
theorem add_toRat (left right : Dyadic) :
    (add left right).toRat = left.toRat + right.toRat := by
  by_cases hleft : left.significand = 0
  · have hleftRat : left.toRat = 0 := by
      simp [toRat, signedSignificand, hleft]
    by_cases hright : right.significand = 0
    · simp [add, addFields, hleft, hright, toRat, signedSignificand]
    · simp [add, addFields, hleft, hright, hleftRat]
  · by_cases hright : right.significand = 0
    · have hrightRat : right.toRat = 0 := by
        simp [toRat, signedSignificand, hright]
      simp [add, addFields, hleft, hright, hrightRat]
    · exact add_toRat_of_significand_ne_zero left right hleft hright

/-- Exact dyadic subtraction commutes with rational denotation. -/
theorem sub_toRat (left right : Dyadic) :
    (sub left right).toRat = left.toRat - right.toRat := by
  rw [sub, subFields]
  change (add left right.neg).toRat = left.toRat - right.toRat
  rw [add_toRat, neg_toRat]
  simp [sub_eq_add_neg]

/-- Multiplying canonical zero on the left returns zero with the other operand's sign and
  exponent. -/
@[simp, grind =] theorem mul_zero_left (value : Dyadic) :
    mul zero value = { negative := value.negative, significand := 0, exponent := value.exponent }
      := by
  simp [mul, mulFields, zero]

/-- Multiplying canonical zero on the right returns zero with the other operand's sign and
  exponent. -/
@[simp, grind =] theorem mul_zero_right (value : Dyadic) :
    mul value zero = { negative := value.negative, significand := 0, exponent := value.exponent }
      := by
  cases value
  simp [mul, mulFields, zero, Bool.xor]

end Dyadic
end FloatLib.Numerics
