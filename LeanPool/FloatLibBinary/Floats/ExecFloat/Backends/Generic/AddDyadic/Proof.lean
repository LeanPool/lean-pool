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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.AddDyadic.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rounding
import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Arithmetic.Proof
import Mathlib.Data.Int.NatAbs

/-!
# Correctness of signed-magnitude dyadic addition

The runtime aligns dyadic significands and adds their natural-number magnitudes with separate
signs. `addDyadicImpl_eq` identifies this implementation with exact dyadic addition, including
cancellation and the signed-zero rule.

The `@[csimp]` theorem `addDyadic_eq_addDyadicImpl` supplies the equality used by the compiler
substitution. The remaining public lemmas describe equal- and adjacent-exponent cases used by
native arithmetic refinements.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

private theorem natAbs_natCast_add (left right : Nat) :
    ((left : Int) + (right : Int)).natAbs = left + right := by
  rw [← Int.natCast_add left right, Int.natAbs_natCast]

/--
Adding two nonzero dyadics with the same sign and exponent adds only their significands.
-/
theorem addDyadic_sameSign_sameExponent
    (sign : Bool) (left right : Nat) (exponent : Int)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    addDyadic
        { negative := sign, significand := left, exponent := exponent }
        { negative := sign, significand := right, exponent := exponent } =
      { negative := sign, significand := left + right, exponent := exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_same_sign_same_exponent
      sign left right exponent hleft hright

/--
Subtract equal-exponent dyadic magnitudes when the left operand has the larger magnitude.

Opposite signs turn addition into exact subtraction; the result keeps the sign of the larger
magnitude and needs no rounding or exponent adjustment.
-/
theorem addDyadic_oppositeSign_sameExponent_largeLeft
    (largeSign smallSign : Bool) (large small : Nat) (exponent : Int)
    (hlarge : large ≠ 0) (hsmall : small ≠ 0)
    (hsign : largeSign ≠ smallSign) (hlt : small < large) :
    addDyadic
        { negative := largeSign, significand := large, exponent }
        { negative := smallSign, significand := small, exponent } =
      { negative := largeSign, significand := large - small, exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_same_exponent_large_left
      largeSign smallSign large small exponent hlarge hsmall hsign hlt

/--
Subtract equal-exponent dyadic magnitudes when the right operand has the larger magnitude.
-/
theorem addDyadic_oppositeSign_sameExponent_largeRight
    (smallSign largeSign : Bool) (small large : Nat) (exponent : Int)
    (hsmall : small ≠ 0) (hlarge : large ≠ 0)
    (hsign : smallSign ≠ largeSign) (hlt : small < large) :
    addDyadic
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent } =
      { negative := largeSign, significand := large - small, exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_same_exponent_large_right
      smallSign largeSign small large exponent hsmall hlarge hsign hlt

/-- Equal nonzero magnitudes with opposite signs cancel to canonical positive zero. -/
theorem addDyadic_oppositeSign_sameExponent_eq_zero
    (leftSign rightSign : Bool) (magnitude : Nat) (exponent : Int)
    (hmagnitude : magnitude ≠ 0) (hsign : leftSign ≠ rightSign) :
    addDyadic
        { negative := leftSign, significand := magnitude, exponent }
        { negative := rightSign, significand := magnitude, exponent } =
      { negative := false, significand := 0, exponent := 0 } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_same_exponent_eq_zero
      leftSign rightSign magnitude exponent hmagnitude hsign

/-- Opposite-sign subtraction with the larger left operand one exponent higher. -/
theorem addDyadic_oppositeSign_adjacentExponent_largeLeft
    (largeSign smallSign : Bool) (large small : Nat) (exponent : Int)
    (hlarge : large ≠ 0) (hsmall : small ≠ 0)
    (hsign : largeSign ≠ smallSign) (hlt : small < large.shiftLeft 1) :
    addDyadic
        { negative := largeSign, significand := large, exponent := exponent + 1 }
        { negative := smallSign, significand := small, exponent } =
      { negative := largeSign
        significand := large.shiftLeft 1 - small
        exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_adjacent_exponent_large_left
      largeSign smallSign large small exponent hlarge hsmall hsign hlt

/-- Opposite-sign subtraction with the larger right operand one exponent higher. -/
theorem addDyadic_oppositeSign_adjacentExponent_largeRight
    (smallSign largeSign : Bool) (small large : Nat) (exponent : Int)
    (hsmall : small ≠ 0) (hlarge : large ≠ 0)
    (hsign : smallSign ≠ largeSign) (hlt : small < large.shiftLeft 1) :
    addDyadic
        { negative := smallSign, significand := small, exponent }
        { negative := largeSign, significand := large, exponent := exponent + 1 } =
      { negative := largeSign
        significand := large.shiftLeft 1 - small
        exponent } := by
  simpa [addDyadic] using
    Numerics.Dyadic.add_opposite_sign_adjacent_exponent_large_right
      smallSign largeSign small large exponent hsmall hlarge hsign hlt

/-- Align the right dyadic magnitude to the left exponent without changing the exact sum. -/
theorem addDyadic_alignRightOffset
    (offset : Nat) (xSign ySign : Bool)
    (xMagnitude yMagnitude xScale yScale : Nat)
    (hx : xMagnitude ≠ 0) (hy : yMagnitude ≠ 0)
    (hscale : xScale ≤ yScale) :
    Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - Int.ofNat offset } =
      Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude <<< (yScale - xScale)
          exponent := Int.ofNat xScale - Int.ofNat offset } := by
  have hscaleInt :
      Int.ofNat xScale - Int.ofNat offset ≤
        Int.ofNat yScale - Int.ofNat offset := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hshift :
      Int.toNat
          ((Int.ofNat yScale - Int.ofNat offset) -
            (Int.ofNat xScale - Int.ofNat offset)) =
        yScale - xScale := by
    simp only [Int.ofNat_eq_natCast]
    omega
  simpa [Model.addDyadic, hshift] using
    Numerics.Dyadic.add_align_right_to_left_exponent
      xSign ySign xMagnitude yMagnitude
      (Int.ofNat xScale - Int.ofNat offset)
      (Int.ofNat yScale - Int.ofNat offset)
      hx hy hscaleInt

/-- Align the left dyadic magnitude to the right exponent without changing the exact sum. -/
theorem addDyadic_alignLeftOffset
    (offset : Nat) (xSign ySign : Bool)
    (xMagnitude yMagnitude xScale yScale : Nat)
    (hx : xMagnitude ≠ 0) (hy : yMagnitude ≠ 0)
    (hscale : yScale < xScale) :
    Model.addDyadic
        { negative := xSign
          significand := xMagnitude
          exponent := Int.ofNat xScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - Int.ofNat offset } =
      Model.addDyadic
        { negative := xSign
          significand := xMagnitude <<< (xScale - yScale)
          exponent := Int.ofNat yScale - Int.ofNat offset }
        { negative := ySign
          significand := yMagnitude
          exponent := Int.ofNat yScale - Int.ofNat offset } := by
  have hscaleInt :
      Int.ofNat yScale - Int.ofNat offset <
        Int.ofNat xScale - Int.ofNat offset := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hshift :
      Int.toNat
          ((Int.ofNat xScale - Int.ofNat offset) -
            (Int.ofNat yScale - Int.ofNat offset)) =
        xScale - yScale := by
    simp only [Int.ofNat_eq_natCast]
    omega
  simpa [Model.addDyadic, hshift] using
    Numerics.Dyadic.add_align_left_to_right_exponent
      xSign ySign xMagnitude yMagnitude
      (Int.ofNat xScale - Int.ofNat offset)
      (Int.ofNat yScale - Int.ofNat offset)
      hx hy hscaleInt

private theorem addDyadicMagnitudes_eq
    (leftSign rightSign : Bool) (left right : Nat) (exponent : Int)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    addDyadicMagnitudes leftSign rightSign left right exponent =
      let leftInt : Int := if leftSign then -(Int.ofNat left) else Int.ofNat left
      let rightInt : Int := if rightSign then -(Int.ofNat right) else Int.ofNat right
      let sum := leftInt + rightInt
      if sum == 0 then
        { negative := leftSign && rightSign, significand := 0, exponent := 0 }
      else
        { negative := sum < 0, significand := Int.natAbs sum, exponent := exponent } := by
  cases leftSign <;> cases rightSign
  · have hsumPos : (0 : Int) < (left : Int) + right := by
      have hleftPos : 0 < left := Nat.pos_of_ne_zero hleft
      have hrightPos : 0 < right := Nat.pos_of_ne_zero hright
      omega
    have hsumNe : (left : Int) + right ≠ 0 := by omega
    have hsumNonneg : (0 : Int) ≤ (left : Int) + right := by omega
    simp [addDyadicMagnitudes, hsumNe, hsumNonneg, natAbs_natCast_add]
  · by_cases heq : left = right
    · subst right
      simp [addDyadicMagnitudes]
    · by_cases hlt : left < right
      · have hsumNeg : (left : Int) + -(right : Int) < 0 := by omega
        have hsumNe : (left : Int) + -(right : Int) ≠ 0 := by omega
        have hnatAbs :
            ((left : Int) + -(right : Int)).natAbs = right - left := by
          rw [← Int.sub_eq_add_neg, ← Int.natAbs_neg, Int.neg_sub]
          exact Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt hlt)
        simp [addDyadicMagnitudes, heq, hlt, hsumNeg, hsumNe, hnatAbs]
      · have hrightLt : right < left := by omega
        have hsumPos : 0 < (left : Int) + -(right : Int) := by omega
        have hsumNe : (left : Int) + -(right : Int) ≠ 0 := by omega
        have hnatAbs :
            ((left : Int) + -(right : Int)).natAbs = left - right := by
          rw [← Int.sub_eq_add_neg]
          exact Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt hrightLt)
        simp [addDyadicMagnitudes, heq, hlt, hsumNe, hnatAbs]
  · by_cases heq : left = right
    · subst right
      simp [addDyadicMagnitudes]
    · by_cases hlt : left < right
      · have hsumPos : 0 < -(left : Int) + (right : Int) := by omega
        have hsumNe : -(left : Int) + (right : Int) ≠ 0 := by omega
        have hle : left ≤ right := Nat.le_of_lt hlt
        have hnatAbs :
            (-(left : Int) + (right : Int)).natAbs = right - left := by
          have hsumEq :
              -(left : Int) + (right : Int) = (right : Int) - (left : Int) := by
            omega
          rw [hsumEq]
          exact Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt hlt)
        simp [addDyadicMagnitudes, heq, hlt, hsumNe, hnatAbs, hle]
      · have hrightLt : right < left := by omega
        have hsumNeg : -(left : Int) + (right : Int) < 0 := by omega
        have hsumNe : -(left : Int) + (right : Int) ≠ 0 := by omega
        have hnatAbs :
            (-(left : Int) + (right : Int)).natAbs = left - right := by
          have hsumEq :
              -(left : Int) + (right : Int) = -((left : Int) - (right : Int)) := by
            omega
          rw [hsumEq, Int.natAbs_neg]
          exact Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt hrightLt)
        simp [addDyadicMagnitudes, heq, hlt, hsumNeg, hsumNe, hnatAbs]
  · have hsumNeg : -(left : Int) + -(right : Int) < 0 := by
      have hleftPos : 0 < left := Nat.pos_of_ne_zero hleft
      have hrightPos : 0 < right := Nat.pos_of_ne_zero hright
      omega
    have hsumNe : -(left : Int) + -(right : Int) ≠ 0 := by omega
    have hnatAbs :
        (-(left : Int) + -(right : Int)).natAbs = left + right := by
      have hsumEq :
          -(left : Int) + -(right : Int) = -((left : Int) + (right : Int)) := by
        omega
      rw [hsumEq, Int.natAbs_neg]
      exact natAbs_natCast_add left right
    simp [addDyadicMagnitudes, hsumNeg, hsumNe, hnatAbs]

/-- Signed-magnitude dyadic addition is equal to the public exact definition. -/
theorem addDyadicImpl_eq (a b : Numerics.Dyadic) :
    addDyadicImpl a b = addDyadic a b := by
  unfold addDyadicImpl addDyadic Numerics.Dyadic.add Numerics.Dyadic.addFields
  simp only [beq_iff_eq]
  by_cases ha : a.significand = 0
  · simp [ha]
  by_cases hb : b.significand = 0
  · simp [ha, hb]
  by_cases hexponent : a.exponent ≤ b.exponent
  · simp only [ha, hb, hexponent, ite_false, ite_true]
    have hshift :
        Nat.shiftLeft b.significand (b.exponent - a.exponent).toNat ≠ 0 := by
      simp [Nat.shiftLeft_eq, hb]
    simpa only [beq_iff_eq] using
      addDyadicMagnitudes_eq a.negative b.negative a.significand
        (Nat.shiftLeft b.significand (b.exponent - a.exponent).toNat) a.exponent
        ha hshift
  · simp only [ha, hb, hexponent, ite_false]
    have hshift :
        Nat.shiftLeft a.significand (a.exponent - b.exponent).toNat ≠ 0 := by
      simp [Nat.shiftLeft_eq, ha]
    simpa only [beq_iff_eq] using
      addDyadicMagnitudes_eq a.negative b.negative
        (Nat.shiftLeft a.significand (a.exponent - b.exponent).toNat) b.significand b.exponent
        hshift hb

/-- Exact dyadic addition is commutative, including its signed-zero rule. -/
theorem addDyadic_comm (a b : Numerics.Dyadic) :
    addDyadic a b = addDyadic b a := by
  exact Numerics.Dyadic.add_comm a b

/-- Compile exact dyadic addition through the verified signed-magnitude implementation. -/
@[csimp] theorem addDyadic_eq_addDyadicImpl :
    addDyadic = addDyadicImpl := by
  funext a b
  exact (addDyadicImpl_eq a b).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model
