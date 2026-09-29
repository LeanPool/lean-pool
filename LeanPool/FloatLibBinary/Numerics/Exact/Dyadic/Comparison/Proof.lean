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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Comparison.Runtime

/-!
# Correctness of dyadic comparisons

Comparisons on separate sign, significand, and exponent fields agree with comparisons on `Dyadic`
records. The results cover Boolean comparisons and the power-of-two tests used by normalization.
Kernels with unpacked operands can use these equations without constructing temporary records.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace Dyadic

/-- Flattened field comparison is exactly record-based dyadic comparison. -/
theorem compareFields_eq
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    compareFields leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      compare
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

/-- The nonnegative comparator is the ordinary exact comparator with both signs cleared. -/
theorem compareNonnegativeFields_eq_compareFields
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) :
    compareNonnegativeFields leftSignificand leftExponent
        rightSignificand rightExponent =
      compareFields false leftSignificand leftExponent
        false rightSignificand rightExponent := by
  unfold compareNonnegativeFields compareFields
  split
  · rfl
  · simp only [Bool.false_eq_true, ite_false]
    split <;> rename_i hexponents
    · simp only [sub_self, Int.toNat_zero]
      let rightMagnitude :=
        Nat.shiftLeft rightSignificand
          (Int.toNat (rightExponent - leftExponent))
      change
        Ord.compare leftSignificand rightMagnitude =
          Ord.compare (Int.ofNat leftSignificand)
            (Int.ofNat rightMagnitude)
      cases hcomparison :
          Ord.compare leftSignificand rightMagnitude with
      | lt =>
          have hless : leftSignificand < rightMagnitude :=
            Nat.compare_eq_lt.mp hcomparison
          exact
            (Int.compare_eq_lt.mpr (Int.ofNat_lt.mpr hless)).symm
      | eq =>
          have hequal : leftSignificand = rightMagnitude :=
            Nat.compare_eq_eq.mp hcomparison
          exact
            (Int.compare_eq_eq.mpr
              (congrArg Int.ofNat hequal)).symm
      | gt =>
          have hgreater : rightMagnitude < leftSignificand :=
            Nat.compare_eq_gt.mp hcomparison
          exact
            (Int.compare_eq_gt.mpr (Int.ofNat_lt.mpr hgreater)).symm
    · simp only [sub_self, Int.toNat_zero]
      let leftMagnitude :=
        Nat.shiftLeft leftSignificand
          (Int.toNat (leftExponent - rightExponent))
      change
        Ord.compare leftMagnitude rightSignificand =
          Ord.compare (Int.ofNat leftMagnitude)
            (Int.ofNat rightSignificand)
      cases hcomparison :
          Ord.compare leftMagnitude rightSignificand with
      | lt =>
          have hless : leftMagnitude < rightSignificand :=
            Nat.compare_eq_lt.mp hcomparison
          exact
            (Int.compare_eq_lt.mpr (Int.ofNat_lt.mpr hless)).symm
      | eq =>
          have hequal : leftMagnitude = rightSignificand :=
            Nat.compare_eq_eq.mp hcomparison
          exact
            (Int.compare_eq_eq.mpr
              (congrArg Int.ofNat hequal)).symm
      | gt =>
          have hgreater : rightSignificand < leftMagnitude :=
            Nat.compare_eq_gt.mp hcomparison
          exact
            (Int.compare_eq_gt.mpr (Int.ofNat_lt.mpr hgreater)).symm

/-- Flattened strict comparison is exactly record-based strict comparison. -/
theorem isLessFields_eq
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    isLessFields leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      isLess
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

/-- Nonnegative strict comparison is the ordinary flattened exact comparison. -/
theorem isLessNonnegativeFields_eq
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) :
    isLessNonnegativeFields leftSignificand leftExponent
        rightSignificand rightExponent =
      isLessFields false leftSignificand leftExponent
        false rightSignificand rightExponent := by
  unfold isLessNonnegativeFields isLessFields
  rw [compareNonnegativeFields_eq_compareFields]

/-- The leading-exponent power-of-two test is the general exact nonnegative comparison. -/
theorem isLessPowerOfTwoAtLeading_eq
    (significand : Nat) (exponent : Int) (leading : Nat) (power : Int)
    (hleading : leading = significand.log2) :
    isLessPowerOfTwoAtLeading significand exponent leading power =
      isLessNonnegativeFields significand exponent 1 power := by
  unfold isLessPowerOfTwoAtLeading
    isLessNonnegativeFields compareNonnegativeFields
  rw [hleading]
  by_cases hzero : significand = 0
  · subst significand
    have honeZero : ((1 : Nat) == 0) = false := by decide
    simp only [beq_self_eq_true, ite_true, Bool.true_and, honeZero,
      Bool.false_eq_true, ite_false]
    split <;> simp [Nat.shiftLeft_eq, Nat.compare_eq_lt]
  · simp only [beq_iff_eq, hzero, ite_false]
    have hboth :
        ¬((significand == 0 && (1 : Nat) == 0) = true) := by
      simp
    rw [ite_eq_right hboth]
    by_cases hexponents : exponent ≤ power
    · simp only [hexponents, ite_true]
      let shift := Int.toNat (power - exponent)
      have hshift :
          Int.ofNat shift = power - exponent := by
        unfold shift
        exact Int.toNat_of_nonneg (sub_nonneg.mpr hexponents)
      have hcondition :
          exponent + Int.ofNat significand.log2 < power ↔
            significand.log2 < shift := by
        change
          exponent + (significand.log2 : Int) < power ↔
            significand.log2 < shift
        omega
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, Nat.compare_eq_lt,
        hcondition, Nat.log2_lt hzero]
      simp [shift, Nat.shiftLeft_eq]
    · simp only [hexponents, ite_false]
      have hlogNonnegative :
          0 ≤ Int.ofNat significand.log2 :=
        Int.natCast_nonneg _
      have hnot :
          ¬exponent + Int.ofNat significand.log2 < power := by
        omega
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, Nat.compare_eq_lt]
      rw [Nat.lt_one_iff]
      constructor
      · exact fun hless => (hnot hless).elim
      · intro hshiftZero
        exact (hzero
          (Nat.shiftLeft_eq_zero_iff.mp hshiftZero)).elim

/-- Flattened non-strict comparison is exactly record-based non-strict comparison. -/
theorem isLessOrEqualFields_eq
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    isLessOrEqualFields leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      isLessOrEqual
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

/-- Nonnegative non-strict comparison is the ordinary flattened exact comparison. -/
theorem isLessOrEqualNonnegativeFields_eq
    (leftSignificand : Nat) (leftExponent : Int)
    (rightSignificand : Nat) (rightExponent : Int) :
    isLessOrEqualNonnegativeFields leftSignificand leftExponent
        rightSignificand rightExponent =
      isLessOrEqualFields false leftSignificand leftExponent
        false rightSignificand rightExponent := by
  unfold isLessOrEqualNonnegativeFields isLessOrEqualFields
  rw [isLessNonnegativeFields_eq]

end Dyadic
end FloatLib.Numerics
