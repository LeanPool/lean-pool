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

public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Arithmetic.Runtime
public import LeanPool.FloatLibBinary.Numerics.Exact.Dyadic.Comparison.Proof

/-!
# Rational semantics of exact-dyadic order

`Dyadic` stores a signed natural significand and an integral power of two. Its executable
comparison routines avoid constructing rationals: they align powers of two, compare natural
magnitudes, and account for signs. This module proves that those decisions are exactly the
ordering decisions made by `Dyadic.toRat`.

The correctness arguments are separate from execution. Field-level comparisons avoid temporary
`Dyadic` records, while format proofs can use rational inequalities. The later lemmas show that
the leading-position comparator agrees with full exponent alignment.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace Dyadic

/-! ## Basic rational denotations -/

/-- Canonical exact zero denotes rational zero. -/
@[simp, grind =] theorem zero_toRat : zero.toRat = 0 := by
  simp [toRat, zero, signedSignificand]

/-- The scaled-integer constructor has exactly its expected rational denotation. -/
@[simp, grind =] theorem ofScaledInt_toRat (coefficient : Int) (exponent : Int) :
    (ofScaledInt coefficient exponent).toRat =
      Rat.ofInt coefficient * (2 : Rat) ^ exponent := by
  unfold ofScaledInt toRat signedSignificand
  by_cases hnegative : coefficient < 0
  · simp [hnegative, Int.ofNat_natAbs_of_nonpos hnegative.le]
  · have hnonnegative : 0 ≤ coefficient := Int.not_lt.mp hnegative
    simp [hnegative, Int.ofNat_natAbs_of_nonneg hnonnegative]

/--
A nonzero dyadic whose sign field is clear has a strictly positive rational denotation.

Format-specific exact rounders share this fact when they reduce signed inputs to positive
magnitudes. Keeping it on the common carrier avoids duplicating sign-and-scale arguments in every
radix-two format.
-/
theorem toRat_pos_of_significand_ne_zero
    (value : Dyadic)
    (hsignificand : value.significand ≠ 0)
    (hnegative : value.negative = false) :
    0 < value.toRat := by
  rw [toRat]
  simp only [signedSignificand, hnegative, Bool.false_eq_true, ite_false]
  apply mul_pos
  · have hcast : (0 : Rat) < value.significand := by
      exact_mod_cast Nat.pos_of_ne_zero hsignificand
    exact hcast
  · exact zpow_pos (by norm_num) _

/-- A dyadic has zero rational value exactly when its integer significand is zero. -/
@[simp, grind =] theorem toRat_eq_zero_iff (value : Dyadic) :
    value.toRat = 0 ↔ value.significand = 0 := by
  have hscale : (2 : Rat) ^ value.exponent ≠ 0 :=
    zpow_ne_zero value.exponent (by norm_num)
  cases hnegative : value.negative <;>
    simp [toRat, signedSignificand, hnegative, hscale]

/-- Exact dyadic negation commutes with rational denotation. -/
theorem neg_toRat (value : Dyadic) :
    value.neg.toRat = -value.toRat := by
  cases hnegative : value.negative <;>
    simp [neg, toRat, signedSignificand, hnegative]

/-- Exact dyadic multiplication commutes with rational denotation. -/
theorem mul_toRat (left right : Dyadic) :
    (mul left right).toRat = left.toRat * right.toRat := by
  rw [toRat, toRat, toRat, mul, mulFields,
    zpow_add₀ (by simp : (2 : Rat) ≠ 0)]
  cases hleft : left.negative <;> cases hright : right.negative <;>
    simp [signedSignificand, hleft, hright, Bool.xor] <;> ac_rfl

/-! ## Exponent alignment and comparison -/

private theorem toRat_eq_aligned (value : Dyadic) (commonExponent : Int)
    (hcommon : commonExponent ≤ value.exponent) :
    value.toRat =
      Rat.ofInt
          (if value.negative then
            -Int.ofNat (Nat.shiftLeft value.significand
              (Int.toNat (value.exponent - commonExponent)))
          else
            Int.ofNat (Nat.shiftLeft value.significand
              (Int.toNat (value.exponent - commonExponent)))) *
        (2 : Rat) ^ commonExponent := by
  let shift := Int.toNat (value.exponent - commonExponent)
  have hdifference : value.exponent - commonExponent = (shift : Int) := by
    simpa [shift] using
      (Int.toNat_of_nonneg
        (a := value.exponent - commonExponent)
        (sub_nonneg.mpr hcommon)).symm
  have hexponent : value.exponent = commonExponent + (shift : Int) := by
    omega
  have hsub : commonExponent + (shift : Int) - commonExponent = (shift : Int) := by
    omega
  rw [toRat, hexponent, zpow_add₀ (by simp : (2 : Rat) ≠ 0)]
  cases hnegative : value.negative <;>
    simp [signedSignificand, hnegative, hsub, Nat.shiftLeft_eq] <;>
    ac_rfl

/--
The executable comparator is the ordinary linear-order comparator on rational denotations.

This is the proof boundary that lets format-specific rounders use aligned integers while their
specifications remain stated in mathlib's ordered rational field. Proving the three-way result
once also keeps the strict and equality corollaries below from repeating exponent alignment.
-/
theorem compare_eq_compare_toRat (left right : Dyadic) :
    Dyadic.compare left right = Ord.compare left.toRat right.toRat := by
  unfold Dyadic.compare Dyadic.compareFields
  split
  next hzero =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hzero
    rcases hzero with ⟨hleft, hright⟩
    simp [toRat, signedSignificand, hleft, hright]
  next _ =>
    let commonExponent :=
      if left.exponent ≤ right.exponent then left.exponent else right.exponent
    let leftMagnitude :=
      Nat.shiftLeft left.significand (Int.toNat (left.exponent - commonExponent))
    let rightMagnitude :=
      Nat.shiftLeft right.significand (Int.toNat (right.exponent - commonExponent))
    let leftInt :=
      if left.negative then -Int.ofNat leftMagnitude else Int.ofNat leftMagnitude
    let rightInt :=
      if right.negative then -Int.ofNat rightMagnitude else Int.ofNat rightMagnitude
    have hcommonLeft : commonExponent ≤ left.exponent := by
      simp only [commonExponent]
      split <;> omega
    have hcommonRight : commonExponent ≤ right.exponent := by
      simp only [commonExponent]
      split <;> omega
    have hleftRat :
        left.toRat = Rat.ofInt leftInt * (2 : Rat) ^ commonExponent := by
      simpa [leftInt, leftMagnitude] using
        toRat_eq_aligned left commonExponent hcommonLeft
    have hrightRat :
        right.toRat = Rat.ofInt rightInt * (2 : Rat) ^ commonExponent := by
      simpa [rightInt, rightMagnitude] using
        toRat_eq_aligned right commonExponent hcommonRight
    have hfactor : 0 < (2 : Rat) ^ commonExponent :=
      zpow_pos (by norm_num) _
    change Ord.compare leftInt rightInt = Ord.compare left.toRat right.toRat
    cases hcomparison : Ord.compare leftInt rightInt with
    | lt =>
        have hintegers : leftInt < rightInt :=
          Int.compare_eq_lt.mp hcomparison
        have hrationals : left.toRat < right.toRat := by
          rw [hleftRat, hrightRat]
          apply mul_lt_mul_of_pos_right _ hfactor
          rw [Rat.ofInt_eq_cast, Rat.ofInt_eq_cast]
          exact_mod_cast hintegers
        exact (compare_lt_iff_lt.mpr hrationals).symm
    | eq =>
        have hintegers : leftInt = rightInt :=
          Int.compare_eq_eq.mp hcomparison
        have hrationals : left.toRat = right.toRat := by
          rw [hleftRat, hrightRat, hintegers]
        exact (compare_eq_iff_eq.mpr hrationals).symm
    | gt =>
        have hintegers : rightInt < leftInt :=
          Int.compare_eq_gt.mp hcomparison
        have hrationals : right.toRat < left.toRat := by
          rw [hleftRat, hrightRat]
          apply mul_lt_mul_of_pos_right _ hfactor
          rw [Rat.ofInt_eq_cast, Rat.ofInt_eq_cast]
          exact_mod_cast hintegers
        exact (compare_gt_iff_gt.mpr hrationals).symm

/--
The integer comparator reports `lt` exactly when rational denotation is smaller.
-/
theorem compare_eq_lt_iff (left right : Dyadic) :
    Dyadic.compare left right = .lt ↔ left.toRat < right.toRat := by
  rw [compare_eq_compare_toRat, compare_lt_iff_lt]

/--
The integer comparator reports `gt` exactly when rational denotation is greater.

Keeping both strict directions at the comparator boundary lets nearest-even rounders inspect one
three-way comparison instead of evaluating two independently aligned dyadic comparisons.
-/
theorem compare_eq_gt_iff (left right : Dyadic) :
    Dyadic.compare left right = .gt ↔ right.toRat < left.toRat := by
  rw [compare_eq_compare_toRat, compare_gt_iff_gt]

/-- The integer comparator reports `eq` exactly for equal rational denotations. -/
theorem compare_eq_eq_iff (left right : Dyadic) :
    Dyadic.compare left right = .eq ↔ left.toRat = right.toRat := by
  rw [compare_eq_compare_toRat, compare_eq_iff_eq]

/-!
## Field-level scalable comparison

Optimized rounders often hold the sign, significand, and exponent in local variables rather than
in a constructed `Dyadic`. These lemmas connect that execution path to the same rational order
without requiring runtime record construction.
-/

private theorem positive_toRat_bounds
    (significand : Nat) (exponent : Int)
    (hsignificand : significand ≠ 0) :
    (2 : Rat) ^ (exponent + Int.ofNat significand.log2) ≤
        (Dyadic.mk false significand exponent).toRat ∧
      (Dyadic.mk false significand exponent).toRat <
        (2 : Rat) ^ (exponent + Int.ofNat significand.log2 + 1) := by
  have hlowerNat : 2 ^ significand.log2 ≤ significand :=
    (Nat.le_log2 hsignificand).mp (le_refl _)
  have hupperNat : significand < 2 ^ (significand.log2 + 1) :=
    (Nat.log2_lt hsignificand).mp (Nat.lt_succ_self _)
  have hlowerRat : (2 : Rat) ^ significand.log2 ≤ significand := by
    exact_mod_cast hlowerNat
  have hupperRat : (significand : Rat) < 2 ^ (significand.log2 + 1) := by
    exact_mod_cast hupperNat
  have hscale : 0 < (2 : Rat) ^ exponent :=
    zpow_pos (by norm_num) _
  rw [toRat]
  simp only [signedSignificand, Bool.false_eq_true, ite_false]
  constructor
  · rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right hlowerRat hscale.le
  · rw [show
      exponent + Int.ofNat significand.log2 + 1 =
        exponent + (Int.ofNat significand.log2 + 1) by omega]
    rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
    change
      (significand : Rat) * 2 ^ exponent <
        2 ^ exponent * 2 ^ (significand.log2 + 1)
    simpa [mul_comm] using
      mul_lt_mul_of_pos_right hupperRat hscale

private theorem positive_toRat_lt_of_leading_lt
    (leftSignificand rightSignificand : Nat)
    (leftExponent rightExponent : Int)
    (hleft : leftSignificand ≠ 0)
    (hright : rightSignificand ≠ 0)
    (hleading :
      leftExponent + Int.ofNat leftSignificand.log2 <
        rightExponent + Int.ofNat rightSignificand.log2) :
    (Dyadic.mk false leftSignificand leftExponent).toRat <
      (Dyadic.mk false rightSignificand rightExponent).toRat := by
  have hleftBound :=
    (positive_toRat_bounds leftSignificand leftExponent hleft).2
  have hrightBound :=
    (positive_toRat_bounds rightSignificand rightExponent hright).1
  calc
    (Dyadic.mk false leftSignificand leftExponent).toRat <
        (2 : Rat) ^
          (leftExponent + Int.ofNat leftSignificand.log2 + 1) :=
      hleftBound
    _ ≤ (2 : Rat) ^
          (rightExponent + Int.ofNat rightSignificand.log2) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    _ ≤ (Dyadic.mk false rightSignificand rightExponent).toRat :=
      hrightBound

/--
Leading-position magnitude comparison equals ordinary exact nonnegative comparison.

The optimized branch avoids exponent-gap allocation; this theorem keeps the existing exact
dyadic comparator as its mathematical specification.
-/
theorem Internal.compareNonzeroMagnitudes_eq_compareNonnegativeFields
    (leftSignificand rightSignificand : Nat)
    (leftExponent rightExponent : Int)
    (hleft : leftSignificand ≠ 0)
    (hright : rightSignificand ≠ 0) :
    Internal.compareNonzeroMagnitudes
        leftSignificand leftExponent rightSignificand rightExponent =
      compareNonnegativeFields
        leftSignificand leftExponent rightSignificand rightExponent := by
  unfold Internal.compareNonzeroMagnitudes
  by_cases hleftRight :
      leftExponent + Int.ofNat leftSignificand.log2 <
        rightExponent + Int.ofNat rightSignificand.log2
  · simp only [hleftRight, ite_true]
    rw [compareNonnegativeFields_eq_compareFields, compareFields_eq]
    exact
      ((compare_eq_lt_iff _ _).2
        (positive_toRat_lt_of_leading_lt
          leftSignificand rightSignificand leftExponent rightExponent
          hleft hright hleftRight)).symm
  · simp only [hleftRight, ite_false]
    by_cases hrightLeft :
        rightExponent + Int.ofNat rightSignificand.log2 <
          leftExponent + Int.ofNat leftSignificand.log2
    · simp only [hrightLeft, ite_true]
      rw [compareNonnegativeFields_eq_compareFields, compareFields_eq]
      exact
        ((compare_eq_gt_iff _ _).2
          (positive_toRat_lt_of_leading_lt
            rightSignificand leftSignificand rightExponent leftExponent
            hright hleft hrightLeft)).symm
    · simp only [hrightLeft, ite_false]
      unfold compareNonnegativeFields
      simp [hleft, hright]

private theorem compare_negative_eq_positive_swap
    (leftSignificand rightSignificand : Nat)
    (leftExponent rightExponent : Int) :
    compare
        (Dyadic.mk true leftSignificand leftExponent)
        (Dyadic.mk true rightSignificand rightExponent) =
      (compare
        (Dyadic.mk false leftSignificand leftExponent)
        (Dyadic.mk false rightSignificand rightExponent)).swap := by
  cases hcomparison :
      compare
        (Dyadic.mk false leftSignificand leftExponent)
        (Dyadic.mk false rightSignificand rightExponent) with
  | lt =>
      have hless := (compare_eq_lt_iff _ _).1 hcomparison
      have hnegative :
          (Dyadic.mk true rightSignificand rightExponent).toRat <
            (Dyadic.mk true leftSignificand leftExponent).toRat := by
        simpa [← neg_toRat] using neg_lt_neg hless
      simpa [hcomparison] using (compare_eq_gt_iff _ _).2 hnegative
  | eq =>
      have hequal := (compare_eq_eq_iff _ _).1 hcomparison
      have hnegative :
          (Dyadic.mk true leftSignificand leftExponent).toRat =
            (Dyadic.mk true rightSignificand rightExponent).toRat := by
        simpa [← neg_toRat] using congrArg Neg.neg hequal
      simpa [hcomparison] using (compare_eq_eq_iff _ _).2 hnegative
  | gt =>
      have hgreater := (compare_eq_gt_iff _ _).1 hcomparison
      have hnegative :
          (Dyadic.mk true leftSignificand leftExponent).toRat <
            (Dyadic.mk true rightSignificand rightExponent).toRat := by
        simpa [← neg_toRat] using neg_lt_neg hgreater
      simpa [hcomparison] using (compare_eq_lt_iff _ _).2 hnegative

private theorem negative_toRat_neg
    (significand : Nat) (exponent : Int)
    (hsignificand : significand ≠ 0) :
    (Dyadic.mk true significand exponent).toRat < 0 := by
  have hpositive : 0 < (Dyadic.mk false significand exponent).toRat :=
    toRat_pos_of_significand_ne_zero _ hsignificand rfl
  have hnegative : -(Dyadic.mk false significand exponent).toRat < 0 :=
    neg_lt_zero.mpr hpositive
  simpa [← neg_toRat] using hnegative

/--
Exponent-scalable field comparison has exactly the ordinary exact-dyadic result.

Kernels can use this equality to justify comparisons over large exponent ranges without
materializing an integer whose width is the exponent gap.
-/
theorem Internal.compareScalableFields_eq_compareFields
    (leftNegative : Bool) (leftSignificand : Nat) (leftExponent : Int)
    (rightNegative : Bool) (rightSignificand : Nat) (rightExponent : Int) :
    Internal.compareScalableFields
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =
      compareFields
        leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent := by
  rw [compareFields_eq]
  by_cases hleft : leftSignificand = 0
  · subst leftSignificand
    by_cases hright : rightSignificand = 0
    · subst rightSignificand
      simp [Internal.compareScalableFields, compare, compareFields]
    · cases rightNegative
      · simp only [compareScalableFields, BEq.rfl, ↓reduceIte, beq_iff_eq, hright,
        Bool.false_eq_true]
        have hpositive :
            0 <
              (Dyadic.mk false rightSignificand rightExponent).toRat :=
          toRat_pos_of_significand_ne_zero _ hright rfl
        have horder :
            (Dyadic.mk leftNegative 0 leftExponent).toRat <
              (Dyadic.mk false rightSignificand rightExponent).toRat := by
          simpa using hpositive
        exact ((compare_eq_lt_iff _ _).2 horder).symm
      · simp only [compareScalableFields, BEq.rfl, ↓reduceIte, beq_iff_eq, hright]
        have hnegative :=
          negative_toRat_neg rightSignificand rightExponent hright
        have horder :
            (Dyadic.mk true rightSignificand rightExponent).toRat <
              (Dyadic.mk leftNegative 0 leftExponent).toRat := by
          simpa using hnegative
        exact ((compare_eq_gt_iff _ _).2 horder).symm
  · by_cases hright : rightSignificand = 0
    · subst rightSignificand
      cases leftNegative
      · simp only [compareScalableFields, beq_iff_eq, hleft, ↓reduceIte, BEq.rfl,
        Bool.false_eq_true]
        have hpositive :
            0 < (Dyadic.mk false leftSignificand leftExponent).toRat :=
          toRat_pos_of_significand_ne_zero _ hleft rfl
        have horder :
            (Dyadic.mk rightNegative 0 rightExponent).toRat <
              (Dyadic.mk false leftSignificand leftExponent).toRat := by
          simpa using hpositive
        exact ((compare_eq_gt_iff _ _).2 horder).symm
      · simp only [compareScalableFields, beq_iff_eq, hleft, ↓reduceIte, BEq.rfl]
        have hnegative :=
          negative_toRat_neg leftSignificand leftExponent hleft
        have horder :
            (Dyadic.mk true leftSignificand leftExponent).toRat <
              (Dyadic.mk rightNegative 0 rightExponent).toRat := by
          simpa using hnegative
        exact ((compare_eq_lt_iff _ _).2 horder).symm
    · cases leftNegative <;> cases rightNegative
      · simp only [compareScalableFields, beq_iff_eq, hleft, ↓reduceIte, hright, bne_self_eq_false,
          Bool.false_eq_true]
        rw [Internal.compareNonzeroMagnitudes_eq_compareNonnegativeFields
          leftSignificand rightSignificand leftExponent rightExponent
          hleft hright]
        rw [compareNonnegativeFields_eq_compareFields, compareFields_eq]
      · simp only [compareScalableFields, beq_iff_eq, hleft, ↓reduceIte, hright, Bool.bne_true,
        Bool.not_false,
          Bool.false_eq_true]
        have hpositive :
            0 < (Dyadic.mk false leftSignificand leftExponent).toRat :=
          toRat_pos_of_significand_ne_zero _ hleft rfl
        have hnegative :=
          negative_toRat_neg rightSignificand rightExponent hright
        exact
          ((compare_eq_gt_iff _ _).2
            (lt_trans hnegative hpositive)).symm
      · simp only [compareScalableFields, beq_iff_eq, hleft, ↓reduceIte, hright, Bool.bne_false]
        have hnegative :=
          negative_toRat_neg leftSignificand leftExponent hleft
        have hpositive :
            0 < (Dyadic.mk false rightSignificand rightExponent).toRat :=
          toRat_pos_of_significand_ne_zero _ hright rfl
        exact
          ((compare_eq_lt_iff _ _).2
            (lt_trans hnegative hpositive)).symm
      · simp only [compareScalableFields, beq_iff_eq, hleft, ↓reduceIte, hright, bne_self_eq_false,
          Bool.false_eq_true]
        rw [Internal.compareNonzeroMagnitudes_eq_compareNonnegativeFields
          leftSignificand rightSignificand leftExponent rightExponent
          hleft hright]
        rw [compareNonnegativeFields_eq_compareFields, compareFields_eq]
        exact
          (compare_negative_eq_positive_swap
            leftSignificand rightSignificand
            leftExponent rightExponent).symm

/-- Record-based scalable comparison equals ordinary exact-dyadic comparison. -/
theorem Internal.compareScalable_eq_compare (left right : Dyadic) :
    Internal.compareScalable left right = compare left right := by
  unfold Internal.compareScalable
  rw [Internal.compareScalableFields_eq_compareFields, compareFields_eq]

/-! ## Boolean comparison API -/

/-- Boolean strict comparison agrees with rational order. -/
theorem isLess_eq_decide (left right : Dyadic) :
    isLess left right = decide (left.toRat < right.toRat) := by
  apply Bool.eq_iff_iff.mpr
  simp [isLess, compare_eq_lt_iff]

/-- Boolean non-strict comparison agrees with rational order. -/
theorem isLessOrEqual_eq_decide (left right : Dyadic) :
    isLessOrEqual left right = decide (left.toRat ≤ right.toRat) := by
  apply Bool.eq_iff_iff.mpr
  simp [isLessOrEqual, isLess_eq_decide, not_lt]

/-- Boolean numerical equality agrees with equality of exact rational denotations. -/
theorem isEqual_eq_decide (left right : Dyadic) :
    isEqual left right = decide (left.toRat = right.toRat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [isEqual, Bool.and_eq_true, isLessOrEqual_eq_decide,
    decide_eq_true_eq]
  constructor
  · intro hbounds
    exact le_antisymm hbounds.1 hbounds.2
  · intro hequal
    exact ⟨le_of_eq hequal, le_of_eq hequal.symm⟩

/-- Numerical equality is symmetric even when dyadic records are not normalized. -/
theorem isEqual_comm (left right : Dyadic) :
    isEqual left right = isEqual right left := by
  rw [isEqual_eq_decide, isEqual_eq_decide]
  simp only [eq_comm]


end Dyadic
end FloatLib.Numerics
