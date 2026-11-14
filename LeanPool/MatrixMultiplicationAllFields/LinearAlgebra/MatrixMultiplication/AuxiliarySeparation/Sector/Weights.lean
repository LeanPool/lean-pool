/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Interval weights for the three-sector convolution degeneration

Section 5.2 assigns weights to the second and third coordinates of
`C(a, 3 * h + a - 1)`. The total weight is nonnegative on convolution support,
and its zero set consists exactly of the three matching sector blocks.
The middle block is a convolution with the last two legs exchanged and the
first coordinate reversed.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Number of second-leg coordinates in the original convolution. -/
def sourceWidth (a h : ℕ) : ℕ := 3 * h + a - 1

/-- Beginning of the right sector on both the second and third legs. -/
def rightStart (a h : ℕ) : ℕ := 2 * h + a - 1

/-- A coefficient-one term of the original convolution tensor. -/
def Support (a h i j k : ℕ) : Prop :=
  i < a ∧ j < sourceWidth a h ∧ k = i + j

/-- The middle interval on the second tensor leg. -/
def MiddleY (a h j : ℕ) : Prop := h ≤ j ∧ j < rightStart a h

/-- The middle interval on the third tensor leg. -/
def MiddleZ (a h k : ℕ) : Prop := h + a - 1 ≤ k ∧ k < rightStart a h

instance (a h j : ℕ) : Decidable (MiddleY a h j) := inferInstanceAs
  (Decidable (h ≤ j ∧ j < rightStart a h))

instance (a h k : ℕ) : Decidable (MiddleZ a h k) := inferInstanceAs
  (Decidable (h + a - 1 ≤ k ∧ k < rightStart a h))

/-- No weight is assigned to the common first leg. -/
def firstWeight (_i : ℕ) : ℤ := 0

/-- Weight one on the middle second-leg interval, zero elsewhere. -/
def secondWeight (a h j : ℕ) : ℤ := if MiddleY a h j then 1 else 0

/-- Weight minus one on the middle third-leg interval, zero elsewhere. -/
def thirdWeight (a h k : ℕ) : ℤ := if MiddleZ a h k then -1 else 0

/-- Exponent of the degeneration parameter on one term. -/
def totalWeight (a h i j k : ℕ) : ℤ :=
  firstWeight i + secondWeight a h j + thirdWeight a h k

/-- The three retained blocks have matching sector labels. -/
def MatchingSectors (a h j k : ℕ) : Prop :=
  (j < h ∧ k < h + a - 1) ∨
  (MiddleY a h j ∧ MiddleZ a h k) ∨
  (rightStart a h ≤ j ∧ rightStart a h ≤ k)

/-- A middle third-leg coordinate can only be reached from the middle second leg. -/
theorem middleY_of_middleZ {a h i j k : ℕ}
    (hs : Support a h i j k) (hz : MiddleZ a h k) : MiddleY a h j := by
  unfold Support at hs
  unfold MiddleY MiddleZ rightStart at *
  omega

/-- Every term has exponent zero or one, so no negative powers occur. -/
theorem totalWeight_eq_zero_or_one {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ∨ totalWeight a h i j k = 1 := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

theorem totalWeight_nonneg {a h i j k : ℕ}
    (hs : Support a h i j k) : 0 ≤ totalWeight a h i j k := by
  rcases totalWeight_eq_zero_or_one hs with hw | hw <;> omega

/-- The constant coefficient consists exactly of the three matching blocks. -/
theorem totalWeight_eq_zero_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔ MatchingSectors a h j k := by
  unfold Support sourceWidth at hs
  unfold MatchingSectors MiddleY MiddleZ rightStart
  unfold totalWeight firstWeight secondWeight thirdWeight MiddleY MiddleZ rightStart
  split_ifs <;> omega

/-- Only a middle second-leg coordinate paired with an outer third-leg coordinate
is erased by the degeneration. -/
theorem totalWeight_eq_one_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 1 ↔ MiddleY a h j ∧ ¬ MiddleZ a h k := by
  have hmiddle := middleY_of_middleZ hs
  by_cases hy : MiddleY a h j <;> by_cases hz : MiddleZ a h k
  all_goals simp [totalWeight, firstWeight, secondWeight, thirdWeight, hy, hz] at *

/-- Parametrization of the left copy of `C(a,h)`. -/
def LeftBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧ j = r ∧ k = u + r

/-- Parametrization of the middle copy with the second and third legs exchanged. -/
def MiddleBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = a - 1 - u ∧
    j = h + u + r ∧ k = h + a - 1 + r

/-- Parametrization of the right translated copy of `C(a,h)`. -/
def RightBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧
    j = rightStart a h + r ∧ k = rightStart a h + u + r

/-- The left block preserves the actual first coordinate. -/
theorem leftBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    LeftBranch a h i j k ↔ j < h ∧ k < h + a - 1 := by
  rcases hs with ⟨hi, hj, hk⟩
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hleft, _⟩
    exact ⟨i, j, hi, hleft, rfl, rfl, hk⟩

/-- The middle support equation becomes convolution after reversing the first
coordinate and exchanging the second and third legs. -/
theorem middleBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    MiddleBranch a h i j k ↔ MiddleY a h j ∧ MiddleZ a h k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold MiddleY MiddleZ rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hy, hz⟩
    refine ⟨a - 1 - i, k - (h + a - 1), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The right block is the same convolution after translating the two outer
coordinates. -/
theorem rightBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    RightBranch a h i j k ↔ rightStart a h ≤ j ∧ rightStart a h ≤ k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold sourceWidth at hj
  unfold RightBranch rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hjr, hkr⟩
    refine ⟨i, j - (2 * h + a - 1), hi, ?_, rfl, ?_, ?_⟩ <;> omega

/-- On the left coordinate block, the support equation is the ordinary
convolution equation. -/
theorem left_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i r s ↔ s = i + r := by
  unfold Support sourceWidth
  omega

/-- Translation of the right block preserves the convolution equation. -/
theorem right_support_coordinates {a h i r s : ℕ} (hi : i < a) (hr : r < h) :
    Support a h i (rightStart a h + r) (rightStart a h + s) ↔ s = i + r := by
  unfold Support sourceWidth rightStart
  omega

/-- In middle-block coordinates the support equation is convolution with the
first coordinate reversed and the other two coordinates exchanged. -/
theorem middle_support_coordinates {a h i s r : ℕ}
    (hi : i < a) (hr : r < h) :
    Support a h i (h + s) (h + a - 1 + r) ↔ s = a - 1 - i + r := by
  unfold Support sourceWidth
  omega

/-- Exact retained support of the three-sector degeneration. -/
theorem retained_support_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  rw [totalWeight_eq_zero_iff hs, leftBranch_iff hs, middleBranch_iff hs,
    rightBranch_iff hs]
  rfl

/-- Every displayed left-branch term belongs to the original convolution. -/
theorem LeftBranch.support {a h i j k : ℕ} (hb : LeftBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed middle-branch term belongs to the original convolution. -/
theorem MiddleBranch.support {a h i j k : ℕ} (hb : MiddleBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed right-branch term belongs to the original convolution. -/
theorem RightBranch.support {a h i j k : ℕ} (hb : RightBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth rightStart
  omega

/-- Exact equality of the retained support and the three explicitly
parametrized convolution branches, without a pre-existing support assumption. -/
theorem support_and_weight_zero_iff (a h i j k : ℕ) :
    (Support a h i j k ∧ totalWeight a h i j k = 0) ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  constructor
  · rintro ⟨hs, hw⟩
    exact (retained_support_iff hs).mp hw
  · intro hb
    have hs : Support a h i j k := hb.elim LeftBranch.support
      (fun hb => hb.elim MiddleBranch.support RightBranch.support)
    exact ⟨hs, (retained_support_iff hs).mpr hb⟩

/-- The first-coordinate reversal is involutive on its natural range. -/
theorem reverse_reverse {a u : ℕ} (hu : u < a) :
    a - 1 - (a - 1 - u) = u := by
  omega

/-- The middle branch has unique reversed-convolution coordinates. -/
theorem middleBranch_coordinates_unique {a h i k u r u' r' : ℕ}
    (hu : u < a) (hu' : u' < a)
    (hi : i = a - 1 - u) (hi' : i = a - 1 - u')
    (hk : k = h + a - 1 + r) (hk' : k = h + a - 1 + r') :
    u = u' ∧ r = r' := by
  omega

/-- The left and middle branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_middleBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ MiddleBranch a h i j k := by
  intro hm
  have hl' := (leftBranch_iff hl.support).mp hl
  have hm' := (middleBranch_iff hm.support).mp hm
  unfold MiddleY at hm'
  omega

/-- The left and right branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_rightBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hl' := (leftBranch_iff hl.support).mp hl
  have hr' := (rightBranch_iff hr.support).mp hr
  have hi := hr.support.1
  unfold rightStart at hr'
  omega

/-- The middle and right branches use disjoint second-leg coordinates. -/
theorem middleBranch_not_rightBranch {a h i j k : ℕ}
    (hm : MiddleBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hm' := (middleBranch_iff hm.support).mp hm
  have hr' := (rightBranch_iff hr.support).mp hr
  unfold MiddleY at hm'
  omega

/-- Positivity of the two original dimensions makes the left branch nonempty. -/
theorem leftBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, LeftBranch a h i j k :=
  ⟨0, 0, 0, 0, 0, ha, hh, rfl, rfl, rfl⟩

/-- Positivity makes the exchanged middle branch nonempty as well. -/
theorem middleBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, MiddleBranch a h i j k := by
  refine ⟨a - 1, h, h + a - 1, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

/-- Positivity also makes the translated right branch nonempty. -/
theorem rightBranch_nonempty {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∃ i j k, RightBranch a h i j k := by
  refine ⟨0, rightStart a h, rightStart a h, 0, 0, ha, hh, ?_, ?_, ?_⟩ <;> omega

end MatrixMultiplication.AuxiliarySeparation.Sector

end MatrixMultiplicationAllFields
