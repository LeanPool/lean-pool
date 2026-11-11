/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card

/-!
# Bit String

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- A binary search point of dimension `n`. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- Numerical value of a bit. -/
def bitValue (b : Bool) : ℕ :=
  if b = true then 1 else 0

@[simp] theorem bitValue_false : bitValue false = 0 := by
  simp [bitValue]

@[simp] theorem bitValue_true : bitValue true = 1 := by
  simp [bitValue]

/-- Every bit value is at most one. -/
theorem bitValue_le_one (b : Bool) : bitValue b ≤ 1 := by
  cases b <;> simp

/-- The all-zero search point. -/
def allZeros (n : ℕ) : BitString n :=
  fun _ => false

/-- The all-one search point. -/
def allOnes (n : ℕ) : BitString n :=
  fun _ => true

/-- Number of one-bits in a search point. -/
def oneCount {n : ℕ} (x : BitString n) : ℕ :=
  ∑ i, bitValue (x i)

/-- Number of zero-bits in a search point. -/
def zeroCount {n : ℕ} (x : BitString n) : ℕ :=
  ∑ i, bitValue (!(x i))

/-- A bit and its complement contribute exactly one in total. -/
theorem bitValue_add_not (b : Bool) : bitValue b + bitValue (!b) = 1 := by
  cases b <;> simp [bitValue]

@[simp] theorem oneCount_allZeros (n : ℕ) : oneCount (allZeros n) = 0 := by
  simp [oneCount, allZeros]

@[simp] theorem oneCount_allOnes (n : ℕ) : oneCount (allOnes n) = n := by
  simp [oneCount, allOnes]

@[simp] theorem zeroCount_allOnes (n : ℕ) : zeroCount (allOnes n) = 0 := by
  simp [zeroCount, allOnes]

@[simp] theorem zeroCount_allZeros (n : ℕ) : zeroCount (allZeros n) = n := by
  simp [zeroCount, allZeros]

/-- The one-count and zero-count partition the `n` coordinates. -/
theorem oneCount_add_zeroCount {n : ℕ} (x : BitString n) :
    oneCount x + zeroCount x = n := by
  rw [oneCount, zeroCount, ← Finset.sum_add_distrib]
  simp [bitValue_add_not]

/-- The number of one-bits cannot exceed the dimension. -/
theorem oneCount_le {n : ℕ} (x : BitString n) : oneCount x ≤ n := by
  unfold oneCount
  calc
    (∑ i, bitValue (x i)) ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact bitValue_le_one (x i)
    _ = n := by simp

/-- The number of zero-bits cannot exceed the dimension. -/
theorem zeroCount_le {n : ℕ} (x : BitString n) : zeroCount x ≤ n := by
  unfold zeroCount
  calc
    (∑ i, bitValue (!(x i))) ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact bitValue_le_one (!(x i))
    _ = n := by simp

/-- Coordinates carrying a zero bit. -/
def zeroPositions {n : ℕ} (x : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = false)

@[simp] theorem mem_zeroPositions {n : ℕ} (x : BitString n) (i : Fin n) :
    i ∈ zeroPositions x ↔ x i = false := by
  simp [zeroPositions]

/-- `zeroCount` is also the cardinality of the finite set of zero positions. -/
theorem zeroPositions_card {n : ℕ} (x : BitString n) :
    (zeroPositions x).card = zeroCount x := by
  classical
  rw [Finset.card_eq_sum_ones]
  unfold zeroPositions zeroCount
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> simp [bitValue]

/-- Hamming distance between two bit strings. -/
def hammingDistance {n : ℕ} (x y : BitString n) : ℕ :=
  ∑ i, if x i = y i then 0 else 1

@[simp] theorem hammingDistance_self {n : ℕ} (x : BitString n) :
    hammingDistance x x = 0 := by
  simp [hammingDistance]

end ECRuntime

namespace ECRuntime

/-- Zero Hamming error characterizes the all-one string. -/
theorem zeroCount_eq_zero_iff_allOnes {n : ℕ} (x : BitString n) :
    zeroCount x = 0 ↔ x = allOnes n := by
  constructor
  · intro hx
    have hcard : (zeroPositions x).card = 0 := by
      rw [zeroPositions_card]
      exact hx
    have hempty : zeroPositions x = ∅ := Finset.card_eq_zero.mp hcard
    funext i
    cases hxi : x i with
    | false =>
        have himem : i ∈ zeroPositions x := (mem_zeroPositions x i).2 hxi
        rw [hempty] at himem
        simp at himem
    | true =>
        simp [allOnes]
  · intro hx
    subst x
    exact zeroCount_allOnes n

end ECRuntime
