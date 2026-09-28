/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.Interval
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Field.Basic
/-!
# Rational Endpoint Intervals - Core Definitions

This file defines `IntervalRat`, a concrete interval type with rational endpoints
suitable for computation. We prove the Fundamental Theorem of Interval Arithmetic
(FTIA) for each operation.

## Main definitions

* `LeanCert.Core.IntervalRat` - Intervals with rational endpoints
* `LeanCert.Core.IntervalRat.toSet` - Semantic interpretation as a subset of ℝ
* Operations: `add`, `neg`, `sub`, `mul`, `inv`, `div`

## Main theorems

* `mem_add` - FTIA for addition
* `mem_neg` - FTIA for negation
* `mem_sub` - FTIA for subtraction
* `mem_mul` - FTIA for multiplication

## Design notes

All operations maintain the invariant `lo ≤ hi`. Domain restrictions for partial
operations (like `inv`) are encoded via separate types or explicit hypotheses.
-/

@[expose] public section

namespace LeanCert.Core

/-- An interval with rational endpoints -/
structure IntervalRat where
  /-- Lower endpoint of the interval. -/
  lo : ℚ
  /-- Upper endpoint of the interval. -/
  hi : ℚ
  le : lo ≤ hi
  deriving Repr, DecidableEq

/-- Default interval [0, 0] for unsupported expression branches -/
instance : Inhabited IntervalRat where
  default := ⟨0, 0, le_refl 0⟩

namespace IntervalRat

/-- The set of reals contained in this interval -/
def toSet (I : IntervalRat) : Set ℝ := Set.Icc (I.lo : ℝ) (I.hi : ℝ)

/-- Membership in an interval -/
instance : Membership ℝ IntervalRat where
  mem I x := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

@[simp]
theorem mem_def (x : ℝ) (I : IntervalRat) : x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) :=
  Iff.rfl

/-- Membership in IntervalRat is the same as membership in Set.Icc -/
theorem mem_iff_mem_Icc (x : ℝ) (I : IntervalRat) : x ∈ I ↔ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ) := by
  simp only [mem_def, Set.mem_Icc]

/-- Universal quantifier over IntervalRat equals universal over Set.Icc -/
theorem forall_mem_iff_forall_Icc {P : ℝ → Prop} (I : IntervalRat) :
    (∀ x ∈ I, P x) ↔ (∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), P x) := by
  constructor <;> intro h x hx <;> apply h <;> simp only [mem_iff_mem_Icc] at hx ⊢ <;> exact hx

/-- Existence in IntervalRat equals existence in Set.Icc -/
theorem exists_mem_iff_exists_Icc {P : ℝ → Prop} (I : IntervalRat) :
    (∃ x ∈ I, P x) ↔ (∃ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), P x) := by
  constructor <;> intro ⟨x, hx, hp⟩ <;> exact ⟨x, by simp only [mem_iff_mem_Icc] at hx ⊢; exact
    hx, hp⟩

/-- Create an interval from a single rational -/
def singleton (q : ℚ) : IntervalRat := ⟨q, q, le_refl q⟩

theorem mem_singleton (q : ℚ) : (q : ℝ) ∈ singleton q := by
  simp only [mem_def, singleton, le_refl, and_self]

/-- The width of an interval -/
def width (I : IntervalRat) : ℚ := I.hi - I.lo

theorem width_nonneg (I : IntervalRat) : 0 ≤ I.width := by
  simp only [width, sub_nonneg]
  exact I.le

/-- Midpoint of an interval -/
def midpoint (I : IntervalRat) : ℚ := (I.lo + I.hi) / 2

/-- The midpoint of an interval is contained in the interval -/
theorem midpoint_mem (I : IntervalRat) : (I.midpoint : ℝ) ∈ I := by
  simp only [mem_def, midpoint]
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  constructor
  · -- lo ≤ (lo + hi) / 2
    have : (((I.lo + I.hi) / 2 : ℚ) : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    rw [this]
    linarith
  · -- (lo + hi) / 2 ≤ hi
    have : (((I.lo + I.hi) / 2 : ℚ) : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    rw [this]
    linarith

/-! ### Interval addition -/

/-- Add two intervals -/
def add (I J : IntervalRat) : IntervalRat where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  le := by linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add, Rat.cast_add]
  constructor <;> linarith

/-! ### Interval negation -/

/-- Negate an interval -/
def neg (I : IntervalRat) : IntervalRat where
  lo := -I.hi
  hi := -I.lo
  le := by linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg, Rat.cast_neg]
  constructor <;> linarith

/-! ### Interval subtraction -/

/-- Subtract two intervals -/
def sub (I J : IntervalRat) : IntervalRat := add I (neg J)

/-- FTIA for subtraction -/
theorem mem_sub {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x - y ∈ sub I J := by
  simp only [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

/-! ### Interval multiplication -/

/-- Helper: minimum of four rationals -/
def min4 (a b c d : ℚ) : ℚ := min (min a b) (min c d)

/-- Helper: maximum of four rationals -/
def max4 (a b c d : ℚ) : ℚ := max (max a b) (max c d)

theorem min4_le_all (a b c d : ℚ) :
    min4 a b c d ≤ a ∧ min4 a b c d ≤ b ∧ min4 a b c d ≤ c ∧ min4 a b c d ≤ d := by
  simp only [min4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  · exact le_trans (min_le_left _ _) (min_le_right _ _)
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem all_le_max4 (a b c d : ℚ) :
    a ≤ max4 a b c d ∧ b ≤ max4 a b c d ∧ c ≤ max4 a b c d ∧ d ≤ max4 a b c d := by
  simp only [max4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem le_min4_iff (x a b c d : ℚ) :
    x ≤ min4 a b c d ↔ x ≤ a ∧ x ≤ b ∧ x ≤ c ∧ x ≤ d := by
  simp only [min4, le_min_iff, and_assoc]

theorem max4_le_iff (x a b c d : ℚ) :
    max4 a b c d ≤ x ↔ a ≤ x ∧ b ≤ x ∧ c ≤ x ∧ d ≤ x := by
  simp only [max4, max_le_iff, and_assoc]

/-- Multiply two intervals -/
def mul (I J : IntervalRat) : IntervalRat where
  lo := min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  hi := max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  le := by
    simp only [min4, max4]
    exact le_trans (min_le_of_left_le (min_le_left _ _))
                   (le_max_of_le_left (le_max_left _ _))

/-- Fast interval multiplication using sign-based case splitting.
    Reduces from 4 multiplications + 12 comparisons to 2 multiplications
    in the common case (both intervals positive or both negative).
    Falls back to the full 4-way product for mixed-sign intervals. -/
def mulFast (I J : IntervalRat) : IntervalRat :=
  if hIlo : I.lo ≥ 0 then
    if hJlo : J.lo ≥ 0 then
      ⟨I.lo * J.lo, I.hi * J.hi, by nlinarith [I.le, J.le]⟩
    else if hJhi : J.hi ≤ 0 then
      ⟨I.hi * J.lo, I.lo * J.hi, by nlinarith [I.le, J.le]⟩
    else
      ⟨I.hi * J.lo, I.hi * J.hi, by nlinarith [I.le, J.le]⟩
  else if hIhi : I.hi ≤ 0 then
    if hJlo : J.lo ≥ 0 then
      ⟨I.lo * J.hi, I.hi * J.lo, by nlinarith [I.le, J.le]⟩
    else if hJhi : J.hi ≤ 0 then
      ⟨I.hi * J.hi, I.lo * J.lo, by nlinarith [I.le, J.le]⟩
    else
      ⟨I.lo * J.hi, I.lo * J.lo, by nlinarith [I.le, J.le]⟩
  else
    if hJlo : J.lo ≥ 0 then
      ⟨I.lo * J.hi, I.hi * J.hi, by nlinarith [I.le, J.le]⟩
    else if hJhi : J.hi ≤ 0 then
      ⟨I.hi * J.lo, I.lo * J.lo, by nlinarith [I.le, J.le]⟩
    else
      mul I J

/- We intentionally do not attach `mulFast` as a native replacement here.
   Native certificate checking should execute the same definition that the
   kernel proofs reason about. Keep `mulFast` available only as an internal
   candidate for future explicitly-audited runtime backends. -/

/-- Helper: for x ∈ [a₁, a₂], x*y lies between endpoint products.
    When y ≥ 0: a₁*y ≤ x*y ≤ a₂*y
    When y ≤ 0: a₂*y ≤ x*y ≤ a₁*y -/
private theorem mul_mem_endpoints_left {x a₁ a₂ y : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) :
    min (a₁ * y) (a₂ * y) ≤ x * y ∧ x * y ≤ max (a₁ * y) (a₂ * y) := by
  by_cases! hy : 0 ≤ y
  · -- y ≥ 0: multiplication preserves order, so a₁*y ≤ x*y ≤ a₂*y
    have h1 : a₁ * y ≤ x * y := mul_le_mul_of_nonneg_right ha.1 hy
    have h2 : x * y ≤ a₂ * y := mul_le_mul_of_nonneg_right ha.2 hy
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · -- y < 0: multiplication reverses order, so a₂*y ≤ x*y ≤ a₁*y
    have hy' := le_of_lt hy
    have h1 : a₂ * y ≤ x * y := mul_le_mul_of_nonpos_right ha.2 hy'
    have h2 : x * y ≤ a₁ * y := mul_le_mul_of_nonpos_right ha.1 hy'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Helper: for y ∈ [b₁, b₂], x*y lies between endpoint products.
    When x ≥ 0: x*b₁ ≤ x*y ≤ x*b₂
    When x ≤ 0: x*b₂ ≤ x*y ≤ x*b₁ -/
private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ}
    (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  by_cases! hx : 0 ≤ x
  · -- x ≥ 0: multiplication preserves order, so x*b₁ ≤ x*y ≤ x*b₂
    have h1 : x * b₁ ≤ x * y := mul_le_mul_of_nonneg_left hb.1 hx
    have h2 : x * y ≤ x * b₂ := mul_le_mul_of_nonneg_left hb.2 hx
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · -- x < 0: multiplication reverses order, so x*b₂ ≤ x*y ≤ x*b₁
    have hx' := le_of_lt hx
    have h1 : x * b₂ ≤ x * y := mul_le_mul_of_nonpos_left hb.2 hx'
    have h2 : x * y ≤ x * b₁ := mul_le_mul_of_nonpos_left hb.1 hx'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Lower bound: xy ≥ min of corner products -/
private theorem mul_lower_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y := by
  -- First, x*y ≥ min(a₁*y, a₂*y) from mul_mem_endpoints_left
  have h1 := (mul_mem_endpoints_left (y := y) ha).1
  -- Now we need: min of corners ≤ min(a₁*y, a₂*y)
  -- Case split on whether a₁*y ≤ a₂*y
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · -- min(a₁*y, a₂*y) = a₁*y
    rw [min_eq_left hcmp] at h1
    -- Need: min corners ≤ a₁*y
    -- a₁*y is between a₁*b₁ and a₁*b₂, so min(a₁*b₁, a₁*b₂) ≤ a₁*y
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₁ * b₁) (a₁ * b₂) := min_le_left _ _
      _ ≤ a₁ * y := h2
      _ ≤ x * y := h1
  · -- min(a₁*y, a₂*y) = a₂*y
    rw [min_eq_right (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₂ * b₁) (a₂ * b₂) := min_le_right _ _
      _ ≤ a₂ * y := h2
      _ ≤ x * y := h1

/-- Upper bound: xy ≤ max of corner products -/
private theorem mul_upper_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).2
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · rw [max_eq_right hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).2
    calc x * y
        ≤ a₂ * y := h1
      _ ≤ max (a₂ * b₁) (a₂ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_right _ _
  · rw [max_eq_left (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).2
    calc x * y
        ≤ a₁ * y := h1
      _ ≤ max (a₁ * b₁) (a₁ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_left _ _

/-- Key lemma: product lies in convex hull of corner products.
    For x ∈ [a₁, a₂] and y ∈ [b₁, b₂], we have
    min{a₁b₁, a₁b₂, a₂b₁, a₂b₂} ≤ xy ≤ max{a₁b₁, a₁b₂, a₂b₁, a₂b₂}

    This is a standard result from interval arithmetic: extrema of bilinear
    functions on rectangles occur at corners. -/
private theorem mul_mem_corners {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y ∧
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) :=
  ⟨mul_lower_bound ha hb, mul_upper_bound ha hb⟩

/-- FTIA for multiplication -/
theorem mem_mul {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mul I J := by
  simp only [mem_def] at *
  simp only [mul, min4, max4, Rat.cast_mul, Rat.cast_min, Rat.cast_max]
  exact mul_mem_corners hx hy

/-- Helper: show a = min4 a b c d when a ≤ b, a ≤ c, a ≤ d -/
theorem eq_min4_of_le {a b c d : ℚ} (h1 : a ≤ b) (h2 : a ≤ c) (h3 : a ≤ d) :
    a = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨le_refl _, h1, h2, h3⟩)
      (min4_le_all _ _ _ _).1

theorem eq_min4_of_le2 {a b c d : ℚ} (h1 : b ≤ a) (h2 : b ≤ c) (h3 : b ≤ d) :
    b = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨h1, le_refl _, h2, h3⟩)
      (min4_le_all _ _ _ _).2.1

theorem eq_min4_of_le3 {a b c d : ℚ} (h1 : c ≤ a) (h2 : c ≤ b) (h3 : c ≤ d) :
    c = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨h1, h2, le_refl _, h3⟩)
      (min4_le_all _ _ _ _).2.2.1

theorem eq_min4_of_le4 {a b c d : ℚ} (h1 : d ≤ a) (h2 : d ≤ b) (h3 : d ≤ c) :
    d = min4 a b c d := le_antisymm ((le_min4_iff _ _ _ _ _).mpr ⟨h1, h2, h3, le_refl _⟩)
      (min4_le_all _ _ _ _).2.2.2

theorem eq_max4_of_ge {a b c d : ℚ} (h1 : b ≤ a) (h2 : c ≤ a) (h3 : d ≤ a) :
    a = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).1 ((max4_le_iff _ _ _ _ _).mpr ⟨le_refl
      _, h1, h2, h3⟩)

theorem eq_max4_of_ge2 {a b c d : ℚ} (h1 : a ≤ b) (h2 : c ≤ b) (h3 : d ≤ b) :
    b = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).2.1 ((max4_le_iff _ _ _ _ _).mpr ⟨h1,
      le_refl _, h2, h3⟩)

theorem eq_max4_of_ge3 {a b c d : ℚ} (h1 : a ≤ c) (h2 : b ≤ c) (h3 : d ≤ c) :
    c = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).2.2.1 ((max4_le_iff _ _ _ _ _).mpr ⟨h1,
      h2, le_refl _, h3⟩)

theorem eq_max4_of_ge4 {a b c d : ℚ} (h1 : a ≤ d) (h2 : b ≤ d) (h3 : c ≤ d) :
    d = max4 a b c d := le_antisymm (all_le_max4 _ _ _ _).2.2.2 ((max4_le_iff _ _ _ _ _).mpr ⟨h1,
      h2, h3, le_refl _⟩)

/-- mulFast endpoints match mul endpoints: lo -/
private theorem mulFast_lo (I J : IntervalRat) : (mulFast I J).lo = (mul I J).lo := by
  simp only [mulFast, mul]
  split
  · split
    · exact eq_min4_of_le (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · exact eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · exact eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · split
      · exact eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_min4_of_le4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · split
      · exact eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rfl

/-- mulFast endpoints match mul endpoints: hi -/
private theorem mulFast_hi (I J : IntervalRat) : (mulFast I J).hi = (mul I J).hi := by
  simp only [mulFast, mul]
  split
  · split
    · exact eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · exact eq_max4_of_ge2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · exact eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · split
      · exact eq_max4_of_ge3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · split
      · exact eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · exact eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rfl

/-- `mulFast` preserves the containment property of `mul`.
    This is retained as documentation and a future audited optimization hook;
    production certificate checking currently uses `mul` directly. -/
theorem mem_mulFast {x y : ℝ} {I J : IntervalRat} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mulFast I J := by
  simp only [mem_def]
  rw [mulFast_lo, mulFast_hi]
  exact mem_mul hx hy

/-! ### Interval containing zero check -/

/-- Check if an interval contains zero -/
def containsZero (I : IntervalRat) : Prop := I.lo ≤ 0 ∧ 0 ≤ I.hi

/-- Decidable containsZero -/
instance (I : IntervalRat) : Decidable (containsZero I) :=
  inferInstanceAs (Decidable (I.lo ≤ 0 ∧ 0 ≤ I.hi))

/-- An interval that is guaranteed not to contain zero -/
structure IntervalRatNonzero extends IntervalRat where
  nonzero : ¬containsZero toIntervalRat

/-! ### Interval inversion (for nonzero intervals) -/

/-- Invert an interval that doesn't contain zero -/
def invNonzero (I : IntervalRatNonzero) : IntervalRat :=
  if h : 0 < I.lo then
    -- Positive interval: [1/hi, 1/lo]
    { lo := I.hi⁻¹
      hi := I.lo⁻¹
      le := by
        have hlo : (0 : ℚ) < I.lo := h
        have hhi : (0 : ℚ) < I.hi := lt_of_lt_of_le hlo I.le
        exact inv_anti₀ hlo I.le }
  else
    -- Negative interval: [1/hi, 1/lo] (both negative)
    { lo := I.hi⁻¹
      hi := I.lo⁻¹
      le := by
        have hlo_le : I.lo ≤ 0 := le_of_not_gt h
        have hhi_neg : I.hi < 0 := by
          have hnz := I.nonzero
          simp only [containsZero, not_and, not_le] at hnz
          exact hnz hlo_le
        have hlo_neg : I.lo < 0 := lt_of_le_of_lt I.le hhi_neg
        exact (inv_le_inv_of_neg hhi_neg hlo_neg).mpr I.le }

/-! ### FTIA for inversion -/

theorem mem_invNonzero {x : ℝ} {I : IntervalRatNonzero} (hx : x ∈ I.toIntervalRat) (_hxne : x ≠ 0) :
    x⁻¹ ∈ invNonzero I := by
  simp only [mem_def] at *
  simp only [invNonzero]
  split_ifs with h
  · -- Positive case: 0 < I.lo
    have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast h
    have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
    have hhi_pos : (0 : ℝ) < I.hi := lt_of_lt_of_le hlo_pos (by exact_mod_cast I.le)
    simp only [Rat.cast_inv]
    constructor
    · exact inv_anti₀ hx_pos hx.2
    · exact inv_anti₀ (by exact_mod_cast h) hx.1
  · -- Negative case
    have hlo_le : I.lo ≤ 0 := le_of_not_gt h
    have hhi_neg : I.hi < 0 := by
      have hnz := I.nonzero
      simp only [containsZero, not_and, not_le] at hnz
      exact hnz hlo_le
    have hlo_neg : I.lo < 0 := lt_of_le_of_lt I.le hhi_neg
    have hx_neg : x < 0 := lt_of_le_of_lt hx.2 (by exact_mod_cast hhi_neg)
    have hhi_neg_r : (I.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
    have hlo_neg_r : (I.lo : ℝ) < 0 := by exact_mod_cast hlo_neg
    simp only [Rat.cast_inv]
    constructor
    · exact (inv_le_inv_of_neg hhi_neg_r hx_neg).mpr hx.2
    · exact (inv_le_inv_of_neg hx_neg hlo_neg_r).mpr hx.1

/-! ### Scalar operations -/

/-- Scale an interval by a rational -/
def scale (q : ℚ) (I : IntervalRat) : IntervalRat :=
  if hq : 0 ≤ q then
    { lo := q * I.lo
      hi := q * I.hi
      le := mul_le_mul_of_nonneg_left I.le hq }
  else
    { lo := q * I.hi
      hi := q * I.lo
      le := mul_le_mul_of_nonpos_left I.le (le_of_lt (not_le.mp hq)) }

/-- FTIA for scaling -/
theorem mem_scale {x : ℝ} {I : IntervalRat} (q : ℚ) (hx : x ∈ I) :
    (q : ℝ) * x ∈ scale q I := by
  simp only [mem_def, scale] at *
  split_ifs with hq
  · simp only [Rat.cast_mul]
    constructor
    · exact mul_le_mul_of_nonneg_left hx.1 (Rat.cast_nonneg.mpr hq)
    · exact mul_le_mul_of_nonneg_left hx.2 (Rat.cast_nonneg.mpr hq)
  · simp only [Rat.cast_mul]
    have hq' : (q : ℝ) ≤ 0 := Rat.cast_nonpos.mpr (le_of_lt (not_le.mp hq))
    constructor
    · exact mul_le_mul_of_nonpos_left hx.2 hq'
    · exact mul_le_mul_of_nonpos_left hx.1 hq'

/-! ### Interval splitting -/

/-- Split an interval at its midpoint -/
def bisect (I : IntervalRat) : IntervalRat × IntervalRat :=
  let m := I.midpoint
  (⟨I.lo, m, by change I.lo ≤ (I.lo + I.hi) / 2; linarith [I.le]⟩,
   ⟨m, I.hi, by change (I.lo + I.hi) / 2 ≤ I.hi; linarith [I.le]⟩)

theorem mem_bisect_left {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hm : x ≤ I.midpoint) :
    x ∈ (bisect I).1 := by
  simp only [mem_def, bisect] at *
  exact ⟨hx.1, hm⟩

theorem mem_bisect_right {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hm : I.midpoint ≤ x) :
    x ∈ (bisect I).2 := by
  simp only [mem_def, bisect] at *
  exact ⟨hm, hx.2⟩

/-- Distance from midpoint to lo is half the width -/
theorem midpoint_sub_lo (I : IntervalRat) :
    (I.midpoint : ℝ) - I.lo = (I.hi - I.lo) / 2 := by
  simp only [midpoint]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  ring

/-- Distance from hi to midpoint is half the width -/
theorem hi_sub_midpoint (I : IntervalRat) :
    (I.hi : ℝ) - I.midpoint = (I.hi - I.lo) / 2 := by
  simp only [midpoint]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  ring

/-- Midpoint is at least lo -/
theorem midpoint_ge_lo (I : IntervalRat) : I.lo ≤ I.midpoint := by
  simp only [midpoint]
  have h := I.le
  linarith

/-- Midpoint is at most hi -/
theorem midpoint_le_hi (I : IntervalRat) : I.midpoint ≤ I.hi := by
  simp only [midpoint]
  have h := I.le
  linarith

/-- Midpoint is at least lo (real version) -/
theorem midpoint_ge_lo_real (I : IntervalRat) : (I.lo : ℝ) ≤ I.midpoint := by
  have := midpoint_ge_lo I
  exact_mod_cast this

/-- Midpoint is at most hi (real version) -/
theorem midpoint_le_hi_real (I : IntervalRat) : (I.midpoint : ℝ) ≤ I.hi := by
  have := midpoint_le_hi I
  exact_mod_cast this

/-- Left bisection is a subset of the original interval -/
theorem mem_of_mem_bisect_left {x : ℝ} {I : IntervalRat} (hx : x ∈ (bisect I).1) : x ∈ I := by
  simp only [mem_def, bisect] at *
  constructor
  · exact hx.1
  · exact le_trans hx.2 (Rat.cast_le.mpr (midpoint_le_hi I))

/-- Right bisection is a subset of the original interval -/
theorem mem_of_mem_bisect_right {x : ℝ} {I : IntervalRat} (hx : x ∈ (bisect I).2) : x ∈ I := by
  simp only [mem_def, bisect] at *
  constructor
  · exact le_trans (Rat.cast_le.mpr (midpoint_ge_lo I)) hx.1
  · exact hx.2

/-- Any point in an interval is in one of its bisected halves -/
theorem mem_bisect_or {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x ∈ (bisect I).1 ∨ x ∈ (bisect I).2 := by
  by_cases hm : x ≤ I.midpoint
  · left; exact mem_bisect_left hx hm
  · right; exact mem_bisect_right hx (le_of_lt (not_le.mp hm))

/-- The default interval [0,0] contains only 0 -/
theorem mem_default (x : ℝ) : x ∈ (default : IntervalRat) ↔ x = 0 := by
  simp only [mem_def, Inhabited.default, Rat.cast_zero]
  constructor
  · intro ⟨h1, h2⟩; linarith
  · intro h; subst h; exact ⟨le_refl _, le_refl _⟩

/-! ### Interval intersection -/

/-- Intersect two intervals. Returns none if they don't intersect. -/
def intersect (I J : IntervalRat) : Option IntervalRat :=
  let lo := max I.lo J.lo
  let hi := min I.hi J.hi
  if h : lo ≤ hi then
    some ⟨lo, hi, h⟩
  else
    none

/-- If intersection succeeds, the result contains any point in both intervals -/
theorem mem_intersect {x : ℝ} {I J : IntervalRat} (hI : x ∈ I) (hJ : x ∈ J) :
    ∃ K, intersect I J = some K ∧ x ∈ K := by
  simp only [mem_def] at hI hJ
  -- Work with the max/min at rational level
  have hle : max I.lo J.lo ≤ min I.hi J.hi := by
    have hmax_le : (I.lo : ℝ) ⊔ (J.lo : ℝ) ≤ x := sup_le hI.1 hJ.1
    have hle_min : x ≤ (I.hi : ℝ) ⊓ (J.hi : ℝ) := le_inf hI.2 hJ.2
    have hR : (I.lo : ℝ) ⊔ (J.lo : ℝ) ≤ (I.hi : ℝ) ⊓ (J.hi : ℝ) := le_trans hmax_le hle_min
    -- Convert back: on ℚ, max = sup and min = inf
    calc max I.lo J.lo = I.lo ⊔ J.lo := rfl
      _ ≤ I.hi ⊓ J.hi := by exact_mod_cast hR
      _ = min I.hi J.hi := rfl
  simp only [intersect, hle, ↓reduceDIte]
  refine ⟨⟨max I.lo J.lo, min I.hi J.hi, hle⟩, rfl, ?_⟩
  simp only [mem_def]
  constructor
  · -- Show (max I.lo J.lo : ℝ) ≤ x
    have h1 : max I.lo J.lo ≤ I.lo ∨ max I.lo J.lo = I.lo ∨ max I.lo J.lo = J.lo := by
      simp only [max_def]; split_ifs <;> simp
    cases le_or_gt I.lo J.lo with
    | inl h => simp only [max_eq_right h]; exact hJ.1
    | inr h => simp only [max_eq_left (le_of_lt h)]; exact hI.1
  · -- Show x ≤ (min I.hi J.hi : ℝ)
    cases le_or_gt I.hi J.hi with
    | inl h => simp only [min_eq_left h]; exact hI.2
    | inr h => simp only [min_eq_right (le_of_lt h)]; exact hJ.2

/-- If intersection returns some K, then K ⊆ I -/
theorem intersect_subset_left {I J K : IntervalRat} (h : intersect I J = some K) :
    K.lo ≥ I.lo ∧ K.hi ≤ I.hi := by
  simp only [intersect] at h
  by_cases hle : max I.lo J.lo ≤ min I.hi J.hi
  · simp only [hle, ↓reduceDIte, Option.some.injEq] at h
    subst h
    exact ⟨le_sup_left, inf_le_left⟩
  · simp only [hle, ↓reduceDIte, reduceCtorEq] at h

/-- If intersection returns some K, then K ⊆ J -/
theorem intersect_subset_right {I J K : IntervalRat} (h : intersect I J = some K) :
    K.lo ≥ J.lo ∧ K.hi ≤ J.hi := by
  simp only [intersect] at h
  by_cases hle : max I.lo J.lo ≤ min I.hi J.hi
  · simp only [hle, ↓reduceDIte, Option.some.injEq] at h
    subst h
    exact ⟨le_sup_right, inf_le_right⟩
  · simp only [hle, ↓reduceDIte, reduceCtorEq] at h

end IntervalRat

end LeanCert.Core
