/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.Dyadic
public import LeanPool.MovingSofa.LeanCert.Core.IntervalReal
public import Mathlib.Data.Rat.Cast.Order
/-!
# Dyadic Intervals

Intervals with Dyadic endpoints. These support "Outward Rounding", ensuring
mathematical soundness even when we limit numerical precision.

## Main definitions

* `IntervalDyadic` - Interval with Dyadic endpoints
* `IntervalDyadic.add`, `mul`, `neg` - Interval arithmetic operations
* `IntervalDyadic.roundOut` - Outward rounding to control precision
* `IntervalDyadic.toIntervalRat` - Convert to rational interval for verification

## Design notes

The key feature is `roundOut`: after each operation, we can enforce a minimum
exponent to prevent precision explosion. When rounding:
- Lower bounds are shifted down (toward -∞)
- Upper bounds are shifted up (toward +∞)

This maintains the containment invariant: the rounded interval always contains
the original interval, which contains the true mathematical value.

## Performance

In v1.0, `Rat` multiplication of `1/3 * 1/3 * ... * 1/3` (10 times) creates
a denominator of 3^10 = 59049. Each operation requires GCD computation.

In v1.1, with `precision = -10`, the denominator stays fixed at 2^10 = 1024.
The result is slightly less tight but computed significantly faster.
-/

@[expose] public section

namespace LeanCert.Core

/-- An interval with Dyadic endpoints.

Maintains invariant: `lo.toRat ≤ hi.toRat` -/
structure IntervalDyadic where
  /-- Lower bound -/
  lo : Dyadic
  /-- Upper bound -/
  hi : Dyadic
  /-- Invariant: lower bound ≤ upper bound -/
  le : lo.toRat ≤ hi.toRat
  deriving Repr

namespace IntervalDyadic

/-! ### Membership and Sets -/

/-- The set of reals contained in this interval -/
def toSet (I : IntervalDyadic) : Set ℝ := Set.Icc (I.lo : ℝ) (I.hi : ℝ)

/-- Membership in a Dyadic interval -/
instance : Membership ℝ IntervalDyadic where
  mem I x := (I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ)

@[simp]
theorem mem_def (x : ℝ) (I : IntervalDyadic) :
    x ∈ I ↔ (I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ) := Iff.rfl

/-! ### Conversion to IntervalRat -/

/-- Convert to IntervalRat for verification with existing theorems -/
def toIntervalRat (I : IntervalDyadic) : IntervalRat :=
  ⟨I.lo.toRat, I.hi.toRat, I.le⟩

/-- Membership is preserved by conversion to IntervalRat -/
theorem mem_toIntervalRat {x : ℝ} {I : IntervalDyadic} :
    x ∈ I ↔ x ∈ I.toIntervalRat := by
  simp only [mem_def, toIntervalRat, IntervalRat.mem_def]

/-! ### Construction -/

/-- Create a singleton interval from a Dyadic -/
def singleton (d : Dyadic) : IntervalDyadic := ⟨d, d, le_refl _⟩

/-- A Dyadic value is in its singleton interval -/
theorem mem_singleton (d : Dyadic) : (d.toRat : ℝ) ∈ singleton d := by
  simp only [mem_def, singleton]
  exact ⟨le_refl _, le_refl _⟩

/-- Default interval [0, 0] -/
instance : Inhabited IntervalDyadic where
  default := singleton Dyadic.zero

/-- Create an interval, checking the invariant -/
def mk? (lo hi : Dyadic) : Option IntervalDyadic :=
  if h : lo.toRat ≤ hi.toRat then some ⟨lo, hi, h⟩ else none

/-- The width of an interval -/
def width (I : IntervalDyadic) : Dyadic := I.hi.sub I.lo

/-- The dyadic width denotes endpoint subtraction exactly. -/
@[simp]
theorem width_toRat (I : IntervalDyadic) :
    I.width.toRat = I.hi.toRat - I.lo.toRat := by
  simp only [width, Dyadic.sub, Dyadic.toRat_add, Dyadic.toRat_neg]
  ring

/-- Exact midpoint of a dyadic interval.

Dyadics are closed under division by two, so midpoint construction must lower
the exponent rather than shift (and potentially round) the mantissa. -/
def midpoint (I : IntervalDyadic) : Dyadic :=
  (I.lo.add I.hi).scale2 (-1)

/-- The dyadic midpoint denotes the ordinary rational midpoint exactly. -/
@[simp]
theorem midpoint_toRat (I : IntervalDyadic) :
    I.midpoint.toRat = (I.lo.toRat + I.hi.toRat) / 2 := by
  simp only [midpoint, Dyadic.toRat_scale2, Dyadic.toRat_add]
  norm_num [div_eq_mul_inv]

/-- The lower endpoint is at most the exact midpoint. -/
theorem lo_le_midpoint (I : IntervalDyadic) : I.lo.toRat ≤ I.midpoint.toRat := by
  rw [midpoint_toRat]
  linarith [I.le]

/-- The exact midpoint is at most the upper endpoint. -/
theorem midpoint_le_hi (I : IntervalDyadic) : I.midpoint.toRat ≤ I.hi.toRat := by
  rw [midpoint_toRat]
  linarith [I.le]

/-- Split a dyadic interval into two exact closed halves. -/
def bisect (I : IntervalDyadic) : IntervalDyadic × IntervalDyadic :=
  (⟨I.lo, I.midpoint, I.lo_le_midpoint⟩,
   ⟨I.midpoint, I.hi, I.midpoint_le_hi⟩)

/-- A point in the original interval and left of the midpoint is in the left half. -/
theorem mem_bisect_left {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hm : x ≤ (I.midpoint.toRat : ℝ)) : x ∈ (I.bisect).1 := by
  exact ⟨hx.1, hm⟩

/-- A point in the original interval and right of the midpoint is in the right half. -/
theorem mem_bisect_right {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hm : (I.midpoint.toRat : ℝ) ≤ x) : x ∈ (I.bisect).2 := by
  exact ⟨hm, hx.2⟩

/-- Membership in the left half implies membership in the original interval. -/
theorem mem_of_mem_bisect_left {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ (I.bisect).1) : x ∈ I := by
  refine ⟨hx.1, hx.2.trans ?_⟩
  exact_mod_cast I.midpoint_le_hi

/-- Membership in the right half implies membership in the original interval. -/
theorem mem_of_mem_bisect_right {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ (I.bisect).2) : x ∈ I := by
  refine ⟨?_, hx.2⟩
  exact (by exact_mod_cast I.lo_le_midpoint : (I.lo.toRat : ℝ) ≤ I.midpoint.toRat) |>.trans hx.1

/-- The two closed halves cover the original interval, including their shared seam. -/
theorem mem_bisect_or {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    x ∈ (I.bisect).1 ∨ x ∈ (I.bisect).2 := by
  by_cases hm : x ≤ (I.midpoint.toRat : ℝ)
  · exact Or.inl (mem_bisect_left hx hm)
  · exact Or.inr (mem_bisect_right hx (le_of_lt (not_le.mp hm)))

/-- Both closed halves contain the midpoint seam. -/
theorem midpoint_mem_bisect_both (I : IntervalDyadic) :
    (I.midpoint.toRat : ℝ) ∈ (I.bisect).1 ∧
      (I.midpoint.toRat : ℝ) ∈ (I.bisect).2 := by
  constructor
  · exact ⟨by exact_mod_cast I.lo_le_midpoint, le_rfl⟩
  · exact ⟨le_rfl, by exact_mod_cast I.midpoint_le_hi⟩

/-- The overlap of the two closed children is exactly their midpoint seam. -/
theorem bisect_intersection (I : IntervalDyadic) :
    I.bisect.1.toSet ∩ I.bisect.2.toSet = {I.midpoint.toReal} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hx' :
        ((I.lo.toRat : ℝ) ≤ x ∧ x ≤ (I.midpoint.toRat : ℝ)) ∧
          ((I.midpoint.toRat : ℝ) ≤ x ∧ x ≤ (I.hi.toRat : ℝ)) := by
      simpa [toSet, bisect, Dyadic.toReal] using hx
    exact le_antisymm hx'.1.2 hx'.2.1
  · rintro rfl
    simpa [toSet, bisect, Dyadic.toReal] using I.midpoint_mem_bisect_both

/-- The left child has exactly half the semantic width of its parent. -/
theorem bisect_left_width_toRat (I : IntervalDyadic) :
    I.bisect.1.width.toRat = I.width.toRat / 2 := by
  simp only [width_toRat, bisect, midpoint_toRat]
  ring

/-- The right child has exactly half the semantic width of its parent. -/
theorem bisect_right_width_toRat (I : IntervalDyadic) :
    I.bisect.2.width.toRat = I.width.toRat / 2 := by
  simp only [width_toRat, bisect, midpoint_toRat]
  ring

/-! ### Outward Rounding -/

/-- Outward rounding: enforces a maximum precision (minimum exponent).

This is the key operation for preventing precision explosion.
`minExp` is the minimum allowed exponent (higher = coarser precision).

For example, `minExp = -10` ensures all values are multiples of 2^(-10) ≈ 0.001.
-/
def roundOut (I : IntervalDyadic) (minExp : Int) : IntervalDyadic :=
  let newLo := I.lo.shiftDown minExp
  let newHi := I.hi.shiftUp minExp
  ⟨newLo, newHi, by
    -- Proof: newLo ≤ I.lo ≤ I.hi ≤ newHi
    have h1 : newLo.toRat ≤ I.lo.toRat := Dyadic.toRat_shiftDown_le I.lo minExp
    have h2 : I.lo.toRat ≤ I.hi.toRat := I.le
    have h3 : I.hi.toRat ≤ newHi.toRat := Dyadic.toRat_shiftUp_ge I.hi minExp
    linarith⟩

/-- roundOut produces an interval containing the original -/
theorem roundOut_contains {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (minExp : Int) :
    x ∈ I.roundOut minExp := by
  simp only [mem_def] at *
  constructor
  · have h := Dyadic.toRat_shiftDown_le I.lo minExp
    have h' : ((I.lo.shiftDown minExp).toRat : ℝ) ≤ (I.lo.toRat : ℝ) := by exact_mod_cast h
    calc ((I.roundOut minExp).lo.toRat : ℝ) = ((I.lo.shiftDown minExp).toRat : ℝ) := by rfl
      _ ≤ (I.lo.toRat : ℝ) := h'
      _ ≤ x := hx.1
  · have h := Dyadic.toRat_shiftUp_ge I.hi minExp
    have h' : (I.hi.toRat : ℝ) ≤ ((I.hi.shiftUp minExp).toRat : ℝ) := by exact_mod_cast h
    calc x ≤ (I.hi.toRat : ℝ) := hx.2
      _ ≤ ((I.hi.shiftUp minExp).toRat : ℝ) := h'
      _ = ((I.roundOut minExp).hi.toRat : ℝ) := by rfl

/-! ### Interval Negation -/

/-- Negate an interval -/
def neg (I : IntervalDyadic) : IntervalDyadic where
  lo := I.hi.neg
  hi := I.lo.neg
  le := by
    simp only [Dyadic.toRat_neg]
    linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg, Dyadic.toRat_neg, Rat.cast_neg]
  constructor <;> linarith

/-! ### Interval Addition -/

/-- Add two intervals -/
def add (I J : IntervalDyadic) : IntervalDyadic where
  lo := I.lo.add J.lo
  hi := I.hi.add J.hi
  le := by
    simp only [Dyadic.toRat_add]
    linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add, Dyadic.toRat_add, Rat.cast_add]
  constructor <;> linarith

/-- Add with precision control -/
def addRounded (I J : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  (add I J).roundOut prec

/-! ### Interval Subtraction -/

/-- Subtract two intervals -/
def sub (I J : IntervalDyadic) : IntervalDyadic := add I (neg J)

/-- FTIA for subtraction -/
theorem mem_sub {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x - y ∈ sub I J := by
  simp only [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

/-! ### Interval Multiplication -/

/-- Multiply two intervals.

Uses min/max of all four endpoint products to handle signs correctly.
This is the exact multiplication - mantissas may grow. Use `mulRounded` or
`mulNormalized` for controlled precision.

Correctness: For x ∈ [a,b] and y ∈ [c,d], the product x*y lies in the interval
[min(ac,ad,bc,bd), max(ac,ad,bc,bd)]. -/
def mul (I J : IntervalDyadic) : IntervalDyadic :=
  let v1 := I.lo.mul J.lo
  let v2 := I.lo.mul J.hi
  let v3 := I.hi.mul J.lo
  let v4 := I.hi.mul J.hi
  ⟨Dyadic.min4 v1 v2 v3 v4, Dyadic.max4 v1 v2 v3 v4, Dyadic.min4_le_max4 v1 v2 v3 v4⟩

/-- Fast interval multiplication using sign-based case splitting.
    Reduces from 4 multiplications + 12 comparisons to 2 multiplications
    in the common case (both intervals positive or both negative).
    Falls back to the full 4-way product for mixed-sign intervals. -/
def mulFast (I J : IntervalDyadic) : IntervalDyadic :=
  if hI : Dyadic.le 0 I.lo then
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.lo, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.lo, I.lo.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      ⟨I.hi.mul J.lo, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 I.lo).mp hI
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
  else if hI2 : Dyadic.le I.hi 0 then
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.hi, I.hi.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.hi, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      ⟨I.lo.mul J.hi, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le I.hi 0).mp hI2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
  else
    if hJ : Dyadic.le 0 J.lo then
      ⟨I.lo.mul J.hi, I.hi.mul J.hi, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le 0 J.lo).mp hJ
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else if hJ2 : Dyadic.le J.hi 0 then
      ⟨I.hi.mul J.lo, I.lo.mul J.lo, by
        simp only [Dyadic.toRat_mul]
        have := (Dyadic.le_iff_toRat_le J.hi 0).mp hJ2
        simp only [Dyadic.toRat_zero] at *
        nlinarith [I.le, J.le]⟩
    else
      mul I J

/- We intentionally do not attach `mulFast` as a native replacement here.
   Native certificate checking should execute the same definition that the
   kernel proofs reason about. Keep `mulFast` available only as an internal
   candidate for future explicitly-audited runtime backends. -/

/-- FTIA for multiplication -/
theorem mem_mul {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mul I J := by
  -- Use IntervalRat.mem_mul and translate the bounds
  have hxI := mem_toIntervalRat.mp hx
  have hyJ := mem_toIntervalRat.mp hy
  have hmul := IntervalRat.mem_mul hxI hyJ
  simp only [mem_def, mul] at *
  -- hmul has bounds from IntervalRat.mul which are min/max of 4 products
  -- Our Dyadic.min4/max4 has the same structure with toRat preserving the products
  constructor
  · -- Lower bound: Dyadic.min4.toRat equals the rational min4 from hmul
    simp only [IntervalRat.mem_def, IntervalRat.mul, toIntervalRat] at hmul
    have heq : (Dyadic.min4 (I.lo.mul J.lo) (I.lo.mul J.hi) (I.hi.mul J.lo) (I.hi.mul J.hi)).toRat
        = min (min (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat))
              (min (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat)) := by
      simp only [Dyadic.min4, Dyadic.toRat_mul, Dyadic.min_toRat]
    rw [heq]
    exact_mod_cast hmul.1
  · -- Upper bound: Dyadic.max4.toRat equals the rational max4 from hmul
    simp only [IntervalRat.mem_def, IntervalRat.mul, toIntervalRat] at hmul
    have heq : (Dyadic.max4 (I.lo.mul J.lo) (I.lo.mul J.hi) (I.hi.mul J.lo) (I.hi.mul J.hi)).toRat
        = max (max (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat))
              (max (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat)) := by
      simp only [Dyadic.max4, Dyadic.toRat_mul, Dyadic.max_toRat]
    rw [heq]
    exact_mod_cast hmul.2

/-- Dyadic.min4 converts to rational min4 -/
private theorem min4_toRat (a b c d : Dyadic) :
    (Dyadic.min4 a b c d).toRat = IntervalRat.min4 a.toRat b.toRat c.toRat d.toRat := by
  simp only [Dyadic.min4, IntervalRat.min4, Dyadic.min_toRat]

/-- Dyadic.max4 converts to rational max4 -/
private theorem max4_toRat (a b c d : Dyadic) :
    (Dyadic.max4 a b c d).toRat = IntervalRat.max4 a.toRat b.toRat c.toRat d.toRat := by
  simp only [Dyadic.max4, IntervalRat.max4, Dyadic.max_toRat]

/-- Extract 0 ≤ toRat from Dyadic.le 0 d -/
private theorem toRat_nonneg_of_le {d : Dyadic} (h : Dyadic.le 0 d) : 0 ≤ d.toRat := by
  have := (Dyadic.le_iff_toRat_le 0 d).mp h; rwa [Dyadic.toRat_zero] at this

/-- Extract toRat ≤ 0 from Dyadic.le d 0 -/
private theorem toRat_nonpos_of_le {d : Dyadic} (h : Dyadic.le d 0) : d.toRat ≤ 0 := by
  have := (Dyadic.le_iff_toRat_le d 0).mp h; rwa [Dyadic.toRat_zero] at this

/-- Extract toRat < 0 from ¬ Dyadic.le 0 d -/
private theorem toRat_neg_of_not_le {d : Dyadic} (h : ¬ Dyadic.le 0 d) : d.toRat < 0 := by
  exact lt_of_not_ge fun h' => h ((Dyadic.le_iff_toRat_le 0 d).mpr (by rwa [Dyadic.toRat_zero]))

/-- Extract 0 < toRat from ¬ Dyadic.le d 0 -/
private theorem toRat_pos_of_not_le {d : Dyadic} (h : ¬ Dyadic.le d 0) : 0 < d.toRat := by
  exact lt_of_not_ge fun h' => h ((Dyadic.le_iff_toRat_le d 0).mpr (by rwa [Dyadic.toRat_zero]))

/-- mulFast endpoints match mul endpoints: lo -/
private theorem mulFast_lo (I J : IntervalDyadic) : (mulFast I J).lo.toRat = (mul I J).lo.toRat :=
  by
  have hrhs : (mul I J).lo.toRat = IntervalRat.min4
      (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat)
      (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat) := by
    simp only [mul, Dyadic.toRat_mul, min4_toRat]
  rw [hrhs]; unfold mulFast
  split
  · rename_i hI
    have hIlo := toRat_nonneg_of_le hI
    split
    · rename_i hJ
      have hJlo := toRat_nonneg_of_le hJ
      simp only [Dyadic.toRat_mul]
      exact IntervalRat.eq_min4_of_le (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · rename_i _ hJ2
        have hJhi := toRat_nonpos_of_le hJ2
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · rename_i hJ hJ2
        have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
        have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · rename_i _ hI2
      have hIhi := toRat_nonpos_of_le hI2
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_min4_of_le4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rename_i hJ hJ2
          have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
          have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · rename_i hI hI2
      have hIlo := le_of_lt (toRat_neg_of_not_le hI)
      have hIhi := le_of_lt (toRat_pos_of_not_le hI2)
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_min4_of_le2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_min4_of_le3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact hrhs

/-- mulFast endpoints match mul endpoints: hi -/
private theorem mulFast_hi (I J : IntervalDyadic) : (mulFast I J).hi.toRat = (mul I J).hi.toRat :=
  by
  have hrhs : (mul I J).hi.toRat = IntervalRat.max4
      (I.lo.toRat * J.lo.toRat) (I.lo.toRat * J.hi.toRat)
      (I.hi.toRat * J.lo.toRat) (I.hi.toRat * J.hi.toRat) := by
    simp only [mul, Dyadic.toRat_mul, max4_toRat]
  rw [hrhs]; unfold mulFast
  split
  · rename_i hI
    have hIlo := toRat_nonneg_of_le hI
    split
    · rename_i hJ
      have hJlo := toRat_nonneg_of_le hJ
      simp only [Dyadic.toRat_mul]
      exact IntervalRat.eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
        (by nlinarith [I.le, J.le])
    · split
      · rename_i _ hJ2
        have hJhi := toRat_nonpos_of_le hJ2
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge2 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · rename_i hJ hJ2
        have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
        have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
  · split
    · rename_i _ hI2
      have hIhi := toRat_nonpos_of_le hI2
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge3 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · rename_i hJ hJ2
          have hJlo := le_of_lt (toRat_neg_of_not_le hJ)
          have hJhi := le_of_lt (toRat_pos_of_not_le hJ2)
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
    · rename_i hI hI2
      have hIlo := le_of_lt (toRat_neg_of_not_le hI)
      have hIhi := le_of_lt (toRat_pos_of_not_le hI2)
      split
      · rename_i hJ
        have hJlo := toRat_nonneg_of_le hJ
        simp only [Dyadic.toRat_mul]
        exact IntervalRat.eq_max4_of_ge4 (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
          (by nlinarith [I.le, J.le])
      · split
        · rename_i _ hJ2
          have hJhi := toRat_nonpos_of_le hJ2
          simp only [Dyadic.toRat_mul]
          exact IntervalRat.eq_max4_of_ge (by nlinarith [I.le, J.le]) (by nlinarith [I.le, J.le])
            (by nlinarith [I.le, J.le])
        · exact hrhs

/-- `mulFast` preserves the containment property of `mul`.
    This is retained as documentation and a future audited optimization hook;
    production certificate checking currently uses `mul` directly. -/
theorem mem_mulFast {x y : ℝ} {I J : IntervalDyadic} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mulFast I J := by
  simp only [mem_def]
  constructor
  · rw [mulFast_lo]; exact (mem_mul hx hy).1
  · rw [mulFast_hi]; exact (mem_mul hx hy).2

/-- Multiply with precision control (outward rounding) -/
def mulRounded (I J : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  (mul I J).roundOut prec

/-- Multiply with mantissa normalization (prevents bit explosion) -/
def mulNormalized (I J : IntervalDyadic) (maxBits : Nat := 256) : IntervalDyadic :=
  let result := mul I J
  ⟨result.lo.normalizeDown maxBits, result.hi.normalizeUp maxBits, by
    -- Normalization preserves ordering: lo.normalizeDown ≤ lo ≤ hi ≤ hi.normalizeUp
    calc (result.lo.normalizeDown maxBits).toRat
        ≤ result.lo.toRat := Dyadic.toRat_normalizeDown_le _ _
      _ ≤ result.hi.toRat := result.le
      _ ≤ (result.hi.normalizeUp maxBits).toRat := Dyadic.toRat_normalizeUp_ge _ _⟩

/-! ### Interval Scaling -/

/-- Scale an interval by a constant Dyadic -/
def scale (I : IntervalDyadic) (c : Dyadic) : IntervalDyadic :=
  if hc : Dyadic.le Dyadic.zero c then
    ⟨I.lo.mul c, I.hi.mul c, by
      rw [Dyadic.toRat_mul, Dyadic.toRat_mul]
      have hcnn : 0 ≤ c.toRat := by
        have := Dyadic.le_iff_toRat_le Dyadic.zero c |>.mp hc
        have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
        rw [hz] at this; exact this
      exact mul_le_mul_of_nonneg_right I.le hcnn⟩
  else
    ⟨I.hi.mul c, I.lo.mul c, by
      rw [Dyadic.toRat_mul, Dyadic.toRat_mul]
      have hcneg : c.toRat < 0 := by
        have hf := Dyadic.le_iff_toRat_le Dyadic.zero c
        have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
        rw [hz] at hf
        by_contra! hge
        exact hc (hf.mpr hge)
      exact mul_le_mul_of_nonpos_right I.le (le_of_lt hcneg)⟩

/-- Scale by a power of 2 (very efficient: just adjusts exponents) -/
def scale2 (I : IntervalDyadic) (n : Int) : IntervalDyadic :=
  ⟨I.lo.scale2 n, I.hi.scale2 n, Dyadic.toRat_scale2_le_scale2 I.lo I.hi n I.le⟩

/-! ### Square Root -/

/-- Square root of an interval.
    Returns a conservative bound [0, max(hi, 1)].
    This is sound because:
    - sqrt(x) = 0 for x < 0 (by definition in Mathlib)
    - sqrt(x) ≥ 0 for all x
    - sqrt(x) ≤ max(x, 1) for x ≥ 0
    Therefore for any x ∈ [lo, hi], sqrt(x) ∈ [0, max(hi, 1)]. -/
def sqrt (I : IntervalDyadic) (_prec : Int := -53) : IntervalDyadic :=
  -- Conservative bound: [0, max(hi, 1)]
  -- sqrt(x) ≥ 0 for all x (including negative where sqrt returns 0)
  -- sqrt(x) ≤ max(x, 1) for x ≥ 0
  -- sqrt(x) = 0 ≤ max(hi, 1) for x < 0
  let one := Dyadic.ofInt 1
  let hi_bound := Dyadic.max I.hi one
  ⟨Dyadic.zero, hi_bound, by
    have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
    rw [Dyadic.max_toRat, Dyadic.toRat_ofInt, hz]
    exact le_max_of_le_right (by norm_num : (0 : ℚ) ≤ 1)⟩

/-- sqrt(x) ≤ max(x, 1) for all x ≥ 0 -/
private theorem sqrt_le_max_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ max x 1 := by
  by_cases! h : x ≤ 1
  · -- Case x ≤ 1: sqrt(x) ≤ 1 ≤ max(x, 1)
    -- sqrt(x) ≤ 1 when x ≤ 1 because sqrt(x)^2 = x ≤ 1 and sqrt(x) ≥ 0
    have hsqrt_le_one : Real.sqrt x ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h
    calc Real.sqrt x ≤ 1 := hsqrt_le_one
      _ ≤ max x 1 := le_max_right x 1
  · -- Case x > 1: sqrt(x) ≤ x = max(x, 1)
    -- sqrt(x) ≤ x for x ≥ 1 follows from sqrt(x) * sqrt(x) = x and sqrt(x) ≥ 1
    have h1 : 1 ≤ Real.sqrt x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (le_of_lt h)
    have hsqrt_le_x : Real.sqrt x ≤ x := by
      calc Real.sqrt x = Real.sqrt x * 1 := by ring
        _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
        _ = x := by rw [← sq, Real.sq_sqrt hx]
    calc Real.sqrt x ≤ x := hsqrt_le_x
      _ ≤ max x 1 := le_max_left x 1

/-- Soundness of interval sqrt: if x ∈ I, x ≥ 0, then Real.sqrt x ∈ sqrt I -/
theorem mem_sqrt {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (hx_nn : 0 ≤ x) (prec : Int) :
    Real.sqrt x ∈ sqrt I prec := by
  simp only [sqrt, mem_def, Dyadic.max_toRat, Dyadic.toRat_ofInt]
  have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
  constructor
  · -- Lower bound: 0 ≤ sqrt(x)
    simp only [hz, Rat.cast_zero]
    exact Real.sqrt_nonneg x
  · -- Upper bound: sqrt(x) ≤ max(hi, 1)
    have hhi_ge : x ≤ (I.hi.toRat : ℝ) := hx.2
    calc Real.sqrt x
        ≤ max x 1 := sqrt_le_max_one hx_nn
      _ ≤ max (I.hi.toRat : ℝ) 1 := max_le_max_right 1 hhi_ge
      _ = (↑(max I.hi.toRat 1) : ℝ) := by simp [Rat.cast_max]

/-- General soundness of interval sqrt for any real input.
    Handles both non-negative inputs and negative inputs (where Real.sqrt returns 0). -/
theorem mem_sqrt' {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (prec : Int) :
    Real.sqrt x ∈ sqrt I prec := by
  rcases le_or_gt 0 x with hx_nn | hx_neg
  · -- Non-negative case
    exact mem_sqrt hx hx_nn prec
  · -- Negative case: sqrt(x) = 0 for x < 0
    have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hx_neg)
    simp only [sqrt, mem_def, Dyadic.max_toRat, Dyadic.toRat_ofInt, hsqrt_zero]
    have hz : Dyadic.zero.toRat = 0 := Dyadic.toRat_zero
    simp only [hz, Rat.cast_zero, Rat.cast_max]
    constructor
    · norm_num
    · apply le_max_of_le_right
      norm_num

/-! ### Comparison and Containment -/

/-- Check if interval contains zero -/
def containsZero (I : IntervalDyadic) : Bool :=
  Dyadic.le I.lo Dyadic.zero && Dyadic.le Dyadic.zero I.hi

/-- Check if entire interval is positive -/
def isPositive (I : IntervalDyadic) : Bool :=
  Dyadic.lt Dyadic.zero I.lo

/-- Check if entire interval is negative -/
def isNegative (I : IntervalDyadic) : Bool :=
  Dyadic.lt I.hi Dyadic.zero

/-- Check if I ⊆ J -/
def subset (I J : IntervalDyadic) : Bool :=
  Dyadic.le J.lo I.lo && Dyadic.le I.hi J.hi

/-- Check if the upper bound is ≤ a rational -/
def upperBoundedBy (I : IntervalDyadic) (q : ℚ) : Bool :=
  I.hi.toRat ≤ q

/-- Check if a rational is ≤ the lower bound -/
def lowerBoundedBy (I : IntervalDyadic) (q : ℚ) : Bool :=
  q ≤ I.lo.toRat

/-- Upper bound extraction from membership -/
theorem le_hi_of_mem {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    x ≤ (I.hi.toRat : ℝ) := hx.2

/-- Lower bound extraction from membership -/
theorem lo_le_of_mem {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    (I.lo.toRat : ℝ) ≤ x := hx.1

/-- What upperBoundedBy means: the interval's hi endpoint is ≤ q -/
theorem upperBoundedBy_spec {I : IntervalDyadic} {q : ℚ}
    (h : I.upperBoundedBy q = true) : (I.hi.toRat : ℝ) ≤ q := by
  simp only [upperBoundedBy, decide_eq_true_eq] at h
  exact_mod_cast h

/-- What lowerBoundedBy means: q is ≤ the interval's lo endpoint -/
theorem lowerBoundedBy_spec {I : IntervalDyadic} {q : ℚ}
    (h : I.lowerBoundedBy q = true) : (q : ℝ) ≤ I.lo.toRat := by
  simp only [lowerBoundedBy, decide_eq_true_eq] at h
  exact_mod_cast h

/-! ### Helper for Transcendentals -/

/-- Convert from IntervalRat (for transcendental results) -/
def ofIntervalRat (I : IntervalRat) (prec : Int := -53) : IntervalDyadic :=
  -- Convert Rat endpoints to Dyadic with outward rounding
  -- For simplicity, we use a conservative conversion
  let lo := Dyadic.ofInt (Int.floor (I.lo * (2 ^ (-prec).toNat)))
  let loD := lo.scale2 prec
  let hi := Dyadic.ofInt (Int.ceil (I.hi * (2 ^ (-prec).toNat)))
  let hiD := hi.scale2 prec
  ⟨loD, hiD, by
    -- Need: loD.toRat ≤ hiD.toRat
    -- loD.toRat = floor(I.lo * 2^n) * 2^prec
    -- hiD.toRat = ceil(I.hi * 2^n) * 2^prec
    -- This follows from: floor(I.lo * 2^n) ≤ ceil(I.hi * 2^n)
    -- Which is: floor(I.lo * 2^n) ≤ I.lo * 2^n ≤ I.hi * 2^n ≤ ceil(I.hi * 2^n)
    apply Dyadic.toRat_scale2_le_scale2
    rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    have hle : I.lo ≤ I.hi := I.le
    have hscale_pos : (0 : ℚ) < (2 : ℚ) ^ (-prec).toNat := pow_pos (by norm_num : (0 : ℚ) < 2) _
    calc (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ)
        ≤ I.lo * (2 : ℚ) ^ (-prec).toNat := Int.floor_le _
      _ ≤ I.hi * (2 : ℚ) ^ (-prec).toNat := mul_le_mul_of_nonneg_right hle (le_of_lt hscale_pos)
      _ ≤ ⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ := Int.le_ceil _⟩

/-- If x ∈ IntervalRat I, then x ∈ ofIntervalRat I prec (outward rounding preserves membership).
    Requires precision ≤ 0 (e.g. -53). -/
theorem mem_ofIntervalRat {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (prec : Int)
    (hprec : prec ≤ 0 := by norm_num) :
    x ∈ ofIntervalRat I prec := by
  -- The conversion uses floor/ceil which provides outward rounding:
  -- floor(lo * 2^n) * 2^(-n) ≤ lo ≤ x ≤ hi ≤ ceil(hi * 2^n) * 2^(-n)
  -- This follows from floor(a) ≤ a and a ≤ ceil(a), combined with
  -- the fact that multiplying by 2^(-n) when prec = -n cancels the 2^n factor.
  simp only [mem_def, ofIntervalRat, IntervalRat.mem_def] at *
  have h2n_pos : (0 : ℚ) < (2 : ℚ) ^ (-prec).toNat := pow_pos (by norm_num) _
  have hfloor : (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) ≤ I.lo * (2 : ℚ) ^ (-prec).toNat :=
    Int.floor_le _
  have hceil : I.hi * (2 : ℚ) ^ (-prec).toNat ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) :=
    Int.le_ceil _
  have hzpow_pos : (0 : ℚ) < (2 : ℚ) ^ prec := zpow_pos (by norm_num) _
  -- Key: 2^(-prec).toNat * 2^prec = 1 when prec ≤ 0 (so (-prec).toNat = -prec)
  have hcancel : (2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec = 1 := by
    set n := (-prec).toNat with hn_def
    have hprec_eq : prec = -(n : ℤ) := by omega
    rw [hprec_eq, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (ne_of_gt h2n_pos)
  constructor
  · -- Lower bound
    rw [Dyadic.toRat_scale2, Dyadic.toRat_ofInt]
    have hle : (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) * (2 : ℚ) ^ prec ≤ I.lo := by
      calc (⌊I.lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) * (2 : ℚ) ^ prec
          ≤ (I.lo * (2 : ℚ) ^ (-prec).toNat) * (2 : ℚ) ^ prec := by
            apply mul_le_mul_of_nonneg_right hfloor (le_of_lt hzpow_pos)
        _ = I.lo * ((2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec) := by ring
        _ = I.lo * 1 := by rw [hcancel]
        _ = I.lo := by ring
    exact le_trans (by exact_mod_cast hle) hx.1
  · -- Upper bound
    rw [Dyadic.toRat_scale2, Dyadic.toRat_ofInt]
    have hle : I.hi ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) * (2 : ℚ) ^ prec := by
      calc I.hi = I.hi * 1 := by ring
        _ = I.hi * ((2 : ℚ) ^ (-prec).toNat * (2 : ℚ) ^ prec) := by rw [hcancel]
        _ = (I.hi * (2 : ℚ) ^ (-prec).toNat) * (2 : ℚ) ^ prec := by ring
        _ ≤ (⌈I.hi * (2 : ℚ) ^ (-prec).toNat⌉ : ℚ) * (2 : ℚ) ^ prec := by
            apply mul_le_mul_of_nonneg_right hceil (le_of_lt hzpow_pos)
    exact le_trans hx.2 (by exact_mod_cast hle)

end IntervalDyadic
end LeanCert.Core
