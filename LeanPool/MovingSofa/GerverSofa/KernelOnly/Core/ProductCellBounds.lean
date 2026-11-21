/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle001

/-!
# Fixed-point checks for the Gerver product cells

Round both path coordinates and the trigonometric factors outward onto a common grid.
The lower bounds of the two interval dot products can then be computed with integer
products. A strictly positive margin for the rounded intervals implies the same
strict bound for the original rational intervals.
-/

@[expose] public section

namespace GerverSofa.PartB.ProductCellBounds

-- Five decimal places leave enough room to certify the original strict bounds.
/-- Number of grid units per rational unit. -/
def scale : ℤ := 100000

private theorem scale_pos : (0 : ℚ) < (scale : ℚ) := by norm_num [scale]

/-- A pair of endpoints measured in units of `1 / scale`. -/
structure GridInterval where
  /-- Lower endpoint in grid units. -/
  lo : ℤ
  /-- Upper endpoint in grid units. -/
  hi : ℤ
  deriving DecidableEq

/-- Interpret the grid endpoints as rational numbers. -/
def GridInterval.toRatInterval (interval : GridInterval) : RatInterval :=
  ⟨(interval.lo : ℚ) / (scale : ℚ), (interval.hi : ℚ) / (scale : ℚ)⟩

/-- Round the lower endpoint down and the upper endpoint strictly up. -/
def roundOutward (interval : RatInterval) : GridInterval :=
  ⟨⌊(scale : ℚ) * interval.lo⌋, ⌊(scale : ℚ) * interval.hi⌋ + 1⟩

/-- Negate an interval measured in grid units. -/
def GridInterval.neg (interval : GridInterval) : GridInterval :=
  ⟨-interval.hi, -interval.lo⟩

/-- Subtract two intervals measured on the same grid. -/
def GridInterval.sub (left right : GridInterval) : GridInterval :=
  ⟨left.lo - right.hi, left.hi - right.lo⟩

private theorem GridInterval.toRatInterval_neg (interval : GridInterval) :
    interval.neg.toRatInterval = interval.toRatInterval.neg := by
  cases interval
  simp only [neg, toRatInterval, RatInterval.neg, Int.cast_neg, neg_div]

private theorem GridInterval.toRatInterval_sub (left right : GridInterval) :
    (left.sub right).toRatInterval = left.toRatInterval.sub right.toRatInterval := by
  cases left
  cases right
  simp only [sub, toRatInterval, RatInterval.sub, RatInterval.add, RatInterval.neg,
    sub_eq_add_neg, Int.cast_add, Int.cast_neg, add_div, neg_div]

/-- Lower endpoint of the product, measured in square grid units. -/
def GridInterval.productLower (left right : GridInterval) : ℤ :=
  min (min (left.lo * right.lo) (left.lo * right.hi))
    (min (left.hi * right.lo) (left.hi * right.hi))

private theorem GridInterval.productLower_eq (left right : GridInterval) :
    (left.productLower right : ℚ) / (scale : ℚ) ^ 2 =
      (left.toRatInterval.mul right.toRatInterval).lo := by
  simp only [productLower, toRatInterval, RatInterval.mul, Int.cast_min, Int.cast_mul,
    div_mul_div_comm, ← pow_two, min_div_div_right (sq_nonneg (scale : ℚ))]

-- Products are measured in square grid units, so no rational arithmetic is needed
-- when evaluating the checker.
/-- Lower endpoint of one plus an interval dot product, in square grid units. -/
def imageLower (dx dy cosine sine : GridInterval) : ℤ :=
  scale ^ 2 + dx.productLower cosine + dy.productLower sine

private theorem imageLower_eq (dx dy cosine sine : GridInterval) :
    (imageLower dx dy cosine sine : ℚ) / (scale : ℚ) ^ 2 =
      ((ExactReplay.oneI.add (dx.toRatInterval.mul cosine.toRatInterval)).add
        (dy.toRatInterval.mul sine.toRatInterval)).lo := by
  delta ExactReplay.oneI RatInterval.point
  simp only [imageLower, Int.cast_add, Int.cast_pow, add_div, GridInterval.productLower_eq,
    RatInterval.add, div_self (pow_ne_zero _ (ne_of_gt scale_pos))]

private structure Covers (outer inner : RatInterval) : Prop where
  lower : outer.lo ≤ inner.lo
  ordered : inner.lo ≤ inner.hi
  upper : inner.hi ≤ outer.hi

private theorem round_covers {interval : RatInterval} (ordered : interval.lo ≤ interval.hi) :
    Covers (roundOutward interval).toRatInterval interval := by
  refine ⟨?_, ordered, ?_⟩
  · exact (div_le_iff₀' scale_pos).2 (Int.floor_le _)
  · apply (le_div_iff₀' scale_pos).2
    change (scale : ℚ) * interval.hi ≤ ((⌊(scale : ℚ) * interval.hi⌋ + 1 : ℤ) : ℚ)
    push_cast
    exact (Int.lt_floor_add_one _).le

private theorem neg_covers {outer inner : RatInterval} (covered : Covers outer inner) :
    Covers outer.neg inner.neg :=
  ⟨neg_le_neg covered.upper, neg_le_neg covered.ordered, neg_le_neg covered.lower⟩

private theorem sub_covers {ox oy x y : RatInterval} (hx : Covers ox x) (hy : Covers oy y) :
    Covers (ox.sub oy) (x.sub y) :=
  ⟨add_le_add hx.lower (neg_le_neg hy.upper),
    add_le_add hx.ordered (neg_le_neg hy.ordered),
    add_le_add hx.upper (neg_le_neg hy.lower)⟩

private theorem endpoint_bounds {outer inner : RatInterval} (covered : Covers outer inner) :
    outer.Contains (inner.lo : ℝ) ∧ outer.Contains (inner.hi : ℝ) := by
  have lo := covered.lower
  have hi := covered.upper
  have ordered := covered.ordered
  exact ⟨⟨by exact_mod_cast lo, by exact_mod_cast ordered.trans hi⟩,
    ⟨by exact_mod_cast lo.trans ordered, by exact_mod_cast hi⟩⟩

private theorem mul_lo_le {ox oy x y : RatInterval} (hx : Covers ox x) (hy : Covers oy y) :
    (ox.mul oy).lo ≤ (x.mul y).lo := by
  have ⟨xl, xh⟩ := endpoint_bounds hx
  have ⟨yl, yh⟩ := endpoint_bounds hy
  simp only [RatInterval.mul, le_min_iff]
  exact ⟨⟨by exact_mod_cast (RatInterval.contains_mul xl yl).1,
      by exact_mod_cast (RatInterval.contains_mul xl yh).1⟩,
    ⟨by exact_mod_cast (RatInterval.contains_mul xh yl).1,
      by exact_mod_cast (RatInterval.contains_mul xh yh).1⟩⟩

/-- Rational interval expression for the first product-cell bound. -/
def imageU (first second : RatInterval × RatInterval) (cosine sine : RatInterval) :
    RatInterval :=
  (ExactReplay.oneI.add ((first.1.sub second.1).mul cosine)).add
    ((first.2.sub second.2).mul sine)

/-- Rational interval expression for the second product-cell bound. -/
def imageV (first second : RatInterval × RatInterval) (cosine sine : RatInterval) :
    RatInterval :=
  (ExactReplay.oneI.add ((first.1.sub second.1).mul sine.neg)).add
    ((first.2.sub second.2).mul cosine)

/-- Check both product-cell bounds on the supplied grid intervals. -/
def passes (threshold : ℤ) (first second : GridInterval × GridInterval)
    (cosine sine : GridInterval) : Bool :=
  let dx := first.1.sub second.1
  let dy := first.2.sub second.2
  decide (threshold < imageLower dx dy cosine sine ∧
    threshold < imageLower dx dy sine.neg cosine)

/-- The rounded check implies the lower bounds for the original interval arithmetic. -/
theorem sound {threshold : ℚ} {scaledThreshold : ℤ} {first second : RatInterval × RatInterval}
    {cosine sine : RatInterval}
    (firstOrdered : first.1.lo ≤ first.1.hi ∧ first.2.lo ≤ first.2.hi)
    (secondOrdered : second.1.lo ≤ second.1.hi ∧ second.2.lo ≤ second.2.hi)
    (cosineOrdered : cosine.lo ≤ cosine.hi) (sineOrdered : sine.lo ≤ sine.hi)
    (threshold_eq : (scaledThreshold : ℚ) / (scale : ℚ) ^ 2 = threshold)
    (checked : passes scaledThreshold (roundOutward first.1, roundOutward first.2)
      (roundOutward second.1, roundOutward second.2) (roundOutward cosine)
      (roundOutward sine) = true) :
    threshold < (imageU first second cosine sine).lo ∧
      threshold < (imageV first second cosine sine).lo := by
  have xCovered := sub_covers (round_covers firstOrdered.1) (round_covers secondOrdered.1)
  have yCovered := sub_covers (round_covers firstOrdered.2) (round_covers secondOrdered.2)
  have cosCovered := round_covers cosineOrdered
  have sinCovered := round_covers sineOrdered
  simp only [passes, decide_eq_true_eq] at checked
  have lowerBound {numerator : ℤ} (bound : scaledThreshold < numerator) :
      threshold < (numerator : ℚ) / (scale : ℚ) ^ 2 := by
    rw [← threshold_eq]
    exact div_lt_div_of_pos_right (by exact_mod_cast bound) (pow_pos scale_pos _)
  have lowerU := lowerBound checked.1
  have lowerV := lowerBound checked.2
  simp only [imageLower_eq, GridInterval.toRatInterval_sub] at lowerU
  simp only [imageLower_eq, GridInterval.toRatInterval_sub,
    GridInterval.toRatInterval_neg] at lowerV
  have uBound :
      (imageU ((roundOutward first.1).toRatInterval, (roundOutward first.2).toRatInterval)
        ((roundOutward second.1).toRatInterval, (roundOutward second.2).toRatInterval)
        (roundOutward cosine).toRatInterval (roundOutward sine).toRatInterval).lo ≤
      (imageU first second cosine sine).lo := by
    exact add_le_add (add_le_add_right (mul_lo_le xCovered cosCovered) ExactReplay.oneI.lo)
      (mul_lo_le yCovered sinCovered)
  have vBound :
      (imageV ((roundOutward first.1).toRatInterval, (roundOutward first.2).toRatInterval)
        ((roundOutward second.1).toRatInterval, (roundOutward second.2).toRatInterval)
        (roundOutward cosine).toRatInterval (roundOutward sine).toRatInterval).lo ≤
      (imageV first second cosine sine).lo := by
    exact add_le_add (add_le_add_right (mul_lo_le xCovered (neg_covers sinCovered))
      ExactReplay.oneI.lo) (mul_lo_le yCovered cosCovered)
  exact ⟨lowerU.trans_le uBound, lowerV.trans_le vBound⟩

end GerverSofa.PartB.ProductCellBounds
