/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Basic
public import LeanPool.MovingSofa.LeanCert.Core.Expr
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-!
# Rational Endpoint Intervals - Transcendental Functions

This file provides noncomputable interval bounds for transcendental functions
using floor/ceiling to obtain rational endpoints.

## Main definitions

* `ofRealEndpoints` - Create rational interval from real bounds using floor/ceil
* `expInterval` - Interval bound for exponential
* `logInterval` - Interval bound for logarithm (positive intervals)
* `atanhIntervalComputed` - Interval bound for atanh (intervals in (-1, 1))
* `sqrtInterval` - Interval bound for square root

## Main theorems

* `mem_expInterval` - FTIA for exp
* `mem_logInterval` - FTIA for log
* `mem_atanhIntervalComputed` - FTIA for atanh
* `mem_sqrtInterval` - FTIA for sqrt

## Design notes

All definitions in this file are noncomputable as they use `Real.exp`, `Real.log`,
etc. For computable versions, see `IntervalRat.Taylor`.
-/

/-! ### Rational enclosure of real intervals -/

@[expose] public section

namespace LeanCert.Core

namespace IntervalRat

/-- Coarse rational enclosure of a real interval using floor/ceil.
    Given a real interval [lo, hi], returns a rational interval [⌊lo⌋, ⌈hi⌉]
    that is guaranteed to contain all points in the original interval. -/
noncomputable def ofRealEndpoints (lo hi : ℝ) (hle : lo ≤ hi) : IntervalRat where
  lo := ⌊lo⌋
  hi := ⌈hi⌉
  le := by
    have h1 : (⌊lo⌋ : ℝ) ≤ lo := Int.floor_le lo
    have h2 : hi ≤ (⌈hi⌉ : ℝ) := Int.le_ceil hi
    have h3 : (⌊lo⌋ : ℝ) ≤ (⌈hi⌉ : ℝ) := le_trans h1 (le_trans hle h2)
    exact_mod_cast h3

/-- Any point in [lo, hi] is in the rational enclosure [⌊lo⌋, ⌈hi⌉] -/
theorem mem_ofRealEndpoints {x lo hi : ℝ} (hle : lo ≤ hi) (hx : lo ≤ x ∧ x ≤ hi) :
    x ∈ ofRealEndpoints lo hi hle := by
  simp only [mem_def, ofRealEndpoints]
  constructor
  · have h := Int.floor_le lo
    exact le_trans h hx.1
  · have h := Int.le_ceil hi
    exact le_trans hx.2 h

/-! ### Exponential interval -/

/-- Interval bound for exp on rational intervals.
    Since exp is strictly increasing, exp([a,b]) ⊆ [⌊exp(a)⌋, ⌈exp(b)⌉].
    This uses Real.exp and floor/ceil to get rational bounds. -/
noncomputable def expInterval (I : IntervalRat) : IntervalRat :=
  ofRealEndpoints (Real.exp I.lo) (Real.exp I.hi)
    (Real.exp_le_exp.mpr (by exact_mod_cast I.le))

/-- FTIA for exp: if x ∈ I, then exp(x) ∈ expInterval(I) -/
theorem mem_expInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.exp x ∈ expInterval I := by
  simp only [expInterval]
  apply mem_ofRealEndpoints
  simp only [mem_def] at hx
  constructor
  · exact Real.exp_le_exp.mpr hx.1
  · exact Real.exp_le_exp.mpr hx.2

/-! ### Positive interval check -/

/-- Check if an interval is strictly positive (lo > 0) -/
def isPositive (I : IntervalRat) : Prop := 0 < I.lo

/-- Decidable isPositive -/
instance (I : IntervalRat) : Decidable (isPositive I) :=
  inferInstanceAs (Decidable (0 < I.lo))

/-- An interval that is guaranteed to be strictly positive -/
structure IntervalRatPos extends IntervalRat where
  lo_pos : 0 < toIntervalRat.lo

/-! ### Logarithm interval (for positive intervals) -/

/-- Interval bound for log on positive rational intervals.
    Since log is strictly increasing on (0, ∞), log([a,b]) ⊆ [⌊log(a)⌋, ⌈log(b)⌉] for a > 0.
    This uses Real.log and floor/ceil to get rational bounds. -/
noncomputable def logInterval (I : IntervalRatPos) : IntervalRat :=
  ofRealEndpoints (Real.log I.lo) (Real.log I.hi)
    (Real.log_le_log (by exact_mod_cast I.lo_pos) (by exact_mod_cast I.le))

/-- FTIA for log: if x ∈ I with lo > 0, then log(x) ∈ logInterval(I) -/
theorem mem_logInterval {x : ℝ} {I : IntervalRatPos} (hx : x ∈ I.toIntervalRat) :
    Real.log x ∈ logInterval I := by
  simp only [logInterval]
  apply mem_ofRealEndpoints
  simp only [mem_def] at hx
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast I.lo_pos
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
  constructor
  · exact Real.log_le_log hlo_pos hx.1
  · exact Real.log_le_log hx_pos hx.2

/-! ### Atanh interval (for intervals in (-1, 1)) -/

/-- An interval strictly contained in (-1, 1), suitable for atanh -/
structure IntervalRatInUnitBall where
  /-- Lower endpoint of the interval. -/
  lo : ℚ
  /-- Upper endpoint of the interval. -/
  hi : ℚ
  le : lo ≤ hi
  lo_gt : -1 < lo
  hi_lt : hi < 1

/-- Convert to standard interval -/
def IntervalRatInUnitBall.toIntervalRat (I : IntervalRatInUnitBall) : IntervalRat :=
  ⟨I.lo, I.hi, I.le⟩

/-- Membership in the underlying interval -/
instance : Membership ℝ IntervalRatInUnitBall where
  mem I x := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

theorem IntervalRatInUnitBall.mem_def {x : ℝ} {I : IntervalRatInUnitBall} :
    x ∈ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ I.hi := Iff.rfl

/-- Interval bound for atanh on intervals strictly inside (-1, 1).
    Since atanh is strictly increasing on (-1, 1), atanh([a,b]) ⊆ [⌊atanh(a)⌋, ⌈atanh(b)⌉]. -/
noncomputable def atanhIntervalComputed (I : IntervalRatInUnitBall) : IntervalRat :=
  have hlo : (-1 : ℝ) < I.lo := by exact_mod_cast I.lo_gt
  have hhi : (I.hi : ℝ) < 1 := by exact_mod_cast I.hi_lt
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  ofRealEndpoints (Real.atanh I.lo) (Real.atanh I.hi)
    (Real.atanh_mono
      (by rw [abs_lt]; constructor <;> linarith)
      (by rw [abs_lt]; constructor <;> linarith)
      hle)

/-- FTIA for atanh: if x ∈ I and I ⊂ (-1, 1), then atanh(x) ∈ atanhIntervalComputed(I) -/
theorem mem_atanhIntervalComputed {x : ℝ} {I : IntervalRatInUnitBall} (hx : x ∈ I) :
    Real.atanh x ∈ atanhIntervalComputed I := by
  simp only [atanhIntervalComputed]
  apply mem_ofRealEndpoints
  have hlo : (-1 : ℝ) < I.lo := by exact_mod_cast I.lo_gt
  have hhi : (I.hi : ℝ) < 1 := by exact_mod_cast I.hi_lt
  rw [IntervalRatInUnitBall.mem_def] at hx
  have hx_lo : -1 < x := by linarith [hx.1]
  have hx_hi : x < 1 := by linarith [hx.2]
  have habs_lo : |(I.lo : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_hi : |(I.hi : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_x : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  constructor
  · exact Real.atanh_mono habs_lo habs_x hx.1
  · exact Real.atanh_mono habs_x habs_hi hx.2

/-! ### Square Root Interval -/

/-- Integer square root (floor of sqrt).
    Satisfies: `(intSqrtNat n)^2 ≤ n < (intSqrtNat n + 1)^2` -/
def intSqrtNat (n : Nat) : Nat := Nat.sqrt n

/-- Key property of Nat.sqrt: `Nat.sqrt n ^ 2 ≤ n` -/
private theorem nat_sqrt_sq_le (n : Nat) : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n

/-- Key property of Nat.sqrt: `n < (Nat.sqrt n + 1) ^ 2` -/
private theorem nat_lt_succ_sqrt_sq (n : Nat) : n < (Nat.sqrt n + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at h
  rw [sq]
  exact h

/-- Rational lower bound for sqrt.
    For q ≥ 0 with q = num/den, we compute floor(sqrt(num * den)) / den.
    This gives: sqrtRatLower q ≤ sqrt(q).

    The idea: sqrt(num/den) = sqrt(num*den)/den when properly scaled. -/
def sqrtRatLower (q : ℚ) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    -- Compute floor(sqrt(num * den)) / den
    let s := intSqrtNat (num * den)
    (s : ℚ) / den

/-- Rational upper bound for sqrt.
    For q ≥ 0, we compute ceil(sqrt(num * den)) / den.
    This gives: sqrt(q) ≤ sqrtRatUpper q. -/
def sqrtRatUpper (q : ℚ) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    let prod := num * den
    let s := intSqrtNat prod
    -- If s^2 = prod, return s/den; else (s+1)/den
    if s * s = prod then (s : ℚ) / den
    else ((s + 1) : ℚ) / den

/-- Scaling exponent for precise sqrt bounds (2^scaleBits = scaling factor for denominator) -/
def sqrtScaleBits : Nat := 20  -- gives about 6 decimal digits precision

/-- Rational lower bound for sqrt with high precision.
    For q ≥ 0, we scale by 4^k, compute integer sqrt, and scale back by 2^k.
    This gives: sqrtRatLowerPrec q ≤ sqrt(q) with precision ~2^(-k). -/
def sqrtRatLowerPrec (q : ℚ) (scaleBits : Nat := sqrtScaleBits) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    -- Scale up: multiply num by 4^scaleBits = 2^(2*scaleBits)
    let scaledNum := num * (2 ^ (2 * scaleBits))
    -- Compute floor(sqrt(scaledNum * den))
    let s := intSqrtNat (scaledNum * den)
    -- Scale back: divide by den * 2^scaleBits
    (s : ℚ) / (den * 2 ^ scaleBits)

/-- Rational upper bound for sqrt with high precision.
    For q ≥ 0, we scale by 4^k, compute ceil of integer sqrt, and scale back by 2^k.
    This gives: sqrt(q) ≤ sqrtRatUpperPrec q with precision ~2^(-k). -/
def sqrtRatUpperPrec (q : ℚ) (scaleBits : Nat := sqrtScaleBits) : ℚ :=
  if q ≤ 0 then 0
  else
    let num := q.num.natAbs
    let den := q.den
    let scaledNum := num * (2 ^ (2 * scaleBits))
    let prod := scaledNum * den
    let s := intSqrtNat prod
    -- If s^2 = prod (perfect square), use s; else use s+1 (ceiling)
    let result := if s * s = prod then s else s + 1
    (result : ℚ) / (den * 2 ^ scaleBits)

/-- Helper: For non-negative q, q.num = q.num.natAbs -/
private theorem rat_num_of_nonneg {q : ℚ} (hq : 0 ≤ q) : (q.num : ℤ) = q.num.natAbs := by
  exact (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)).symm

/-- Helper: For positive q, num.natAbs > 0 -/
private theorem rat_num_natAbs_pos {q : ℚ} (hq : 0 < q) : 0 < q.num.natAbs := by
  have h := Rat.num_pos.mpr hq
  exact Int.natAbs_pos.mpr (ne_of_gt h)

/-- Soundness of sqrtRatLower: sqrtRatLower q ≤ Real.sqrt q for q ≥ 0 -/
theorem sqrtRatLower_le_sqrt {q : ℚ} (hq : 0 ≤ q) : (sqrtRatLower q : ℝ) ≤ Real.sqrt q := by
  simp only [sqrtRatLower]
  by_cases! hq0 : q ≤ 0
  · -- q = 0
    have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · -- q > 0
    simp only [not_le.mpr hq0, ↓reduceIte]
    -- Key insight: sqrtRatLower returns s/den where s = floor(sqrt(num*den))
    -- We want to show s/den ≤ sqrt(q) = sqrt(num/den)
    -- This follows because s^2 ≤ num*den, so s ≤ sqrt(num*den), hence s/den ≤ sqrt(num*den)/den =
    -- sqrt(num/den)
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hsqrt_den_pos : 0 < Real.sqrt q.den := Real.sqrt_pos.mpr hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    -- s^2 ≤ num * den
    have hsq : (intSqrtNat (q.num.natAbs * q.den))^2 ≤ q.num.natAbs * q.den := nat_sqrt_sq_le _
    -- s ≤ sqrt(num * den)
    have hs_le : (intSqrtNat (q.num.natAbs * q.den) : ℝ) ≤ Real.sqrt (q.num.natAbs * q.den) := by
      have h1 : ((intSqrtNat (q.num.natAbs * q.den) : ℕ) : ℝ) ^ 2 ≤ (q.num.natAbs * q.den : ℕ) := by
        exact_mod_cast hsq
      have h2 := Real.sqrt_sq (Nat.cast_nonneg (intSqrtNat (q.num.natAbs * q.den)))
      calc (intSqrtNat (q.num.natAbs * q.den) : ℝ)
          = Real.sqrt ((intSqrtNat (q.num.natAbs * q.den) : ℝ) ^ 2) := h2.symm
        _ ≤ Real.sqrt ((q.num.natAbs * q.den : ℕ) : ℝ) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt ((q.num.natAbs : ℝ) * q.den) := by rw [Nat.cast_mul]
    -- q = num/den and sqrt(q) = sqrt(num)/sqrt(den) = sqrt(num*den)/den (after scaling)
    have hq_eq : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
      have habs : (q.num : ℤ) = q.num.natAbs := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
      simp only [Int.natAbs_natCast]
    simp only [Rat.cast_div, Rat.cast_natCast]
    rw [hq_eq, Real.sqrt_div hnum_real_nn, div_le_div_iff₀ hden_pos hsqrt_den_pos]
    -- Goal: s * sqrt(den) ≤ sqrt(num) * den
    calc (intSqrtNat (q.num.natAbs * q.den) : ℝ) * Real.sqrt q.den
        ≤ Real.sqrt (q.num.natAbs * q.den) * Real.sqrt q.den := by
            apply mul_le_mul_of_nonneg_right hs_le (le_of_lt hsqrt_den_pos)
      _ = Real.sqrt (q.num.natAbs) * Real.sqrt q.den * Real.sqrt q.den := by
            rw [Real.sqrt_mul hnum_real_nn]
      _ = Real.sqrt (q.num.natAbs) * (Real.sqrt q.den * Real.sqrt q.den) := by ring
      _ = Real.sqrt (q.num.natAbs) * q.den := by rw [Real.mul_self_sqrt hden_nn]

/-- Soundness of sqrtRatUpper: Real.sqrt q ≤ sqrtRatUpper q for q ≥ 0 -/
theorem sqrt_le_sqrtRatUpper {q : ℚ} (hq : 0 ≤ q) : Real.sqrt q ≤ (sqrtRatUpper q : ℝ) := by
  simp only [sqrtRatUpper]
  by_cases! hq0 : q ≤ 0
  · -- q = 0
    have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · -- q > 0
    simp only [not_le.mpr hq0, ↓reduceIte]
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    have hsqrt_den_pos : 0 < Real.sqrt q.den := Real.sqrt_pos.mpr hden_pos
    have hq_eq : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
      have habs : (q.num : ℤ) = q.num.natAbs := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
      simp only [Int.natAbs_natCast]
    set prod := q.num.natAbs * q.den
    set s := intSqrtNat prod
    rw [hq_eq, Real.sqrt_div hnum_real_nn]
    by_cases hperfect : s * s = prod
    · -- Perfect square case: s^2 = num * den, so sqrt(num*den) = s
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast]
      rw [div_le_div_iff₀ hsqrt_den_pos hden_pos]
      -- sqrt(num*den) = s since s^2 = num*den
      have heq_sqrt : Real.sqrt ((q.num.natAbs : ℝ) * q.den) = s := by
        have h : (s : ℝ) ^ 2 = (q.num.natAbs : ℝ) * q.den := by
          calc (s : ℝ) ^ 2 = ((s * s : ℕ) : ℝ) := by push_cast; ring
            _ = (prod : ℝ) := by exact_mod_cast hperfect
            _ = (q.num.natAbs : ℝ) * q.den := by simp only [prod, Nat.cast_mul]
        rw [← h, Real.sqrt_sq (Nat.cast_nonneg s)]
      calc Real.sqrt q.num.natAbs * q.den
          = Real.sqrt q.num.natAbs * (Real.sqrt q.den * Real.sqrt q.den) := by
              rw [Real.mul_self_sqrt hden_nn]
        _ = (Real.sqrt q.num.natAbs * Real.sqrt q.den) * Real.sqrt q.den := by ring
        _ = Real.sqrt ((q.num.natAbs : ℝ) * q.den) * Real.sqrt q.den := by
              rw [Real.sqrt_mul hnum_real_nn]
        _ = (s : ℝ) * Real.sqrt q.den := by rw [heq_sqrt]
        _ ≤ (s : ℝ) * Real.sqrt q.den := le_refl _
    · -- Non-perfect square case: prod < (s+1)^2
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast]
      rw [div_le_div_iff₀ hsqrt_den_pos hden_pos]
      have hlt : prod < (s + 1) ^ 2 := nat_lt_succ_sqrt_sq prod
      have hsqrt_le : Real.sqrt ((q.num.natAbs : ℝ) * q.den) ≤ (s + 1 : ℕ) := by
        have h1 : (q.num.natAbs : ℝ) * q.den < ((s + 1) ^ 2 : ℕ) := by
          calc (q.num.natAbs : ℝ) * q.den = (prod : ℕ) := by simp only [prod, Nat.cast_mul]
            _ < ((s + 1) ^ 2 : ℕ) := by exact_mod_cast hlt
        have h2 : (0 : ℝ) ≤ (s + 1 : ℕ) := Nat.cast_nonneg _
        have h3 : Real.sqrt ((q.num.natAbs : ℝ) * q.den) < Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) :=
          Real.sqrt_lt_sqrt (mul_nonneg hnum_real_nn hden_nn) h1
        have h4 : Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) = (s + 1 : ℕ) := by
          have : (((s + 1) ^ 2 : ℕ) : ℝ) = ((s + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
          rw [this, Real.sqrt_sq h2]
        exact le_of_lt (h3.trans_eq h4)
      have hgoal : Real.sqrt q.num.natAbs * q.den ≤ ((s + 1 : ℕ) : ℝ) * Real.sqrt q.den := by
        calc Real.sqrt q.num.natAbs * q.den
            = Real.sqrt q.num.natAbs * (Real.sqrt q.den * Real.sqrt q.den) := by
                rw [Real.mul_self_sqrt hden_nn]
          _ = (Real.sqrt q.num.natAbs * Real.sqrt q.den) * Real.sqrt q.den := by ring
          _ = Real.sqrt ((q.num.natAbs : ℝ) * q.den) * Real.sqrt q.den := by
                rw [Real.sqrt_mul hnum_real_nn]
          _ ≤ ((s + 1 : ℕ) : ℝ) * Real.sqrt q.den := by
              exact mul_le_mul_of_nonneg_right hsqrt_le (le_of_lt hsqrt_den_pos)
      convert! hgoal using 2
      push_cast
      ring

/-- Square root interval with conservative bounds.
    For a non-negative interval [lo, hi], sqrt is monotone so:
    sqrt([lo, hi]) ⊆ [0, max(hi, 1)]

    The lower bound is 0 (always sound for sqrt).
    The upper bound uses max(hi, 1) which satisfies sqrt(x) ≤ max(x, 1) for x ≥ 0. -/
def sqrtInterval (I : IntervalRat) : IntervalRat :=
  ⟨0, max I.hi 1, le_sup_of_le_right rfl⟩

/-- Improved square root interval with tight lower bounds.
    For a non-negative interval [lo, hi] with lo ≥ 0:
    - Lower bound: sqrtRatLower(lo)
    - Upper bound: sqrtRatUpper(hi)

    For intervals crossing zero, we use 0 as lower bound. -/
def sqrtIntervalTight (I : IntervalRat) : IntervalRat :=
  if h : 0 ≤ I.lo then
    ⟨sqrtRatLower I.lo, max (sqrtRatUpper I.hi) 1,
     by
       simp only [le_max_iff]
       left
       have hlo_le_hi : I.lo ≤ I.hi := I.le
       -- sqrtRatLower I.lo ≤ sqrtRatUpper I.hi
       have h1 : (sqrtRatLower I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLower_le_sqrt h
       have h2 : Real.sqrt I.hi ≤ (sqrtRatUpper I.hi : ℝ) := sqrt_le_sqrtRatUpper (le_trans h
         hlo_le_hi)
       have h3 : Real.sqrt I.lo ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt (by exact_mod_cast hlo_le_hi)
       have h4 : (sqrtRatLower I.lo : ℝ) ≤ (sqrtRatUpper I.hi : ℝ) := le_trans h1 (le_trans h3 h2)
       exact_mod_cast h4⟩
  else
    ⟨0, max (sqrtRatUpper I.hi) 1, le_sup_of_le_right rfl⟩

/-- Soundness of sqrtRatLowerPrec: sqrtRatLowerPrec q k ≤ Real.sqrt q for q ≥ 0 -/
theorem sqrtRatLowerPrec_le_sqrt {q : ℚ} (hq : 0 ≤ q) (k : Nat) :
    (sqrtRatLowerPrec q k : ℝ) ≤ Real.sqrt q := by
  simp only [sqrtRatLowerPrec]
  by_cases! hq0 : q ≤ 0
  · have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · simp only [not_le.mpr hq0, ↓reduceIte]
    -- Setup: let num = q.num.natAbs, den = q.den, scaledNum = num * 4^k
    -- We compute s = floor(sqrt(scaledNum * den)) and return s / (den * 2^k)
    -- Goal: s / (den * 2^k) ≤ sqrt(q) = sqrt(num/den)
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    have h2k_pos : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num : (0 : ℝ) < 2) k
    have h2k_nn : (0 : ℝ) ≤ 2 ^ k := le_of_lt h2k_pos
    have hden2k_pos : (0 : ℝ) < q.den * 2 ^ k := mul_pos hden_pos h2k_pos
    set num := q.num.natAbs
    set den := q.den
    set scaledNum := num * 2 ^ (2 * k)
    set prod := scaledNum * den
    set s := intSqrtNat prod
    -- s^2 ≤ prod, so s ≤ sqrt(prod)
    have hsq : s ^ 2 ≤ prod := nat_sqrt_sq_le prod
    have hs_le_sqrt : (s : ℝ) ≤ Real.sqrt prod := by
      have h1 : (s : ℝ) ^ 2 ≤ prod := by exact_mod_cast hsq
      have h2 := Real.sqrt_sq (Nat.cast_nonneg s)
      calc (s : ℝ) = Real.sqrt ((s : ℝ) ^ 2) := h2.symm
        _ ≤ Real.sqrt prod := Real.sqrt_le_sqrt h1
    -- sqrt(prod) = sqrt(num * 4^k * den) = sqrt(num * den) * 2^k
    have h4k_eq : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by ring
    have hsqrt_prod : Real.sqrt (prod : ℕ) = Real.sqrt (num * den) * 2 ^ k := by
      calc Real.sqrt (prod : ℕ) = Real.sqrt ((scaledNum * den : ℕ) : ℝ) := by simp only [prod]
        _ = Real.sqrt ((num * 2 ^ (2 * k) * den : ℕ) : ℝ) := by simp only [scaledNum]
        _ = Real.sqrt ((num : ℝ) * 2 ^ (2 * k) * den) := by push_cast; ring_nf
        _ = Real.sqrt ((num : ℝ) * den * (2 ^ k) ^ 2) := by rw [h4k_eq]; ring_nf
        _ = Real.sqrt ((num : ℝ) * den) * Real.sqrt ((2 ^ k) ^ 2) := by
            rw [Real.sqrt_mul (mul_nonneg hnum_real_nn hden_nn)]
        _ = Real.sqrt ((num : ℝ) * den) * 2 ^ k := by rw [Real.sqrt_sq h2k_nn]
    -- q = num/den, so sqrt(q) = sqrt(num)/sqrt(den) = sqrt(num*den)/den
    have hq_eq : (q : ℝ) = (num : ℝ) / den := by
      have habs : (q.num : ℤ) = num := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
    -- Final calculation
    simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    rw [hq_eq, Real.sqrt_div hnum_real_nn]
    have hsqrt_den_pos : 0 < Real.sqrt den := Real.sqrt_pos.mpr hden_pos
    -- Key helper: sqrt(num * den) / den = sqrt(num) / sqrt(den)
    have hsqrt_conv : Real.sqrt (num * den) / den = Real.sqrt num / Real.sqrt den := by
      have hden_sqrt_mul : Real.sqrt den * Real.sqrt den = den := Real.mul_self_sqrt hden_nn
      calc Real.sqrt (num * den) / den
          = Real.sqrt num * Real.sqrt den / den := by rw [Real.sqrt_mul hnum_real_nn]
        _ = Real.sqrt num * Real.sqrt den / (Real.sqrt den * Real.sqrt den) := by rw [hden_sqrt_mul]
        _ = Real.sqrt num * (Real.sqrt den / (Real.sqrt den * Real.sqrt den)) := by rw
          [mul_div_assoc]
        _ = Real.sqrt num * (Real.sqrt den / Real.sqrt den / Real.sqrt den) := by rw
          [div_mul_eq_div_div]
        _ = Real.sqrt num * (1 / Real.sqrt den) := by rw [div_self (ne_of_gt hsqrt_den_pos)]
        _ = Real.sqrt num / Real.sqrt den := by rw [mul_one_div]
    calc (s : ℝ) / (den * 2 ^ k)
        ≤ Real.sqrt prod / (den * 2 ^ k) :=
          div_le_div_of_nonneg_right hs_le_sqrt (le_of_lt hden2k_pos)
      _ = (Real.sqrt (num * den) * 2 ^ k) / (den * 2 ^ k) := by rw [hsqrt_prod]
      _ = Real.sqrt (num * den) / den := by rw [mul_div_mul_right _ _ (ne_of_gt h2k_pos)]
      _ = Real.sqrt num / Real.sqrt den := hsqrt_conv

/-- Soundness of sqrtRatUpperPrec: Real.sqrt q ≤ sqrtRatUpperPrec q k for q ≥ 0 -/
theorem sqrt_le_sqrtRatUpperPrec {q : ℚ} (hq : 0 ≤ q) (k : Nat) :
    Real.sqrt q ≤ (sqrtRatUpperPrec q k : ℝ) := by
  simp only [sqrtRatUpperPrec]
  by_cases! hq0 : q ≤ 0
  · have heq : q = 0 := le_antisymm hq0 hq
    simp only [heq, le_refl, ↓reduceIte, Rat.cast_zero, Real.sqrt_zero]
  · simp only [not_le.mpr hq0, ↓reduceIte]
    have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden_nn : (0 : ℝ) ≤ q.den := le_of_lt hden_pos
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hnum_real_nn : (0 : ℝ) ≤ q.num.natAbs := Nat.cast_nonneg _
    have h2k_pos : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num : (0 : ℝ) < 2) k
    have h2k_nn : (0 : ℝ) ≤ 2 ^ k := le_of_lt h2k_pos
    have hden2k_pos : (0 : ℝ) < q.den * 2 ^ k := mul_pos hden_pos h2k_pos
    set num := q.num.natAbs
    set den := q.den
    set scaledNum := num * 2 ^ (2 * k)
    set prod := scaledNum * den
    set s := intSqrtNat prod
    -- sqrt(prod) ≤ result (either s or s+1)
    have h4k_eq : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by ring
    have hsqrt_prod : Real.sqrt (prod : ℕ) = Real.sqrt (num * den) * 2 ^ k := by
      calc Real.sqrt (prod : ℕ) = Real.sqrt ((scaledNum * den : ℕ) : ℝ) := by simp only [prod]
        _ = Real.sqrt ((num * 2 ^ (2 * k) * den : ℕ) : ℝ) := by simp only [scaledNum]
        _ = Real.sqrt ((num : ℝ) * 2 ^ (2 * k) * den) := by push_cast; ring_nf
        _ = Real.sqrt ((num : ℝ) * den * (2 ^ k) ^ 2) := by rw [h4k_eq]; ring_nf
        _ = Real.sqrt ((num : ℝ) * den) * Real.sqrt ((2 ^ k) ^ 2) := by
            rw [Real.sqrt_mul (mul_nonneg hnum_real_nn hden_nn)]
        _ = Real.sqrt ((num : ℝ) * den) * 2 ^ k := by rw [Real.sqrt_sq h2k_nn]
    have hq_eq : (q : ℝ) = (num : ℝ) / den := by
      have habs : (q.num : ℤ) = num := (Int.natAbs_of_nonneg hnum_nn).symm
      rw [Rat.cast_def, habs, Int.cast_natCast]
    have hsqrt_den_pos : 0 < Real.sqrt den := Real.sqrt_pos.mpr hden_pos
    -- Key helper: sqrt(num * den) / den = sqrt(num) / sqrt(den)
    have hsqrt_conv : Real.sqrt (num * den) / den = Real.sqrt num / Real.sqrt den := by
      have hden_sqrt_mul : Real.sqrt den * Real.sqrt den = den := Real.mul_self_sqrt hden_nn
      calc Real.sqrt (num * den) / den
          = Real.sqrt num * Real.sqrt den / den := by rw [Real.sqrt_mul hnum_real_nn]
        _ = Real.sqrt num * Real.sqrt den / (Real.sqrt den * Real.sqrt den) := by rw [hden_sqrt_mul]
        _ = Real.sqrt num * (Real.sqrt den / (Real.sqrt den * Real.sqrt den)) := by rw
          [mul_div_assoc]
        _ = Real.sqrt num * (Real.sqrt den / Real.sqrt den / Real.sqrt den) := by rw
          [div_mul_eq_div_div]
        _ = Real.sqrt num * (1 / Real.sqrt den) := by rw [div_self (ne_of_gt hsqrt_den_pos)]
        _ = Real.sqrt num / Real.sqrt den := by rw [mul_one_div]
    by_cases hperfect : s * s = prod
    · -- Perfect square: result = s, and sqrt(prod) = s
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
                 Rat.cast_pow, Rat.cast_ofNat]
      have hsqrt_eq_s : Real.sqrt (prod : ℕ) = s := by
        have h : (s : ℝ) ^ 2 = prod := by
          calc (s : ℝ) ^ 2 = ((s * s : ℕ) : ℝ) := by push_cast; ring
            _ = prod := by exact_mod_cast hperfect
        rw [← h, Real.sqrt_sq (Nat.cast_nonneg s)]
      rw [hq_eq, Real.sqrt_div hnum_real_nn]
      calc Real.sqrt num / Real.sqrt den
          = Real.sqrt (num * den) / den := hsqrt_conv.symm
        _ = (Real.sqrt (num * den) * 2 ^ k) / (den * 2 ^ k) := by
            rw [mul_div_mul_right _ _ (ne_of_gt h2k_pos)]
        _ = Real.sqrt prod / (den * 2 ^ k) := by rw [hsqrt_prod]
        _ ≤ (s : ℝ) / (den * 2 ^ k) := by rw [hsqrt_eq_s]
    · -- Non-perfect square: result = s + 1, and sqrt(prod) < s + 1
      simp only [hperfect, ↓reduceIte, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
                 Rat.cast_pow, Rat.cast_ofNat]
      have hlt : prod < (s + 1) ^ 2 := nat_lt_succ_sqrt_sq prod
      have hsqrt_lt : Real.sqrt (prod : ℕ) < (s + 1 : ℕ) := by
        have h1 : (prod : ℝ) < ((s + 1) ^ 2 : ℕ) := by exact_mod_cast hlt
        have h2 : (0 : ℝ) ≤ (s + 1 : ℕ) := Nat.cast_nonneg _
        have h3 : Real.sqrt (prod : ℕ) < Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) :=
          Real.sqrt_lt_sqrt (Nat.cast_nonneg _) h1
        have h4 : Real.sqrt (((s + 1) ^ 2 : ℕ) : ℝ) = (s + 1 : ℕ) := by
          have : (((s + 1) ^ 2 : ℕ) : ℝ) = ((s + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
          rw [this, Real.sqrt_sq h2]
        exact h3.trans_eq h4
      rw [hq_eq, Real.sqrt_div hnum_real_nn]
      calc Real.sqrt num / Real.sqrt den
          = Real.sqrt (num * den) / den := hsqrt_conv.symm
        _ = (Real.sqrt (num * den) * 2 ^ k) / (den * 2 ^ k) := by
            rw [mul_div_mul_right _ _ (ne_of_gt h2k_pos)]
        _ = Real.sqrt prod / (den * 2 ^ k) := by rw [hsqrt_prod]
        _ ≤ (s + 1 : ℕ) / (den * 2 ^ k) :=
            div_le_div_of_nonneg_right (le_of_lt hsqrt_lt) (le_of_lt hden2k_pos)

/-- High-precision square root interval.
    For a non-negative interval [lo, hi] with lo ≥ 0:
    - Lower bound: sqrtRatLowerPrec(lo)
    - Upper bound: sqrtRatUpperPrec(hi)

    Uses scaling to achieve ~6 decimal digits of precision. -/
def sqrtIntervalTightPrec (I : IntervalRat) : IntervalRat :=
  if h : 0 ≤ I.lo then
    ⟨sqrtRatLowerPrec I.lo, max (sqrtRatUpperPrec I.hi) 1,
     by
       simp only [le_max_iff]
       left
       have hlo_le_hi : I.lo ≤ I.hi := I.le
       have h1 : (sqrtRatLowerPrec I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLowerPrec_le_sqrt h
         sqrtScaleBits
       have h2 : Real.sqrt I.hi ≤ (sqrtRatUpperPrec I.hi : ℝ) :=
         sqrt_le_sqrtRatUpperPrec (le_trans h hlo_le_hi) sqrtScaleBits
       have h3 : Real.sqrt I.lo ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt (by exact_mod_cast hlo_le_hi)
       have h4 : (sqrtRatLowerPrec I.lo : ℝ) ≤ (sqrtRatUpperPrec I.hi : ℝ) := le_trans h1
         (le_trans h3 h2)
       exact_mod_cast h4⟩
  else
    ⟨0, max (sqrtRatUpperPrec I.hi) 1, le_sup_of_le_right rfl⟩

/-- Membership theorem for sqrtIntervalTightPrec -/
theorem mem_sqrtIntervalTightPrec' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtIntervalTightPrec I := by
  simp only [sqrtIntervalTightPrec, mem_def]
  split_ifs with h
  · -- lo ≥ 0: use tight bounds
    constructor
    · calc (sqrtRatLowerPrec I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLowerPrec_le_sqrt h sqrtScaleBits
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
    · simp only [Rat.cast_max, Rat.cast_one]
      calc Real.sqrt x ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt hx.2
        _ ≤ (sqrtRatUpperPrec I.hi : ℝ) := sqrt_le_sqrtRatUpperPrec (le_trans h I.le) sqrtScaleBits
        _ ≤ max (sqrtRatUpperPrec I.hi : ℝ) 1 := le_max_left _ _
  · -- lo < 0: use 0 as lower bound
    push Not at h
    simp only [Rat.cast_zero, Rat.cast_max, Rat.cast_one]
    constructor
    · exact Real.sqrt_nonneg x
    · -- sqrt(x) ≤ max(sqrtRatUpperPrec I.hi, 1)
      by_cases! hhi_neg : I.hi < 0
      · -- If hi < 0, then x ≤ I.hi < 0, but sqrt(x) ≥ 0, so sqrt(x) ≤ 1 ≤ max(_, 1)
        have hx_neg : x < 0 := lt_of_le_of_lt hx.2 (by exact_mod_cast hhi_neg)
        have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hx_neg)
        rw [hsqrt_zero]
        calc (0 : ℝ) ≤ 1 := by norm_num
          _ ≤ max (sqrtRatUpperPrec I.hi : ℝ) 1 := le_max_right _ _
      · calc Real.sqrt x ≤ Real.sqrt I.hi := Real.sqrt_le_sqrt hx.2
          _ ≤ (sqrtRatUpperPrec I.hi : ℝ) := sqrt_le_sqrtRatUpperPrec hhi_neg sqrtScaleBits
          _ ≤ max (sqrtRatUpperPrec I.hi : ℝ) 1 := le_max_left _ _

/-- Helper: sqrt(x) ≤ max(x, 1) for x ≥ 0 -/
private theorem sqrt_le_max_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ max x 1 := by
  rcases le_or_gt x 1 with hle | hgt
  · -- x ≤ 1: sqrt(x) ≤ 1 ≤ max(x, 1)
    calc Real.sqrt x ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
      _ ≤ max x 1 := le_max_right x 1
  · -- x > 1: sqrt(x) < x ≤ max(x, 1)
    have hx_pos : 0 < x := lt_trans zero_lt_one hgt
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hsqrt_gt_one : 1 < Real.sqrt x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hgt
    have hsqrt_lt : Real.sqrt x < x := by
      have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
      have h2 : Real.sqrt x * 1 < Real.sqrt x * Real.sqrt x :=
        mul_lt_mul_of_pos_left hsqrt_gt_one hsqrt_pos
      simp only [mul_one] at h2
      linarith
    calc Real.sqrt x ≤ x := le_of_lt hsqrt_lt
      _ ≤ max x 1 := le_max_left x 1

/-- Soundness of sqrt interval: if x ∈ I and x ≥ 0, then sqrt(x) ∈ sqrtInterval I -/
theorem mem_sqrtInterval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hx_nn : 0 ≤ x) :
    Real.sqrt x ∈ sqrtInterval I := by
  simp only [mem_def, sqrtInterval, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
  constructor
  · exact Real.sqrt_nonneg x
  · calc Real.sqrt x ≤ max x 1 := sqrt_le_max_one hx_nn
      _ ≤ max (I.hi : ℝ) 1 := max_le_max_right 1 hx.2

/-- General soundness of sqrt interval: works for any x ∈ I (including negative).
    When x < 0, Real.sqrt x = 0, which is always in [0, max(hi, 1)]. -/
theorem mem_sqrtInterval' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtInterval I := by
  rcases le_or_gt 0 x with hnn | hneg
  · -- x ≥ 0: use the standard soundness
    exact mem_sqrtInterval hx hnn
  · -- x < 0: sqrt(x) = 0, and 0 ∈ [0, max(hi, 1)]
    simp only [mem_def, sqrtInterval, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
    have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
    rw [hsqrt_zero]
    constructor
    · exact le_refl 0
    · calc (0 : ℝ) ≤ 1 := by norm_num
        _ ≤ max (I.hi : ℝ) 1 := le_max_right _ _

/-- Helper: upper bound for tight sqrt interval is valid -/
private theorem sqrt_le_sqrtRatUpper_max {x : ℝ} {q : ℚ} (hx : 0 ≤ x) (hxq : x ≤ q) :
    Real.sqrt x ≤ max (sqrtRatUpper q : ℝ) 1 := by
  by_cases! hq0 : q ≤ 0
  · -- q ≤ 0 means x ≤ 0, combined with hx gives x = 0
    have hx0 : x = 0 := le_antisymm (le_trans hxq (by exact_mod_cast hq0)) hx
    rw [hx0, Real.sqrt_zero]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right (sqrtRatUpper q : ℝ) (1 : ℝ))
  · -- q > 0
    calc Real.sqrt x
        ≤ Real.sqrt q := Real.sqrt_le_sqrt hxq
      _ ≤ sqrtRatUpper q := sqrt_le_sqrtRatUpper (le_of_lt hq0)
      _ ≤ max (sqrtRatUpper q : ℝ) 1 := le_max_left (sqrtRatUpper q : ℝ) (1 : ℝ)

/-- Soundness of tight sqrt interval: if x ∈ I and x ≥ 0, then sqrt(x) ∈ sqrtIntervalTight I -/
theorem mem_sqrtIntervalTight {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hx_nn : 0 ≤ x) :
    Real.sqrt x ∈ sqrtIntervalTight I := by
  simp only [sqrtIntervalTight]
  split_ifs with hlo
  · -- Case: I.lo ≥ 0 (positive interval)
    simp only [mem_def, Rat.cast_max, Rat.cast_one]
    constructor
    · -- Lower bound: sqrtRatLower I.lo ≤ sqrt(x)
      have h1 : (sqrtRatLower I.lo : ℝ) ≤ Real.sqrt I.lo := sqrtRatLower_le_sqrt hlo
      have h2 : Real.sqrt (I.lo : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
      exact le_trans h1 h2
    · -- Upper bound: sqrt(x) ≤ max (sqrtRatUpper I.hi) 1
      exact sqrt_le_sqrtRatUpper_max hx_nn hx.2
  · -- Case: I.lo < 0 (interval crosses zero)
    simp only [mem_def, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
    constructor
    · exact Real.sqrt_nonneg x
    · exact sqrt_le_sqrtRatUpper_max hx_nn hx.2

/-- General soundness of tight sqrt interval: works for any x ∈ I (including negative).
    When x < 0, Real.sqrt x = 0, which is always in the result interval. -/
theorem mem_sqrtIntervalTight' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtIntervalTight I := by
  rcases le_or_gt 0 x with hnn | hneg
  · exact mem_sqrtIntervalTight hx hnn
  · -- x < 0: sqrt(x) = 0
    have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
    simp only [sqrtIntervalTight]
    split_ifs with hlo
    · -- I.lo ≥ 0, but x ∈ I and x < 0, contradiction
      have h : (I.lo : ℝ) ≤ x := hx.1
      have hlo_real : (0 : ℝ) ≤ I.lo := by exact_mod_cast hlo
      have hx_nn : 0 ≤ x := le_trans hlo_real h
      exact absurd hx_nn (not_le.mpr hneg)
    · -- I.lo < 0
      simp only [mem_def, Rat.cast_zero, Rat.cast_max, Rat.cast_one]
      rw [hsqrt_zero]
      constructor
      · exact le_refl 0
      · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right (sqrtRatUpper I.hi : ℝ) (1 : ℝ))

end IntervalRat

end LeanCert.Core
