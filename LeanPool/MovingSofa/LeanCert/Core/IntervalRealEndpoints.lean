/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.IntervalReal
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.MeanValue
/-!
# Intervals with Real Endpoints

This file defines `IntervalReal`, an interval type with real (ℝ) endpoints.
Unlike `IntervalRat` (which has rational endpoints and is suitable for computation),
`IntervalReal` allows us to represent intervals involving transcendental values
like `[1, Real.exp 1]` or `[Real.log 2, π]`.

## Main definitions

* `IntervalReal` - Intervals with real endpoints
* `expInterval` - Interval bound for exp
* `logInterval` - Interval bound for log (on positive intervals)

## Main theorems

* `mem_expInterval` - FTIA for exp: if x ∈ I, then exp(x) ∈ expInterval(I)

## Design notes

This type complements `IntervalRat` for proving facts about transcendental functions.
While `IntervalRat` is used for numerical computation (since rationals are computable),
`IntervalReal` is used for correctness proofs involving exp, log, etc.

Typical workflow:
1. Use `IntervalRat` for actual interval arithmetic computations
2. Convert to `IntervalReal` when proving facts about transcendental functions
3. Use mathlib's analysis lemmas directly on real intervals
-/

@[expose] public section

namespace LeanCert.Core

/-- An interval with real endpoints -/
structure IntervalReal where
  /-- Lower endpoint of the interval. -/
  lo : ℝ
  /-- Upper endpoint of the interval. -/
  hi : ℝ
  le : lo ≤ hi

namespace IntervalReal

/-- The set of reals contained in this interval -/
def toSet (I : IntervalReal) : Set ℝ := Set.Icc I.lo I.hi

/-- Membership in an interval -/
instance : Membership ℝ IntervalReal where
  mem I x := I.lo ≤ x ∧ x ≤ I.hi

@[simp]
theorem mem_def (x : ℝ) (I : IntervalReal) : x ∈ I ↔ I.lo ≤ x ∧ x ≤ I.hi :=
  Iff.rfl

theorem mem_toSet_iff (x : ℝ) (I : IntervalReal) : x ∈ I.toSet ↔ x ∈ I := by
  simp only [toSet, Set.mem_Icc, mem_def]

/-- Create an interval from a single real -/
def singleton (r : ℝ) : IntervalReal := ⟨r, r, le_refl r⟩

theorem mem_singleton (r : ℝ) : r ∈ singleton r := ⟨le_refl r, le_refl r⟩

/-- Convert from IntervalRat to IntervalReal -/
def ofRat (I : IntervalRat) : IntervalReal where
  lo := I.lo
  hi := I.hi
  le := by exact_mod_cast I.le

theorem mem_ofRat {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : x ∈ ofRat I := by
  simp only [mem_def, ofRat] at *
  exact hx

/-! ### Interval addition -/

/-- Add two intervals -/
def add (I J : IntervalReal) : IntervalReal where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  le := by linarith [I.le, J.le]

/-- FTIA for addition -/
theorem mem_add {x y : ℝ} {I J : IntervalReal} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add I J := by
  simp only [mem_def] at *
  simp only [add]
  constructor <;> linarith

/-! ### Interval negation -/

/-- Negate an interval -/
def neg (I : IntervalReal) : IntervalReal where
  lo := -I.hi
  hi := -I.lo
  le := by linarith [I.le]

/-- FTIA for negation -/
theorem mem_neg {x : ℝ} {I : IntervalReal} (hx : x ∈ I) : -x ∈ neg I := by
  simp only [mem_def] at *
  simp only [neg]
  constructor <;> linarith

/-! ### Interval multiplication -/

/-- The minimum of four real endpoints, used for interval multiplication. -/
def min4 (a b c d : ℝ) : ℝ := min (min a b) (min c d)
/-- The maximum of four real endpoints, used for interval multiplication. -/
def max4 (a b c d : ℝ) : ℝ := max (max a b) (max c d)

/-- Multiply two intervals -/
def mul (I J : IntervalReal) : IntervalReal where
  lo := min4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  hi := max4 (I.lo * J.lo) (I.lo * J.hi) (I.hi * J.lo) (I.hi * J.hi)
  le := by
    simp only [min4, max4]
    exact le_trans (min_le_of_left_le (min_le_left _ _))
                   (le_max_of_le_left (le_max_left _ _))

/-! ### Exponential interval -/

/-- Interval bound for exp.
    Since exp is strictly increasing, exp([a,b]) = [exp(a), exp(b)]. -/
noncomputable def expInterval (I : IntervalReal) : IntervalReal where
  lo := Real.exp I.lo
  hi := Real.exp I.hi
  le := Real.exp_le_exp.mpr I.le

/-- FTIA for exp: if x ∈ [a,b], then exp(x) ∈ [exp(a), exp(b)].
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_expInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.exp x ∈ expInterval I := by
  simp only [mem_def] at *
  simp only [expInterval]
  constructor
  · exact Real.exp_le_exp.mpr hx.1
  · exact Real.exp_le_exp.mpr hx.2

/-! ### Logarithm interval (for positive intervals) -/

/-- An interval that is strictly positive -/
structure IntervalRealPos extends IntervalReal where
  lo_pos : 0 < toIntervalReal.lo

/-- Interval bound for log on positive intervals.
    Since log is strictly increasing on (0, ∞), log([a,b]) = [log(a), log(b)] for a > 0. -/
noncomputable def logInterval (I : IntervalRealPos) : IntervalReal where
  lo := Real.log I.lo
  hi := Real.log I.hi
  le := Real.log_le_log I.lo_pos I.le

/-- FTIA for log: if x ∈ [a,b] with a > 0, then log(x) ∈ [log(a), log(b)].
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_logInterval {x : ℝ} {I : IntervalRealPos} (hx : x ∈ I.toIntervalReal) :
    Real.log x ∈ logInterval I := by
  simp only [mem_def] at *
  simp only [logInterval]
  have hx_pos : 0 < x := lt_of_lt_of_le I.lo_pos hx.1
  constructor
  · exact Real.log_le_log I.lo_pos hx.1
  · exact Real.log_le_log hx_pos hx.2

/-! ### Trigonometric intervals (global bounds) -/

/-- Interval bound for sin. Since |sin x| ≤ 1 for all x, we use [-1, 1]. -/
def sinInterval (_I : IntervalReal) : IntervalReal :=
  ⟨-1, 1, by norm_num⟩

/-- FTIA for sin -/
theorem mem_sinInterval {x : ℝ} {I : IntervalReal} (_hx : x ∈ I) :
    Real.sin x ∈ sinInterval I := by
  simp only [mem_def, sinInterval]
  have h := Real.sin_mem_Icc x
  simp only [Set.mem_Icc] at h
  exact h

/-- Interval bound for cos. Since |cos x| ≤ 1 for all x, we use [-1, 1]. -/
def cosInterval (_I : IntervalReal) : IntervalReal :=
  ⟨-1, 1, by norm_num⟩

/-- FTIA for cos -/
theorem mem_cosInterval {x : ℝ} {I : IntervalReal} (_hx : x ∈ I) :
    Real.cos x ∈ cosInterval I := by
  simp only [mem_def, cosInterval]
  have h := Real.cos_mem_Icc x
  simp only [Set.mem_Icc] at h
  exact h

/-- Interval bound for atan. Since arctan x ∈ (-π/2, π/2) ⊂ [-2, 2] for all x. -/
def atanInterval (_I : IntervalReal) : IntervalReal :=
  ⟨-2, 2, by norm_num⟩

/-- FTIA for atan -/
theorem mem_atanInterval {x : ℝ} {I : IntervalReal} (_hx : x ∈ I) :
    Real.arctan x ∈ atanInterval I := by
  simp only [mem_def, atanInterval]
  constructor
  · have := Real.neg_pi_div_two_lt_arctan x
    have hpi : Real.pi < 4 := Real.pi_lt_four
    linarith
  · have := Real.arctan_lt_pi_div_two x
    have hpi : Real.pi < 4 := Real.pi_lt_four
    linarith

/-- The derivative of arsinh is bounded by 1: |arsinh'(x)| = 1/√(1+x²) ≤ 1 -/
private theorem arsinh_deriv_abs_le_one (x : ℝ) : |deriv Real.arsinh x| ≤ 1 := by
  have hderiv : deriv Real.arsinh x = (Real.sqrt (1 + x ^ 2))⁻¹ :=
    (Real.hasDerivAt_arsinh x).deriv
  rw [hderiv]
  have hsqrt_ge_one : Real.sqrt (1 + x ^ 2) ≥ 1 := by
    have h1 : 1 + x ^ 2 ≥ 1 := by nlinarith [sq_nonneg x]
    calc Real.sqrt (1 + x ^ 2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  have hsqrt_pos : 0 < Real.sqrt (1 + x ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg x]
  rw [abs_inv, abs_of_pos hsqrt_pos]
  exact inv_le_one_of_one_le₀ hsqrt_ge_one

/-- |arsinh x| ≤ |x| for all x. This follows from MVT and |arsinh'| ≤ 1. -/
theorem abs_arsinh_le_abs (x : ℝ) : |Real.arsinh x| ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · -- Case x ≥ 0: arsinh x ≥ 0 by monotonicity of arsinh
    rcases eq_or_lt_of_le hx with rfl | hx_pos
    · -- x = 0
      simp [Real.arsinh_zero]
    · -- x > 0
      have harsinh_nonneg : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr (le_of_lt hx_pos)
      have hcont : ContinuousOn Real.arsinh (Set.Icc 0 x) :=
        Real.continuous_arsinh.continuousOn
      have hdiff : DifferentiableOn ℝ Real.arsinh (Set.Ioo 0 x) :=
        Real.differentiable_arsinh.differentiableOn
      obtain ⟨c, ⟨_, _⟩, hc_eq⟩ := exists_deriv_eq_slope Real.arsinh hx_pos hcont hdiff
      simp only [Real.arsinh_zero, sub_zero] at hc_eq
      have hderiv_bound : |deriv Real.arsinh c| ≤ 1 := arsinh_deriv_abs_le_one c
      rw [abs_of_nonneg harsinh_nonneg, abs_of_pos hx_pos]
      have heq : Real.arsinh x = deriv Real.arsinh c * x := by rw [hc_eq]; field_simp
      calc Real.arsinh x = deriv Real.arsinh c * x := heq
        _ ≤ |deriv Real.arsinh c * x| := le_abs_self _
        _ = |deriv Real.arsinh c| * |x| := abs_mul _ _
        _ ≤ 1 * x := by rw [abs_of_pos hx_pos]; nlinarith [abs_nonneg x, hderiv_bound]
        _ = x := one_mul _
  · -- Case x < 0: use oddness arsinh(-x) = -arsinh(x)
    have hx_neg : -x > 0 := by linarith
    -- For x < 0, arsinh x < 0 (arsinh is strictly increasing, arsinh 0 = 0)
    have harsinh_neg : Real.arsinh x < 0 := Real.arsinh_neg_iff.mpr hx
    have harsinh_neg_nonneg : 0 ≤ Real.arsinh (-x) := Real.arsinh_nonneg_iff.mpr (by linarith)
    -- Use the positive case on -x
    have hcont : ContinuousOn Real.arsinh (Set.Icc 0 (-x)) :=
      Real.continuous_arsinh.continuousOn
    have hdiff : DifferentiableOn ℝ Real.arsinh (Set.Ioo 0 (-x)) :=
      Real.differentiable_arsinh.differentiableOn
    obtain ⟨c, ⟨_, _⟩, hc_eq⟩ := exists_deriv_eq_slope Real.arsinh hx_neg hcont hdiff
    simp only [Real.arsinh_zero, sub_zero] at hc_eq
    have hderiv_bound : |deriv Real.arsinh c| ≤ 1 := arsinh_deriv_abs_le_one c
    rw [abs_of_neg harsinh_neg, abs_of_neg hx]
    have heq : Real.arsinh (-x) = deriv Real.arsinh c * (-x) := by
      have hne : (-x) ≠ 0 := ne_of_gt hx_neg
      have : deriv Real.arsinh c * (-x) = (Real.arsinh (-x) / (-x)) * (-x) := by rw [hc_eq]
      rw [this, div_mul_cancel₀ _ hne]
    calc -Real.arsinh x = Real.arsinh (-x) := by rw [Real.arsinh_neg]
      _ = deriv Real.arsinh c * (-x) := heq
      _ ≤ |deriv Real.arsinh c * (-x)| := le_abs_self _
      _ = |deriv Real.arsinh c| * |-x| := abs_mul _ _
      _ ≤ 1 * (-x) := by rw [abs_of_pos hx_neg]; nlinarith [abs_nonneg (-x), hderiv_bound]
      _ = -x := one_mul _

/-- Interval bound for arsinh. Uses a conservative bound based on input interval. -/
def arsinhInterval (I : IntervalReal) : IntervalReal :=
  -- arsinh is monotonic, so we just apply it to endpoints
  -- Using conservative bound: |arsinh x| ≤ |x|, plus margin of 1 for safety
  let bound := max (|I.lo|) (|I.hi|) + 1
  ⟨-bound, bound, by
    have h3 : (0 : ℝ) ≤ max (|I.lo|) (|I.hi|) := le_max_of_le_left (abs_nonneg I.lo)
    change -(max (|I.lo|) (|I.hi|) + 1) ≤ max (|I.lo|) (|I.hi|) + 1
    linarith⟩

/-- FTIA for arsinh -/
theorem mem_arsinhInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.arsinh x ∈ arsinhInterval I := by
  unfold arsinhInterval
  simp only [mem_def]
  have habs : |Real.arsinh x| ≤ max (|I.lo|) (|I.hi|) + 1 := by
    have h1 : |Real.arsinh x| ≤ |x| := abs_arsinh_le_abs x
    have h2 : |x| ≤ max (|I.lo|) (|I.hi|) := by
      simp only [IntervalReal.mem_def] at hx
      rcases le_or_gt x 0 with hxneg | hxpos
      · rw [abs_of_nonpos hxneg]
        calc -x ≤ -I.lo := by linarith [hx.1]
          _ ≤ |I.lo| := neg_le_abs I.lo
          _ ≤ max (|I.lo|) (|I.hi|) := le_max_left _ _
      · rw [abs_of_pos hxpos]
        calc x ≤ I.hi := hx.2
          _ ≤ |I.hi| := le_abs_self I.hi
          _ ≤ max (|I.lo|) (|I.hi|) := le_max_right _ _
    linarith
  constructor
  · have := neg_abs_le (Real.arsinh x)
    linarith
  · have := le_abs_self (Real.arsinh x)
    linarith

/-! ### Hyperbolic function intervals -/

/-- Interval bound for sinh.
    Since sinh is strictly monotonic increasing, sinh([a,b]) = [sinh(a), sinh(b)]. -/
noncomputable def sinhInterval (I : IntervalReal) : IntervalReal where
  lo := Real.sinh I.lo
  hi := Real.sinh I.hi
  le := Real.sinh_le_sinh.mpr I.le

/-- FTIA for sinh: if x ∈ [a,b], then sinh(x) ∈ [sinh(a), sinh(b)].
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_sinhInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.sinh x ∈ sinhInterval I := by
  simp only [mem_def] at *
  simp only [sinhInterval]
  exact ⟨Real.sinh_le_sinh.mpr hx.1, Real.sinh_le_sinh.mpr hx.2⟩

/-- Interval bound for cosh.
    cosh is convex with minimum at 0:
    - If interval is all non-negative: cosh is increasing
    - If interval is all non-positive: cosh is decreasing
    - If interval contains 0: minimum is cosh(0) = 1, max is at endpoints -/
noncomputable def coshInterval (I : IntervalReal) : IntervalReal :=
  if h1 : 0 ≤ I.lo then
    -- Interval is [a,b] with 0 ≤ a: cosh increasing, so [cosh(a), cosh(b)]
    -- Since 0 ≤ a ≤ b, we have |a| ≤ |b|, so cosh(a) ≤ cosh(b)
    ⟨Real.cosh I.lo, Real.cosh I.hi, by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 I.le)]
      exact I.le⟩
  else if h2 : I.hi ≤ 0 then
    -- Interval is [a,b] with b ≤ 0: cosh decreasing, so [cosh(b), cosh(a)]
    -- Since a ≤ b ≤ 0, we have |b| ≤ |a|, so cosh(b) ≤ cosh(a)
    ⟨Real.cosh I.hi, Real.cosh I.lo, by
      rw [Real.cosh_le_cosh]
      have hlo_neg : I.lo < 0 := not_le.mp h1
      rw [abs_of_nonpos h2, abs_of_nonpos (le_of_lt hlo_neg)]
      linarith [I.le]⟩
  else
    -- Interval contains 0: min is 1, max is max(cosh(lo), cosh(hi))
    ⟨1, max (Real.cosh I.lo) (Real.cosh I.hi), by
      have h := Real.one_le_cosh I.lo
      exact le_trans h (le_max_left _ _)⟩

/-- FTIA for cosh: if x ∈ [a,b], then cosh(x) ∈ coshInterval([a,b]).
    This is FULLY PROVED - no sorry, no axioms. -/
theorem mem_coshInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.cosh x ∈ coshInterval I := by
  simp only [mem_def] at hx
  unfold coshInterval
  split_ifs with h1 h2
  · -- Case: 0 ≤ I.lo (cosh increasing on [0, ∞))
    simp only [mem_def]
    have hx_nonneg : 0 ≤ x := le_trans h1 hx.1
    constructor
    · rw [Real.cosh_le_cosh, abs_of_nonneg h1, abs_of_nonneg hx_nonneg]
      exact hx.1
    · rw [Real.cosh_le_cosh, abs_of_nonneg hx_nonneg, abs_of_nonneg (le_trans h1 I.le)]
      exact hx.2
  · -- Case: I.hi ≤ 0 (cosh decreasing on (-∞, 0])
    simp only [mem_def]
    have hx_nonpos : x ≤ 0 := le_trans hx.2 h2
    have hlo_neg : I.lo < 0 := not_le.mp h1
    constructor
    · rw [Real.cosh_le_cosh, abs_of_nonpos h2, abs_of_nonpos hx_nonpos]
      linarith
    · rw [Real.cosh_le_cosh, abs_of_nonpos hx_nonpos, abs_of_nonpos (le_of_lt hlo_neg)]
      linarith
  · -- Case: interval contains 0
    simp only [mem_def]
    push Not at h1 h2
    constructor
    · exact Real.one_le_cosh x
    · -- cosh(x) ≤ max(cosh(lo), cosh(hi))
      by_cases! hx0 : 0 ≤ x
      · -- x ≥ 0: cosh(x) ≤ cosh(hi) since |x| ≤ |hi|
        have hle : Real.cosh x ≤ Real.cosh I.hi := by
          rw [Real.cosh_le_cosh, abs_of_nonneg hx0, abs_of_pos h2]
          exact hx.2
        exact le_trans hle (le_max_right _ _)
      · -- x < 0: cosh(x) ≤ cosh(lo) since |x| ≤ |lo|
        have hx_nonpos : x ≤ 0 := le_of_lt hx0
        have hle : Real.cosh x ≤ Real.cosh I.lo := by
          rw [Real.cosh_le_cosh, abs_of_nonpos hx_nonpos, abs_of_neg h1]
          linarith
        exact le_trans hle (le_max_left _ _)

/-! ### Square root interval -/

/-- Interval bound for sqrt.
    For any interval I, sqrt(x) ∈ [0, max(hi, 1)] for x ∈ I.
    This is always sound because:
    - sqrt(x) ≥ 0 for all x (Mathlib convention: sqrt(negative) = 0)
    - sqrt(x) ≤ max(x, 1) for x ≥ 0, so sqrt(x) ≤ max(hi, 1) -/
noncomputable def sqrtInterval (I : IntervalReal) : IntervalReal where
  lo := 0
  hi := max I.hi 1
  le := le_max_of_le_right zero_le_one

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

/-- FTIA for sqrt: if x ∈ I, then sqrt(x) ∈ sqrtInterval(I).
    Works for all x including negative (where sqrt returns 0 by Mathlib convention). -/
theorem mem_sqrtInterval {x : ℝ} {I : IntervalReal} (hx : x ∈ I) :
    Real.sqrt x ∈ sqrtInterval I := by
  simp only [mem_def, sqrtInterval]
  constructor
  · exact Real.sqrt_nonneg x
  · rcases le_or_gt 0 x with hnn | hneg
    · -- x ≥ 0: sqrt(x) ≤ max(x, 1) ≤ max(hi, 1)
      calc Real.sqrt x ≤ max x 1 := sqrt_le_max_one hnn
        _ ≤ max I.hi 1 := max_le_max_right 1 hx.2
    · -- x < 0: sqrt(x) = 0 ≤ max(hi, 1)
      have hsqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt hneg)
      rw [hsqrt_zero]
      exact le_max_of_le_right zero_le_one

end IntervalReal

end LeanCert.Core
