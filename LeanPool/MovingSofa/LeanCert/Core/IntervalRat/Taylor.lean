/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Basic
public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.LogReduction
public import LeanPool.MovingSofa.LeanCert.Core.Taylor
public import LeanPool.MovingSofa.LeanCert.Core.Expr
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.List.Range
/-!
# Rational Endpoint Intervals - Computable Taylor Series

This file provides computable interval enclosures for transcendental functions
using Taylor series with rational coefficients and rigorous remainder bounds.

## Main definitions

* `ratFactorial` - Compute n! as a rational
* `pow` - Compute interval power
* `absInterval`, `maxAbs` - Absolute value helpers
* `evalTaylorSeries` - Evaluate Taylor polynomial on an interval
* `expComputable`, `sinComputable`, `cosComputable` - Computable transcendental functions
* `sinhComputable`, `coshComputable` - Computable hyperbolic functions

## Main theorems

* `mem_pow` - FTIA for interval power
* `mem_evalTaylorSeries` - General FTIA for Taylor series
* `mem_expComputable`, `mem_sinComputable`, `mem_cosComputable` - FTIA for computable functions

## Design notes

All definitions in this file use only rational arithmetic and are fully computable.
The proofs connect these to the real-valued functions via Taylor's theorem.
-/

/-! ### Computable Taylor series helpers -/

@[expose] public section

namespace LeanCert.Core

namespace IntervalRat

/-- Compute n! as a Rational -/
def ratFactorial (n : ℕ) : ℚ := (Nat.factorial n : ℚ)

/-- Compute the integer power of an interval using exponentiation by squaring.
    O(log n) interval multiplications instead of O(n). -/
def pow (I : IntervalRat) : ℕ → IntervalRat
  | 0 => singleton 1
  | 1 => I
  | n + 2 =>
    let half := pow I ((n + 2) / 2)
    let sq := mul half half
    if (n + 2) % 2 == 0 then sq else mul I sq

/-- Compute the absolute value interval: |I| = [0, max(|lo|, |hi|)] if 0 ∈ I,
    or [min(|lo|,|hi|), max(|lo|,|hi|)] otherwise -/
def absInterval (I : IntervalRat) : IntervalRat :=
  if h1 : I.lo ≥ 0 then
    I
  else if h2 : I.hi ≤ 0 then
    neg I
  else
    ⟨0, max (-I.lo) I.hi, by
      apply le_max_of_le_right
      push Not at h1 h2
      linarith⟩

/-- Maximum absolute value of an interval -/
def maxAbs (I : IntervalRat) : ℚ := max (|I.lo|) (|I.hi|)

/-- Evaluate Taylor series ∑_{i=0}^{n} c_i * x^i at interval I using Horner's method.
    Computes c₀ + I * (c₁ + I * (c₂ + ... + I * cₙ)), which is mathematically
    equivalent to the direct sum but uses fewer operations and often gives tighter
    bounds by reducing the dependency problem in interval arithmetic. -/
def evalTaylorSeries (coeffs : List ℚ) (I : IntervalRat) : IntervalRat :=
  coeffs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton 0)

/-! ### Computable exp via Taylor series -/

/-- Tail-recursive exp coefficient generator.
    `expTaylorCoeffsAux n k c` produces `n+1` coefficients starting at index `k`,
    assuming `c = 1 / k!`. -/
def expTaylorCoeffsAux : ℕ → ℕ → ℚ → List ℚ
  | 0, _, c => [c]
  | (n + 1), k, c => c :: expTaylorCoeffsAux n (k + 1) (c / (k + 1))

/-- Taylor coefficients for exp: 1/i! for i = 0, 1, ..., n.
    Implemented iteratively to avoid repeated factorial recomputation. -/
def expTaylorCoeffs (n : ℕ) : List ℚ :=
  expTaylorCoeffsAux n 0 1

/-- `ratFactorial` unfolds factorial as a product. -/
private lemma ratFactorial_succ (k : ℕ) :
    ratFactorial (k + 1) = ratFactorial k * (k + 1) := by
  simp [ratFactorial, Nat.factorial_succ, Nat.cast_mul, mul_comm]

private lemma map_range_succ {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- range (n+2) = range (n+1) ++ [n+1]
      calc
        (List.range (n + 2)).map f
            = (List.range (n + 1) ++ [n + 1]).map f := by
                simp [List.range_succ]
        _ = (List.range (n + 1)).map f ++ [f (n + 1)] := by
                simp [List.map_append]
        _ = (f 0 :: (List.range n).map (fun i => f (i + 1))) ++ [f (n + 1)] := by
                simp [ih]
        _ = f 0 :: ((List.range n).map (fun i => f (i + 1)) ++ [f (n + 1)]) := by
                rfl
        _ = f 0 :: (List.range (n + 1)).map (fun i => f (i + 1)) := by
                simp [List.range_succ, List.map_append]

/-- Iterative exp coefficients match the standard `1 / i!` definition. -/
private lemma expTaylorCoeffsAux_eq_range (n k : ℕ) :
    expTaylorCoeffsAux n k (1 / ratFactorial k) =
      (List.range (n + 1)).map (fun i => 1 / ratFactorial (i + k)) := by
  induction n generalizing k with
  | zero =>
      simp [expTaylorCoeffsAux]
  | succ n ih =>
      have hstep : (ratFactorial k)⁻¹ / (k + 1) = (ratFactorial (k + 1))⁻¹ := by
        -- (1/k!) / (k+1) = 1/(k+1)!
        simp [ratFactorial_succ, div_eq_mul_inv, mul_comm]
      calc
        expTaylorCoeffsAux (n + 1) k (1 / ratFactorial k)
            = (1 / ratFactorial k) ::
                expTaylorCoeffsAux n (k + 1) ((1 / ratFactorial k) / (k + 1)) := by
                  rfl
        _ = (1 / ratFactorial k) ::
                expTaylorCoeffsAux n (k + 1) ((ratFactorial k)⁻¹ / (k + 1)) := by
                  simp [one_div]
        _ = (1 / ratFactorial k) ::
                expTaylorCoeffsAux n (k + 1) (ratFactorial (k + 1))⁻¹ := by
                  simp [hstep]
        _ = (1 / ratFactorial k) ::
              (List.range (n + 1)).map (fun i => (ratFactorial (i + (k + 1)))⁻¹) := by
                  simpa [one_div] using (ih (k + 1))
        _ = (List.range (n + 2)).map (fun i => 1 / ratFactorial (i + k)) := by
            -- unfold the range map at the front
            have hmap := map_range_succ (fun i => 1 / ratFactorial (i + k)) (n + 1)
            -- rewrite and simplify
            simpa [one_div, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmap.symm

private lemma expTaylorCoeffs_eq_range_map (n : ℕ) :
    expTaylorCoeffs n = (List.range (n + 1)).map (fun i => 1 / ratFactorial i) := by
  have h0 : (1 / ratFactorial 0 : ℚ) = 1 := by simp [ratFactorial]
  simpa [expTaylorCoeffs, h0] using (expTaylorCoeffsAux_eq_range n 0)

/-- Computable exp remainder bound using rational arithmetic.
    The Lagrange remainder is exp(ξ) * x^{n+1} / (n+1)! where ξ is between 0 and x.
    We use e < 3, so e^r ≤ 3^(⌈r⌉+1) as a conservative bound.

    Returns an interval [-R, R] where R bounds the remainder. -/
def expRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  -- Crude bound: e < 3, so e^r ≤ 3^(ceil(r)+1)
  let expBound := (3 : ℚ) ^ (Nat.ceil r + 1)
  let xBound := r ^ (n + 1)
  let R := expBound * xBound / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply mul_nonneg
        · apply pow_nonneg; norm_num
        · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- The raw rational Taylor enclosure of the exponential at a point. -/
def expPointComputableRaw (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let I := singleton q
  let coeffs := expTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := expRemainderBoundComputable I n
  add polyVal remainder

/-- Heuristic reduction factor for exp evaluation.
    We choose `k = log2(ceil(|q|) + 1)`, so `2^k` grows roughly with |q|.
    No correctness depends on the specific choice; it only affects performance. -/
def expReduceK (q : ℚ) : ℕ :=
  Nat.log2 (Nat.ceil |q| + 1)

/-- Computable interval enclosure for exp at a single rational point.
    Uses argument reduction: `exp(q) = exp(q/2^k)^(2^k)`. -/
def expPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let k := expReduceK q
  let m : ℕ := (2:ℕ)^k
  let q' : ℚ := q / m
  pow (expPointComputableRaw q' n) m

/-- Point exponential using Taylor coefficients prepared for depth `n`. -/
def expPointComputableWithCoeffs (q : ℚ) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  let k := expReduceK q
  let m : ℕ := (2 : ℕ) ^ k
  let q' : ℚ := q / m
  let I := singleton q'
  let polyVal := evalTaylorSeries coeffs I
  let remainder := expRemainderBoundComputable I n
  pow (add polyVal remainder) m

theorem expPointComputableWithCoeffs_eq (q : ℚ) (n : ℕ) :
    expPointComputableWithCoeffs q n (expTaylorCoeffs n) = expPointComputable q n := by
  simp [expPointComputableWithCoeffs, expPointComputable, expPointComputableRaw]

/-- Hull of two intervals: smallest interval containing both. -/
def hull (I J : IntervalRat) : IntervalRat :=
  ⟨min I.lo J.lo, max I.hi J.hi, le_trans (min_le_left _ _) (le_trans I.le (le_max_left _ _))⟩

/-- Membership in hull -/
theorem mem_hull_left {x : ℝ} {I J : IntervalRat} (hx : x ∈ I) : x ∈ hull I J := by
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_left _ _) hx.1
  · exact le_trans hx.2 (le_max_left _ _)

theorem mem_hull_right {x : ℝ} {I J : IntervalRat} (hx : x ∈ J) : x ∈ hull I J := by
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · exact le_trans (min_le_right _ _) hx.1
  · exact le_trans hx.2 (le_max_right _ _)

/-- Computable interval enclosure for exp using Taylor series with monotonicity optimization.

    exp(x) = ∑_{i=0}^{n} x^i/i! + R where |R| ≤ exp(|x|) * |x|^{n+1} / (n+1)!

    For intervals not crossing 0, we use endpoint evaluation and take the hull,
    which is tighter than direct Taylor evaluation due to interval widening.

    This is fully computable using only rational arithmetic. -/
def expComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  if I.hi ≤ 0 ∨ 0 ≤ I.lo then
    -- Interval doesn't cross 0: use endpoint evaluation for tighter bounds
    let expLo := expPointComputable I.lo n
    let expHi := expPointComputable I.hi n
    hull expLo expHi
  else
    -- Interval crosses 0: use standard Taylor (can't avoid interval widening)
    let coeffs := expTaylorCoeffs n
    let polyVal := evalTaylorSeries coeffs I
    let remainder := expRemainderBoundComputable I n
    add polyVal remainder

/-- Interval exponential using Taylor coefficients prepared for depth `n`. -/
def expComputableWithCoeffs (I : IntervalRat) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  if I.hi ≤ 0 ∨ 0 ≤ I.lo then
    let expLo := expPointComputableWithCoeffs I.lo n coeffs
    let expHi := expPointComputableWithCoeffs I.hi n coeffs
    hull expLo expHi
  else
    let polyVal := evalTaylorSeries coeffs I
    let remainder := expRemainderBoundComputable I n
    add polyVal remainder

theorem expComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    expComputableWithCoeffs I n (expTaylorCoeffs n) = expComputable I n := by
  simp [expComputableWithCoeffs, expComputable, expPointComputableWithCoeffs_eq]

/-! ### Computable sin via Taylor series -/

/-- Taylor coefficients for sin: 0, 1, 0, -1/6, 0, 1/120, ... -/
def sinTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 1 then  -- odd terms only
      ((-1 : ℚ) ^ ((i - 1) / 2)) / ratFactorial i
    else 0)

/-- Computable sin remainder bound.
    Since |sin^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
def sinRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for sin using Taylor series.

    sin(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k+1}/(2k+1)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of sin are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
def sinComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := sinTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := sinRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-- Interval sine using Taylor coefficients prepared for depth `n`. -/
def sinComputableWithCoeffs (I : IntervalRat) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  let polyVal := evalTaylorSeries coeffs I
  let remainder := sinRemainderBoundComputable I n
  let raw := add polyVal remainder
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw

theorem sinComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    sinComputableWithCoeffs I n (sinTaylorCoeffs n) = sinComputable I n := by
  simp [sinComputableWithCoeffs, sinComputable]

/-! ### Computable cos via Taylor series -/

/-- Taylor coefficients for cos: 1, 0, -1/2, 0, 1/24, 0, ... -/
def cosTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 0 then  -- even terms only
      ((-1 : ℚ) ^ (i / 2)) / ratFactorial i
    else 0)

/-- Computable cos remainder bound.
    Since |cos^{(k)}(x)| ≤ 1 for all k, x, the remainder is bounded by |x|^{n+1}/(n+1)! -/
def cosRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  let R := r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hR : 0 ≤ R := by
      apply div_nonneg
      · apply pow_nonneg hr
      · exact Nat.cast_nonneg _
    linarith⟩

/-- Computable interval enclosure for cos using Taylor series.

    cos(x) = ∑_{k=0}^{n/2} (-1)^k x^{2k}/(2k)! + R
    where |R| ≤ |x|^{n+1}/(n+1)! since all derivatives of cos are bounded by 1.

    We intersect with [-1, 1] for tighter bounds on small intervals. -/
def cosComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coeffs := cosTaylorCoeffs n
  let polyVal := evalTaylorSeries coeffs I
  let remainder := cosRemainderBoundComputable I n
  let raw := add polyVal remainder
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw  -- Should not happen for valid inputs

/-- Interval cosine using Taylor coefficients prepared for depth `n`. -/
def cosComputableWithCoeffs (I : IntervalRat) (n : ℕ) (coeffs : List ℚ) : IntervalRat :=
  let polyVal := evalTaylorSeries coeffs I
  let remainder := cosRemainderBoundComputable I n
  let raw := add polyVal remainder
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => raw

theorem cosComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    cosComputableWithCoeffs I n (cosTaylorCoeffs n) = cosComputable I n := by
  simp [cosComputableWithCoeffs, cosComputable]

/-! ### Computable sinh and cosh via exp -/

/-- Computable interval enclosure for sinh at a single rational point.
    Uses the definition sinh(q) = (exp(q) - exp(-q)) / 2. -/
def sinhPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let expPos := expPointComputable q n
  let expNeg := expPointComputable (-q) n
  -- sinh(q) = (exp(q) - exp(-q)) / 2
  -- Lower bound: (expPos.lo - expNeg.hi) / 2
  -- Upper bound: (expPos.hi - expNeg.lo) / 2
  let sinhLo := (expPos.lo - expNeg.hi) / 2
  let sinhHi := (expPos.hi - expNeg.lo) / 2
  if h : sinhLo ≤ sinhHi then
    ⟨sinhLo, sinhHi, h⟩
  else
    ⟨min sinhLo sinhHi, max sinhLo sinhHi, @min_le_max _ _ sinhLo sinhHi⟩

/-- Computable interval enclosure for cosh at a single rational point.
    Uses the definition cosh(q) = (exp(q) + exp(-q)) / 2. -/
def coshPointComputable (q : ℚ) (n : ℕ := 10) : IntervalRat :=
  let expPos := expPointComputable q n
  let expNeg := expPointComputable (-q) n
  -- cosh(q) = (exp(q) + exp(-q)) / 2
  -- Lower bound: (expPos.lo + expNeg.lo) / 2
  -- Upper bound: (expPos.hi + expNeg.hi) / 2
  let coshLo := (expPos.lo + expNeg.lo) / 2
  let coshHi := (expPos.hi + expNeg.hi) / 2
  -- cosh ≥ 1 always, so ensure lower bound is at least 1
  let safeLo := max 1 coshLo
  if h : safeLo ≤ coshHi then
    ⟨safeLo, coshHi, h⟩
  else
    ⟨1, max 2 coshHi, by
      have h1 : (1 : ℚ) ≤ 2 := by norm_num
      exact le_trans h1 (le_max_left _ _)⟩

/-- The lower bound of coshPointComputable is always at least 1. -/
theorem coshPointComputable_lo_ge_one (q : ℚ) (n : ℕ) : 1 ≤ (coshPointComputable q n).lo := by
  simp only [coshPointComputable]
  split_ifs with h
  · exact le_max_left 1 _
  · exact le_refl 1

/-- Computable interval enclosure for sinh using exp with endpoint evaluation.

    sinh(x) = (exp(x) - exp(-x)) / 2
    Since sinh is strictly monotone increasing, sinh([a,b]) = [sinh(a), sinh(b)].
    We use endpoint evaluation for tight bounds. -/
def sinhComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  -- sinh is strictly monotone increasing, so evaluate at endpoints
  let sinhLo := sinhPointComputable I.lo n
  let sinhHi := sinhPointComputable I.hi n
  hull sinhLo sinhHi

/-- Computable interval enclosure for cosh using exp with endpoint evaluation.

    cosh(x) = (exp(x) + exp(-x)) / 2
    cosh has minimum 1 at x = 0, and is symmetric: cosh(-x) = cosh(x).
    - cosh is decreasing on (-∞, 0]
    - cosh is increasing on [0, ∞)

    We use endpoint evaluation with monotonicity for tight bounds. -/
def coshComputable (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let coshLo := coshPointComputable I.lo n
  let coshHi := coshPointComputable I.hi n
  if 0 ≤ I.lo then
    -- Interval is non-negative: cosh is increasing, so [cosh(lo), cosh(hi)]
    hull coshLo coshHi
  else if I.hi ≤ 0 then
    -- Interval is non-positive: cosh is decreasing, so [cosh(hi), cosh(lo)]
    hull coshHi coshLo
  else
    -- Interval contains 0: minimum is 1 at x=0, max is at whichever endpoint is farther
    let maxEndpoint := hull coshLo coshHi
    ⟨1, maxEndpoint.hi, by
      -- coshPointComputable ensures lower bound ≥ 1 via max 1 _
      have hlo_ge1 := coshPointComputable_lo_ge_one I.lo n
      have hhi_ge1 := coshPointComputable_lo_ge_one I.hi n
      calc (1 : ℚ) ≤ min (coshPointComputable I.lo n).lo (coshPointComputable I.hi n).lo :=
          le_min hlo_ge1 hhi_ge1
        _ = maxEndpoint.lo := rfl
        _ ≤ maxEndpoint.hi := maxEndpoint.le⟩

/-! ### FTIA for pow -/

/-- FTIA for interval power (binary exponentiation version) -/
theorem mem_pow {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    x ^ n ∈ pow I n := by
  match n with
  | 0 =>
    simp only [_root_.pow_zero, pow, mem_def, singleton]
    norm_num
  | 1 =>
    simp only [_root_.pow_one, pow]
    exact hx
  | n + 2 =>
    have ih_half := mem_pow hx ((n + 2) / 2)
    have h_sq := mem_mul ih_half ih_half
    change x ^ (n + 2) ∈ pow I (n + 2)
    unfold pow
    split
    · -- even case: x^(n+2) = (x^half)^2
      next heven =>
      have := beq_iff_eq.mp heven
      rw [show x ^ (n + 2) = x ^ ((n + 2) / 2) * x ^ ((n + 2) / 2) from by
        rw [← _root_.pow_add]; congr 1; omega]
      exact h_sq
    · -- odd case: x^(n+2) = x * (x^half)^2
      next heven =>
      have hodd : (n + 2) % 2 ≠ 0 := fun h => heven (beq_iff_eq.mpr h)
      rw [show x ^ (n + 2) = x * (x ^ ((n + 2) / 2) * x ^ ((n + 2) / 2)) from by
        rw [← _root_.pow_add, ← mul_comm, ← _root_.pow_succ]; congr 1; omega]
      exact mem_mul hx h_sq
termination_by n

/-! ### Helper lemmas for Taylor series membership -/

/-- Any x in I has |x| ≤ maxAbs I -/
theorem abs_le_maxAbs {x : ℝ} {I : IntervalRat} (hx : x ∈ I) : |x| ≤ maxAbs I := by
  simp only [mem_def, maxAbs] at *
  have hlo : -(max |I.lo| |I.hi|) ≤ I.lo := by
    calc -(max |I.lo| |I.hi|) ≤ -|I.lo| := neg_le_neg (le_max_left _ _)
      _ ≤ I.lo := neg_abs_le _
  have hhi : I.hi ≤ max |I.lo| |I.hi| := le_trans (le_abs_self _) (le_max_right _ _)
  rw [abs_le]
  constructor
  · calc (-(max |I.lo| |I.hi| : ℚ) : ℝ) ≤ I.lo := by exact_mod_cast hlo
      _ ≤ x := hx.1
  · calc x ≤ I.hi := hx.2
      _ ≤ max |I.lo| |I.hi| := by exact_mod_cast hhi

/-- If |x| ≤ R for nonnegative R, then x ∈ [-R, R].
    This is the key micro-lemma for embedding Lagrange remainder bounds into intervals. -/
theorem abs_le_mem_symmetric_interval {x : ℝ} {R : ℚ} (hR : 0 ≤ R) (h : |x| ≤ R) :
    x ∈ (⟨-R, R, by linarith⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  constructor
  · have := neg_abs_le x; linarith
  · exact le_trans (le_abs_self x) h

/-- Domain setup for Taylor theorem: if |x| ≤ r for nonnegative r,
    then x ∈ [-r, r] as an Icc with the required inequalities. -/
theorem domain_from_abs_bound {x : ℝ} {r : ℚ} (_hr : 0 ≤ r) (habs : |x| ≤ r) :
    x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) := by
  simp only [Set.mem_Icc, Rat.cast_neg]
  exact abs_le.mp habs

/-- Combined domain setup from interval membership. -/
theorem domain_from_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    let r := maxAbs I
    (0 : ℝ) ≤ r ∧ |x| ≤ r ∧ x ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ) ∧
    ((-r : ℚ) : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ (r : ℚ) ∧ ((-r : ℚ) : ℝ) ≤ r := by
  have hr_nonneg : 0 ≤ maxAbs I := le_max_of_le_left (abs_nonneg I.lo)
  have habs_x := abs_le_maxAbs hx
  have hr_nonneg_real : (0 : ℝ) ≤ maxAbs I := by exact_mod_cast hr_nonneg
  have hdom := domain_from_abs_bound hr_nonneg habs_x
  refine ⟨hr_nonneg_real, habs_x, hdom, ?_, hr_nonneg_real, ?_⟩
  · simp only [Rat.cast_neg]; linarith
  · simp only [Rat.cast_neg]; linarith

/-- Convert an absolute value bound |v| ≤ R to interval membership v ∈ [-R, R].
    This is the key micro-lemma for the final step of Taylor remainder bounds. -/
theorem remainder_to_interval {v : ℝ} {R : ℚ} (hbound : |v| ≤ R) :
    v ∈ (⟨-R, R, by
      have h1 : 0 ≤ |v| := abs_nonneg v
      have h2 : (0 : ℝ) ≤ (R : ℚ) := le_trans h1 hbound
      linarith [Rat.cast_nonneg.mp h2]⟩ : IntervalRat) := by
  simp only [mem_def, Rat.cast_neg]
  exact abs_le.mp hbound

/-- Key lemma: exp(ξ) ≤ 3^(⌈r⌉+1) for |ξ| ≤ r -/
theorem exp_bound_by_pow3 {r : ℚ} (_hr : 0 ≤ r) {ξ : ℝ} (hξ : |ξ| ≤ r) :
    Real.exp ξ ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
  -- e < 3, using Real.exp_one_lt_d9 which gives exp(1) < 2.7182818286
  have h3 : Real.exp 1 < 3 := by
    have h := Real.exp_one_lt_d9  -- exp(1) < 2.7182818286
    have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
    exact lt_trans h h2
  have hceil : (r : ℝ) ≤ Nat.ceil r := by
    have h : r ≤ (Nat.ceil r : ℚ) := Nat.le_ceil r
    exact_mod_cast h
  calc Real.exp ξ ≤ Real.exp |ξ| := Real.exp_le_exp.mpr (le_abs_self ξ)
    _ ≤ Real.exp r := Real.exp_le_exp.mpr hξ
    _ ≤ Real.exp (Nat.ceil r) := Real.exp_le_exp.mpr hceil
    _ = Real.exp 1 ^ (Nat.ceil r) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ 3 ^ (Nat.ceil r) := by
        rcases Nat.eq_zero_or_pos (Nat.ceil r) with hr0 | hrpos
        · simp [hr0]
        · exact le_of_lt (pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (Nat.pos_iff_ne_zero.mp hrpos))
    _ ≤ 3 ^ (Nat.ceil r + 1) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ _)

/-! ### Coefficient matching lemmas -/

/-- For exp, all iterated derivatives at 0 equal 1. -/
lemma iteratedDeriv_exp_zero (i : ℕ) : iteratedDeriv i Real.exp 0 = 1 := by
  simp [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-! ### Helper lemmas for Taylor series membership -/

/-- Polynomial sum starting at exponent `n`. -/
private def polySumFrom (coeffs : List ℚ) (x : ℝ) (n : ℕ) : ℝ :=
  ((coeffs.zipIdx n).map (fun (c, i) => (c : ℝ) * x ^ i)).sum

/-- Horner polynomial evaluation: the real value computed by Horner's method.
    `hornerVal [c₀, c₁, c₂] x = c₀ + x * (c₁ + x * (c₂ + x * 0)) = c₀ + c₁*x + c₂*x²` -/
private def hornerVal (coeffs : List ℚ) (x : ℝ) : ℝ :=
  coeffs.foldr (fun c acc => (c : ℝ) + x * acc) 0

/-- hornerVal equals polySumFrom at any starting index n, scaled by x^n.
    Specifically: x^n * hornerVal coeffs x = polySumFrom coeffs x n -/
private lemma hornerVal_mul_pow_eq_polySumFrom (coeffs : List ℚ) (x : ℝ) (n : ℕ) :
    x ^ n * hornerVal coeffs x = polySumFrom coeffs x n := by
  induction coeffs generalizing n with
  | nil => simp [hornerVal, polySumFrom]
  | cons c cs ih =>
    have hstep : hornerVal (c :: cs) x = (c : ℝ) + x * hornerVal cs x := by
      simp [hornerVal]
    have hunfold : polySumFrom (c :: cs) x n =
        (c : ℝ) * x ^ n + polySumFrom cs x (n + 1) := by
      simp [polySumFrom, List.zipIdx_cons]
    rw [hstep, mul_add, hunfold, ← ih (n + 1)]
    ring

/-- hornerVal equals polySumFrom at index 0. -/
private lemma hornerVal_eq_polySumFrom (coeffs : List ℚ) (x : ℝ) :
    hornerVal coeffs x = polySumFrom coeffs x 0 := by
  rw [← hornerVal_mul_pow_eq_polySumFrom coeffs x 0]
  simp

/-- Auxiliary lemma for Horner-style evaluation: the foldr contains hornerVal. -/
private lemma mem_horner_foldr {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (coeffs : List ℚ) :
    hornerVal coeffs x ∈
      coeffs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton 0) := by
  induction coeffs with
  | nil =>
      simp [hornerVal, mem_def, singleton]
  | cons c cs ih =>
      -- hornerVal (c :: cs) x = ↑c + x * hornerVal cs x
      -- foldr ... (c :: cs) = add (singleton c) (mul (foldr ... cs) I)
      change (c : ℝ) + x * hornerVal cs x ∈
        add (singleton c) (mul (cs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton
          0)) I)
      have hc : (c : ℝ) ∈ singleton c := by simp [mem_def, singleton]
      have hmul : hornerVal cs x * x ∈
        mul (cs.foldr (fun c acc => add (singleton c) (mul acc I)) (singleton 0)) I :=
        mem_mul ih hx
      have : (c : ℝ) + x * hornerVal cs x = (c : ℝ) + hornerVal cs x * x := by ring
      rw [this]
      exact mem_add hc hmul

/-- General FTIA for evalTaylorSeries (Horner version): if coeffs has length n+1, then
    ∑_{i=0}^{n} coeffs[i] * x^i ∈ evalTaylorSeries coeffs I for x ∈ I. -/
theorem mem_evalTaylorSeries {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (coeffs : List ℚ) :
    (coeffs.zipIdx.map (fun (c, i) => (c : ℝ) * x ^ i)).sum ∈ evalTaylorSeries coeffs I := by
  have hmem := mem_horner_foldr hx coeffs
  rw [hornerVal_eq_polySumFrom] at hmem
  simp only [evalTaylorSeries, polySumFrom] at *
  exact hmem

/-- Helper: (List.range n).map f).sum = ∑ i ∈ Finset.range n, f i -/
private lemma list_map_sum_eq_finset_sum {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ]
    rw [ih, add_comm]

/-- Helper: zipIdx of List.range just pairs each element with its index (which is itself) -/
private lemma zipIdx_range_map {α : Type*} (f : ℕ → ℕ → α) (n : ℕ) :
    (List.range n).zipIdx.map (fun p => f p.1 p.2) = (List.range n).map (fun i => f i i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.zipIdx_append, List.map_append, List.length_range]
    rw [ih]
    simp only [List.zipIdx_singleton, List.map_singleton, zero_add]

/-- The exp Taylor polynomial value matches our evalTaylorSeries.
    The proof shows that our list-based polynomial evaluation produces the same
    sum as the Finset.sum form used in Mathlib's Taylor theorem. -/
theorem mem_evalTaylorSeries_exp {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i ∈
      evalTaylorSeries (expTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (expTaylorCoeffs n)
  have hmem' :
      (((List.range (n + 1)).map (fun i => 1 / ratFactorial i)).zipIdx.map
          (fun p => (p.1 : ℝ) * x ^ p.2)).sum ∈
        evalTaylorSeries (expTaylorCoeffs n) I := by
    simpa [expTaylorCoeffs_eq_range_map] using hmem
  convert hmem' using 1
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (1 / i.factorial : ℝ) * x ^ i) (n + 1)]
  -- The two list maps are equal: both compute [1/0! * x^0, 1/1! * x^1, ...]
  -- LHS: (List.range (n+1)).map (fun i => 1/i! * x^i)
  -- RHS: zipIdx.map with Prod.map composition
  -- For List.range, zipIdx gives [(0,0), (1,1), ...], so they match
  congr 1
  symm
  -- The RHS has type (ℚ × ℕ) from Prod.map applied to zipIdx pairs
  -- Step 1: Simplify the composition
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map (fun i => (1 : ℚ) / ratFactorial i) id) =
      (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / ratFactorial p.1 : ℝ) * x ^
        p.2) := by
    apply List.map_congr_left
    intro ⟨a, b⟩ _
    simp only [Function.comp_apply, Prod.map_apply, id_eq, Rat.cast_div, Rat.cast_one]
  -- Step 2: Use zipIdx_range_map to eliminate zipIdx
  have h2 : (List.range (n + 1)).zipIdx.map (fun p : ℕ × ℕ => ((1 : ℚ) / ratFactorial p.1 : ℝ) * x
    ^ p.2) =
      (List.range (n + 1)).map (fun i => ((1 : ℚ) / ratFactorial i : ℝ) * x ^ i) := by
    convert! zipIdx_range_map (fun a b => ((1 : ℚ) / ratFactorial a : ℝ) * x ^ b) (n + 1) using 2
  -- Step 3: Simplify the casts
  have h3 : (List.range (n + 1)).map (fun i => ((1 : ℚ) / ratFactorial i : ℝ) * x ^ i) =
      (List.range (n + 1)).map (fun i => (1 / i.factorial : ℝ) * x ^ i) := by
    apply List.map_congr_left
    intro i _
    simp [ratFactorial]
  rw [h1, h2, h3]

/-- The iterated derivative of sin is sin, cos, -sin, -cos in a cycle of 4. -/
private lemma iteratedDeriv_sin (n : ℕ) : iteratedDeriv n Real.sin =
    if n % 4 = 0 then Real.sin
    else if n % 4 = 1 then Real.cos
    else if n % 4 = 2 then fun x => -Real.sin x
    else fun x => -Real.cos x := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv sin = cos
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte, Real.deriv_sin]; norm_num
    · -- n % 4 = 1: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of sin at 0 follows the pattern 0, 1, 0, -1, 0, 1, 0, -1, ... -/
private lemma iteratedDeriv_sin_zero (i : ℕ) : iteratedDeriv i Real.sin 0 =
    if i % 4 = 0 then 0
    else if i % 4 = 1 then 1
    else if i % 4 = 2 then 0
    else -1 := by
  rw [iteratedDeriv_sin]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.sin_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h3]; norm_num [Real.cos_zero]

/-- The sin Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i sin 0 = 0, 1, 0, -1, 0, 1, ... matches sinTaylorCoeffs. -/
theorem mem_evalTaylorSeries_sin {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (sinTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (sinTaylorCoeffs n)
  convert hmem using 1
  simp only [sinTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i)
    (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 1 then (-1 : ℚ) ^ ((i - 1) / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert! zipIdx_range_map
      (fun a b => ((if a % 2 = 1 then (-1 : ℚ) ^ ((a - 1) / 2) / a.factorial else 0 : ℚ) : ℝ) * x
        ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  -- Need: (iteratedDeriv i sin 0 / i!) * x^i = ((sinCoeff i) : ℝ) * x^i
  -- where sinCoeff i = if i % 2 = 1 then (-1)^((i-1)/2) / i! else 0
  congr 1
  -- Show iteratedDeriv i sin 0 / i! = sinCoeff i (as ℝ)
  rw [iteratedDeriv_sin_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h0, ↓reduceIte, zero_div, ite_eq_right hi_ne, Rat.cast_zero]
  · -- i % 4 = 1: i is odd, iteratedDeriv = 1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h1, ↓reduceIte, ite_eq_left hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    congr 1
    have heven : Even ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    exact heven.neg_one_pow
  · -- i % 4 = 2: i is even, iteratedDeriv = 0
    have hi_even : i % 2 = 0 := by omega
    have hi_ne : i % 2 ≠ 1 := by omega
    simp only [h2, ↓reduceIte, ite_eq_right hi_ne]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = -1, coefficient = (-1)^((i-1)/2) / i!
    have hi_odd : i % 2 = 1 := by omega
    simp only [h3, ite_eq_left hi_odd]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd ((i - 1) / 2) := ⟨(i - 1) / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num

/-- The iterated derivative of cos is cos, -sin, -cos, sin in a cycle of 4. -/
private lemma iteratedDeriv_cos (n : ℕ) : iteratedDeriv n Real.cos =
    if n % 4 = 0 then Real.cos
    else if n % 4 = 1 then fun x => -Real.sin x
    else if n % 4 = 2 then fun x => -Real.cos x
    else Real.sin := by
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_mod, ↓reduceIte]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h0 | h1 | h2 | h3
    · -- n % 4 = 0: deriv cos = -sin
      have hn1 : (n + 1) % 4 = 1 := by omega
      simp only [h0, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 1: deriv (-sin) = -cos
      have hn1 : (n + 1) % 4 = 2 := by omega
      simp only [h1, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 2: deriv (-cos) = sin
      have hn1 : (n + 1) % 4 = 3 := by omega
      simp only [h2, hn1, ↓reduceIte]; norm_num
    · -- n % 4 = 3: deriv sin = cos
      have hn1 : (n + 1) % 4 = 0 := by omega
      simp only [h3, hn1, ↓reduceIte]; norm_num

/-- The iterated derivative of cos at 0 follows the pattern 1, 0, -1, 0, 1, 0, ... -/
private lemma iteratedDeriv_cos_zero (i : ℕ) : iteratedDeriv i Real.cos 0 =
    if i % 4 = 0 then 1
    else if i % 4 = 1 then 0
    else if i % 4 = 2 then -1
    else 0 := by
  rw [iteratedDeriv_cos]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · simp only [h0, ↓reduceIte, Real.cos_zero]
  · simp only [h1, ↓reduceIte]; norm_num [Real.sin_zero]
  · simp only [h2, ↓reduceIte]; norm_num [Real.cos_zero]
  · simp only [h3]; norm_num [Real.sin_zero]

/-- The cos Taylor polynomial value matches our evalTaylorSeries.
    Key: iteratedDeriv i cos 0 = 1, 0, -1, 0, 1, 0, ... matches cosTaylorCoeffs. -/
theorem mem_evalTaylorSeries_cos {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i ∈
      evalTaylorSeries (cosTaylorCoeffs n) I := by
  have hmem := mem_evalTaylorSeries hx (cosTaylorCoeffs n)
  convert hmem using 1
  simp only [cosTaylorCoeffs, ratFactorial]
  rw [List.zipIdx_map]
  simp only [List.map_map]
  rw [← list_map_sum_eq_finset_sum (fun i => (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i)
    (n + 1)]
  congr 1
  symm
  -- Step 1: Simplify the RHS using zipIdx_range_map
  have h1 : (List.range (n + 1)).zipIdx.map
        ((fun p : ℚ × ℕ => (p.1 : ℝ) * x ^ p.2) ∘ Prod.map
          (fun i => if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0) id) =
      (List.range (n + 1)).map (fun i =>
        ((if i % 2 = 0 then (-1 : ℚ) ^ (i / 2) / i.factorial else 0 : ℚ) : ℝ) * x ^ i) := by
    convert! zipIdx_range_map
      (fun a b => ((if a % 2 = 0 then (-1 : ℚ) ^ (a / 2) / a.factorial else 0 : ℚ) : ℝ) * x ^ b)
      (n + 1) using 2
  rw [h1]
  -- Step 2: Show term-by-term equality
  apply List.map_congr_left
  intro i _
  congr 1
  -- Show iteratedDeriv i cos 0 / i! = cosCoeff i (as ℝ)
  rw [iteratedDeriv_cos_zero]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h0 | h1 | h2 | h3
  · -- i % 4 = 0: i is even, iteratedDeriv = 1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h0, ↓reduceIte, one_div, ite_eq_left hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have heven : Even (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [heven.neg_one_pow]
    ring
  · -- i % 4 = 1: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h1, ↓reduceIte, ite_eq_right hi_ne]
    norm_num
  · -- i % 4 = 2: i is even, iteratedDeriv = -1, coefficient = (-1)^(i/2) / i!
    have hi_even : i % 2 = 0 := by omega
    simp only [h2, ite_eq_left hi_even]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    have hodd : Odd (i / 2) := ⟨i / 2 / 2, by omega⟩
    rw [hodd.neg_one_pow]
    norm_num
  · -- i % 4 = 3: i is odd, iteratedDeriv = 0
    have hi_odd : i % 2 = 1 := by omega
    have hi_ne : i % 2 ≠ 0 := by omega
    simp only [h3, ite_eq_right hi_ne]
    norm_num

/-! ### Taylor remainder micro-lemmas -/

/-- Unified Taylor remainder bound for exp: given x ∈ I with r = maxAbs I,
    the Taylor remainder |exp x - poly(x)| ≤ 3^(⌈r⌉+1) * r^(n+1) / (n+1)!.
    This encapsulates the domain setup and remainder calculation. -/
theorem exp_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
    ∈ expRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := ((3 : ℚ) ^ (Nat.ceil r + 1) * r ^ (n + 1) / ratFactorial (n + 1))
  -- Apply Taylor theorem
  have hexp_smooth : ContDiff ℝ (n + 1) Real.exp := Real.contDiff_exp.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.exp y‖ ≤ Real.exp r := by
    intro y hy
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos
      y)]
    exact Real.exp_le_exp.mpr hy.2
  have hTaylor := taylor_remainder_bound hab h0a h0b hexp_smooth hderiv_bound
    (Real.exp_pos (r : ℚ)).le x hdom
  -- Compute remainder bound
  have hr_nonneg_rat : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
  have hexp_r_bound : Real.exp (r : ℚ) ≤ (3 : ℝ) ^ (Nat.ceil r + 1) := by
    apply exp_bound_by_pow3 hr_nonneg_rat
    rw [abs_of_nonneg hr_nonneg]
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : Real.exp (r : ℚ) * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero]
    calc Real.exp (r : ℚ) * |x| ^ (n + 1) / (n + 1).factorial
        ≤ (3 : ℝ) ^ (Nat.ceil r + 1) * (r : ℝ) ^ (n + 1) / (n + 1).factorial := by
          apply div_le_div_of_nonneg_right _ hfact_pos.le
          apply mul_le_mul hexp_r_bound hx_pow_bound (pow_nonneg (abs_nonneg x) _)
          apply pow_nonneg; norm_num
      _ = (R : ℝ) := by
          simp only [R, ratFactorial, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
            Rat.cast_natCast, Rat.cast_ofNat]
  -- Convert to interval membership
  simp only [expRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.exp x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for sin: given x ∈ I with r = maxAbs I,
    the Taylor remainder |sin x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |sin^(k)(x)| ≤ 1 for all k, x. -/
theorem sin_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
    ∈ sinRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))
  -- Apply Taylor theorem with M = 1
  have hsin_smooth : ContDiff ℝ (n + 1) Real.sin := Real.contDiff_sin.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.sin y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).1
  have hTaylor := taylor_remainder_bound hab h0a h0b hsin_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom
  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  -- Convert to interval membership
  simp only [sinRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.sin x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-- Unified Taylor remainder bound for cos: given x ∈ I with r = maxAbs I,
    the Taylor remainder |cos x - poly(x)| ≤ r^(n+1) / (n+1)!.
    Uses the fact that |cos^(k)(x)| ≤ 1 for all k, x. -/
theorem cos_taylor_remainder_in_interval {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x - ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
    ∈ cosRemainderBoundComputable I n := by
  -- Extract domain info
  have ⟨hr_nonneg, habs_x, hdom, h0a, h0b, hab⟩ := domain_from_mem hx
  set r := maxAbs I
  set R := (r ^ (n + 1) / ratFactorial (n + 1))
  -- Apply Taylor theorem with M = 1
  have hcos_smooth : ContDiff ℝ (n + 1) Real.cos := Real.contDiff_cos.of_le le_top
  have hderiv_bound : ∀ y ∈ Set.Icc ((-r : ℚ) : ℝ) (r : ℚ),
      ‖iteratedDeriv (n + 1) Real.cos y‖ ≤ 1 := by
    intro y _; exact (sin_cos_deriv_bound (n + 1) y).2
  have hTaylor := taylor_remainder_bound hab h0a h0b hcos_smooth hderiv_bound
    (by norm_num : (0 : ℝ) ≤ 1) x hdom
  -- Compute remainder bound
  have hx_pow_bound : |x| ^ (n + 1) ≤ (r : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) habs_x _
  have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hrem_bound : 1 * |x - 0| ^ (n + 1) / (n + 1).factorial ≤ (R : ℝ) := by
    simp only [sub_zero, one_mul]
    calc |x| ^ (n + 1) / (n + 1).factorial
        ≤ (r : ℝ) ^ (n + 1) / (n + 1).factorial :=
          div_le_div_of_nonneg_right hx_pow_bound hfact_pos.le
      _ = (R : ℝ) := by simp only [R, ratFactorial, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  -- Convert to interval membership
  simp only [cosRemainderBoundComputable, mem_def, ratFactorial]
  have h := hTaylor
  simp only [sub_zero, one_mul] at h hrem_bound
  rw [Real.norm_eq_abs] at h
  have hbound : |Real.cos x - ∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i| ≤ (R : ℝ) :=
    le_trans h hrem_bound
  have habs := abs_le.mp hbound
  simp only [R, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg] at habs ⊢
  exact habs

/-! ### FTIA for computable functions -/

private theorem mem_expPointComputableRaw (q : ℚ) (n : ℕ) :
    Real.exp q ∈ expPointComputableRaw q n := by
  simp only [expPointComputableRaw]
  have hq_mem : (q : ℝ) ∈ singleton q := mem_singleton q
  -- Strategy: exp q = poly(q) + remainder, with both in their respective intervals
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * (q :
    ℝ) ^ i
      ∈ evalTaylorSeries (expTaylorCoeffs n) (singleton q) := by
    have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * (q :
      ℝ) ^ i =
        ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * (q : ℝ) ^ i := by
      apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
    rw [hsum_eq]; exact mem_evalTaylorSeries_exp hq_mem n
  have hrem_mem := exp_taylor_remainder_in_interval hq_mem n
  have heq : Real.exp q = (∑ i ∈ Finset.range (n + 1),
      (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i) +
      (Real.exp q - ∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * (q : ℝ) ^ i) := by ring
  rw [heq]; exact mem_add hpoly_mem hrem_mem

/-- FTIA for single-point exp: Real.exp q ∈ expPointComputable q n -/
theorem mem_expPointComputable (q : ℚ) (n : ℕ) :
    Real.exp q ∈ expPointComputable q n := by
  simp only [expPointComputable]
  set k := expReduceK q
  set m : ℕ := (2:ℕ)^k
  set q' : ℚ := q / m
  have hbase : Real.exp q' ∈ expPointComputableRaw q' n :=
    mem_expPointComputableRaw q' n
  have hpow : (Real.exp q') ^ m ∈ pow (expPointComputableRaw q' n) m :=
    mem_pow hbase m
  have hm : (m:ℝ) ≠ 0 := by
    -- m = 2^k > 0
    exact_mod_cast (pow_ne_zero k (by decide : (2:ℕ) ≠ 0))
  have hq : (q : ℝ) = (m:ℝ) * (q' : ℝ) := by
    -- q' = q / m
    have hm' : (m:ℝ) ≠ 0 := hm
    calc
      (q:ℝ) = (m:ℝ) * ((q:ℝ) / (m:ℝ)) := by
        field_simp [hm']
      _ = (m:ℝ) * (q' : ℝ) := by
        simp [q', Rat.cast_div, Rat.cast_natCast]
  have hexp : Real.exp q = (Real.exp q') ^ m := by
    calc
      Real.exp q = Real.exp ((m:ℝ) * (q' : ℝ)) := by simp [hq]
      _ = (Real.exp (q' : ℝ)) ^ m := by
            -- exp (m * q') = (exp q')^m
            simpa [mul_comm] using (Real.exp_nat_mul (q' : ℝ) m)
  -- rewrite and apply membership
  simpa [hexp]

theorem mem_expComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.exp x ∈ expComputable I n := by
  simp only [expComputable]
  split_ifs with h
  · -- Interval doesn't cross 0: use endpoint evaluation and monotonicity
    -- exp is monotone increasing, so exp([lo, hi]) ⊆ hull(exp(lo), exp(hi))
    have hlo_mem := mem_expPointComputable I.lo n
    have hhi_mem := mem_expPointComputable I.hi n
    -- Since x ∈ [lo, hi] and exp is monotone, exp(x) ∈ [exp(lo), exp(hi)]
    -- The hull contains both exp(lo) and exp(hi), so it contains exp(x)
    rcases h with ⟨hhi_neg⟩ | ⟨hlo_pos⟩
    · -- Case: hi ≤ 0 (negative interval)
      -- exp(lo) ≤ exp(x) ≤ exp(hi) by monotonicity
      have hx_le_hi : x ≤ I.hi := hx.2
      have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
      have hexp_mono1 : Real.exp x ≤ Real.exp I.hi := Real.exp_le_exp.mpr hx_le_hi
      have hexp_mono2 : Real.exp I.lo ≤ Real.exp x := Real.exp_le_exp.mpr hlo_le_x
      -- exp(x) is between exp(lo) and exp(hi), both of which are in the hull
      simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
      constructor
      · -- lower bound: min(expLo.lo, expHi.lo) ≤ exp(x)
        calc (min (expPointComputable I.lo n).lo (expPointComputable I.hi n).lo : ℝ)
            ≤ (expPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
          _ ≤ Real.exp I.lo := hlo_mem.1
          _ ≤ Real.exp x := hexp_mono2
      · -- upper bound: exp(x) ≤ max(expLo.hi, expHi.hi)
        calc Real.exp x ≤ Real.exp I.hi := hexp_mono1
          _ ≤ (expPointComputable I.hi n).hi := hhi_mem.2
          _ ≤ max ((expPointComputable I.lo n).hi : ℝ) ((expPointComputable I.hi n).hi : ℝ) :=
            le_max_right _ _
    · -- Case: 0 ≤ lo (positive interval) - same argument
      have hx_le_hi : x ≤ I.hi := hx.2
      have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
      have hexp_mono1 : Real.exp x ≤ Real.exp I.hi := Real.exp_le_exp.mpr hx_le_hi
      have hexp_mono2 : Real.exp I.lo ≤ Real.exp x := Real.exp_le_exp.mpr hlo_le_x
      simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
      constructor
      · calc (min (expPointComputable I.lo n).lo (expPointComputable I.hi n).lo : ℝ)
            ≤ (expPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
          _ ≤ Real.exp I.lo := hlo_mem.1
          _ ≤ Real.exp x := hexp_mono2
      · calc Real.exp x ≤ Real.exp I.hi := hexp_mono1
          _ ≤ (expPointComputable I.hi n).hi := hhi_mem.2
          _ ≤ max ((expPointComputable I.lo n).hi : ℝ) ((expPointComputable I.hi n).hi : ℝ) :=
            le_max_right _ _
  · -- Interval crosses 0: use standard Taylor
    -- Strategy: exp x = poly(x) + remainder, with both in their respective intervals
    have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i
        ∈ evalTaylorSeries (expTaylorCoeffs n) I := by
      have hsum_eq : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.exp 0 / i.factorial) * x ^
        i =
          ∑ i ∈ Finset.range (n + 1), (1 / i.factorial : ℝ) * x ^ i := by
        apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_exp_zero, one_div]
      rw [hsum_eq]; exact mem_evalTaylorSeries_exp hx n
    have hrem_mem := exp_taylor_remainder_in_interval hx n
    have heq : Real.exp x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) +
        (Real.exp x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.exp 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem

/-- FTIA for sinComputable: Real.sin x ∈ sinComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound sin ∈ [-1, 1]. -/
theorem mem_sinComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sin x ∈ sinComputable I n := by
  simp only [sinComputable]
  -- Strategy: sin x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (sinTaylorCoeffs n) I := mem_evalTaylorSeries_sin hx n
  -- Remainder part ∈ sinRemainderBoundComputable (via micro-lemma)
  have hrem_mem := sin_taylor_remainder_in_interval hx n
  -- Raw interval membership: sin x ∈ poly + remainder
  have hraw_mem : Real.sin x ∈ add (evalTaylorSeries (sinTaylorCoeffs n) I)
      (sinRemainderBoundComputable I n) := by
    have heq : Real.sin x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) +
        (Real.sin x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.sin 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem
  -- Global bound: sin x ∈ [-1, 1]
  have hglobal_mem : Real.sin x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_sin x
    · simp only [Rat.cast_one]; exact Real.sin_le_one x
  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

/-- FTIA for cosComputable: Real.cos x ∈ cosComputable I n for any x ∈ I.

    The proof uses the Taylor remainder micro-lemma and the global bound cos ∈ [-1, 1]. -/
theorem mem_cosComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cos x ∈ cosComputable I n := by
  simp only [cosComputable]
  -- Strategy: cos x = poly(x) + remainder, intersected with global bound [-1, 1]

  -- Polynomial part ∈ evalTaylorSeries
  have hpoly_mem : ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i
      ∈ evalTaylorSeries (cosTaylorCoeffs n) I := mem_evalTaylorSeries_cos hx n
  -- Remainder part ∈ cosRemainderBoundComputable (via micro-lemma)
  have hrem_mem := cos_taylor_remainder_in_interval hx n
  -- Raw interval membership: cos x ∈ poly + remainder
  have hraw_mem : Real.cos x ∈ add (evalTaylorSeries (cosTaylorCoeffs n) I)
      (cosRemainderBoundComputable I n) := by
    have heq : Real.cos x = (∑ i ∈ Finset.range (n + 1),
        (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) +
        (Real.cos x - ∑ i ∈ Finset.range (n + 1),
          (iteratedDeriv i Real.cos 0 / i.factorial) * x ^ i) := by ring
    rw [heq]; exact mem_add hpoly_mem hrem_mem
  -- Global bound: cos x ∈ [-1, 1]
  have hglobal_mem : Real.cos x ∈ (⟨-1, 1, by norm_num⟩ : IntervalRat) := by
    simp only [mem_def]; constructor
    · simp only [Rat.cast_neg, Rat.cast_one]; exact Real.neg_one_le_cos x
    · simp only [Rat.cast_one]; exact Real.cos_le_one x
  -- Intersect and conclude
  have ⟨K, hK_eq, hK_mem⟩ := mem_intersect hraw_mem hglobal_mem
  simp only [hK_eq]; exact hK_mem

/-- FTIA for sinhPointComputable: Real.sinh q ∈ sinhPointComputable q n -/
theorem mem_sinhPointComputable (q : ℚ) (n : ℕ) :
    Real.sinh q ∈ sinhPointComputable q n := by
  simp only [sinhPointComputable]
  have hexp_pos := mem_expPointComputable q n
  have hexp_neg := mem_expPointComputable (-q) n
  rw [Real.sinh_eq]
  simp only [Rat.cast_neg] at hexp_neg
  simp only [mem_def] at hexp_pos hexp_neg ⊢
  obtain ⟨hexp_pos_lo, hexp_pos_hi⟩ := hexp_pos
  obtain ⟨hexp_neg_lo, hexp_neg_hi⟩ := hexp_neg
  split_ifs with h
  · constructor <;> { simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]; linarith }
  · -- Fallback case: use min/max bounds
    constructor
    · simp only [Rat.cast_min, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
      apply min_le_of_left_le; linarith
    · simp only [Rat.cast_max, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
      apply le_max_of_le_right; linarith

/-- FTIA for coshPointComputable: Real.cosh q ∈ coshPointComputable q n -/
theorem mem_coshPointComputable (q : ℚ) (n : ℕ) :
    Real.cosh q ∈ coshPointComputable q n := by
  simp only [coshPointComputable]
  have hexp_pos := mem_expPointComputable q n
  have hexp_neg := mem_expPointComputable (-q) n
  rw [Real.cosh_eq]
  simp only [Rat.cast_neg] at hexp_neg
  simp only [mem_def] at hexp_pos hexp_neg ⊢
  obtain ⟨hexp_pos_lo, hexp_pos_hi⟩ := hexp_pos
  obtain ⟨hexp_neg_lo, hexp_neg_hi⟩ := hexp_neg
  -- cosh q ≥ 1 always (AM-GM)
  have hcosh_ge_one : 1 ≤ (Real.exp q + Real.exp (-(q : ℝ))) / 2 := by
    have h1 : Real.exp q > 0 := Real.exp_pos q
    have h2 : Real.exp (-(q : ℝ)) > 0 := Real.exp_pos (-(q : ℝ))
    have hprod : Real.exp q * Real.exp (-(q : ℝ)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have ham : Real.exp q + Real.exp (-(q : ℝ)) ≥ 2 := by nlinarith [sq_nonneg (Real.exp q -
      Real.exp (-(q : ℝ))), hprod]
    linarith
  split_ifs with h
  · constructor
    · -- Lower bound: max 1 coshLo ≤ cosh q
      simp only [Rat.cast_max, Rat.cast_one, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
      apply max_le
      · exact hcosh_ge_one
      · linarith
    · -- Upper bound
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
      linarith
  · -- Fallback
    constructor
    · simp only [Rat.cast_one]
      exact hcosh_ge_one
    · simp only [Rat.cast_max, Rat.cast_ofNat, Rat.cast_div, Rat.cast_add]
      apply le_max_of_le_right
      linarith

/-- FTIA for sinhComputable: Real.sinh x ∈ sinhComputable I n for any x ∈ I.

    Uses endpoint evaluation and monotonicity of sinh. -/
theorem mem_sinhComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.sinh x ∈ sinhComputable I n := by
  simp only [sinhComputable]
  -- sinh is strictly monotone increasing
  have hsinh_mono : StrictMono Real.sinh := Real.sinh_strictMono
  have hlo_mem := mem_sinhPointComputable I.lo n
  have hhi_mem := mem_sinhPointComputable I.hi n
  -- x ∈ [lo, hi] implies sinh(lo) ≤ sinh(x) ≤ sinh(hi)
  have hlo_le_x : (I.lo : ℝ) ≤ x := hx.1
  have hx_le_hi : x ≤ (I.hi : ℝ) := hx.2
  have hsinh_lo_le : Real.sinh I.lo ≤ Real.sinh x :=
    hsinh_mono.monotone hlo_le_x
  have hsinh_x_le_hi : Real.sinh x ≤ Real.sinh I.hi :=
    hsinh_mono.monotone hx_le_hi
  -- sinh x is between sinh(lo) and sinh(hi), which are in the hull
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (sinhPointComputable I.lo n).lo (sinhPointComputable I.hi n).lo : ℝ)
        ≤ (sinhPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.sinh I.lo := hlo_mem.1
      _ ≤ Real.sinh x := hsinh_lo_le
  · calc Real.sinh x ≤ Real.sinh I.hi := hsinh_x_le_hi
      _ ≤ (sinhPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((sinhPointComputable I.lo n).hi : ℝ) ((sinhPointComputable I.hi n).hi : ℝ) :=
        le_max_right _ _

/-- FTIA for coshComputable: Real.cosh x ∈ coshComputable I n for any x ∈ I.

    Uses endpoint evaluation and monotonicity properties of cosh. -/
theorem mem_coshComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ) :
    Real.cosh x ∈ coshComputable I n := by
  simp only [coshComputable]
  have hlo_mem := mem_coshPointComputable I.lo n
  have hhi_mem := mem_coshPointComputable I.hi n
  -- cosh x ≥ 1 always (AM-GM)
  have hcosh_ge_one : 1 ≤ Real.cosh x := Real.one_le_cosh x
  -- Key lemma: cosh a ≤ cosh b iff |a| ≤ |b|
  split_ifs with h1 h2
  · -- Case: 0 ≤ I.lo (non-negative interval, cosh is increasing)
    have hlo_nonneg : (0 : ℝ) ≤ I.lo := by exact_mod_cast h1
    have hx_nonneg : 0 ≤ x := le_trans hlo_nonneg hx.1
    have hhi_nonneg : (0 : ℝ) ≤ I.hi := le_trans hlo_nonneg (by exact_mod_cast I.le)
    -- For 0 ≤ a ≤ b: |a| = a ≤ b = |b|, so cosh(a) ≤ cosh(b)
    have hcosh_lo_le : Real.cosh I.lo ≤ Real.cosh x := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg hlo_nonneg, abs_of_nonneg hx_nonneg]
      exact hx.1
    have hcosh_x_le_hi : Real.cosh x ≤ Real.cosh I.hi := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hhi_nonneg]
      exact hx.2
    simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
    constructor
    · calc (min (coshPointComputable I.lo n).lo (coshPointComputable I.hi n).lo : ℝ)
          ≤ (coshPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
        _ ≤ Real.cosh I.lo := hlo_mem.1
        _ ≤ Real.cosh x := hcosh_lo_le
    · calc Real.cosh x ≤ Real.cosh I.hi := hcosh_x_le_hi
        _ ≤ (coshPointComputable I.hi n).hi := hhi_mem.2
        _ ≤ max ((coshPointComputable I.lo n).hi : ℝ) ((coshPointComputable I.hi n).hi : ℝ) :=
          le_max_right _ _
  · -- Case: I.hi ≤ 0 (non-positive interval, cosh is decreasing)
    have hhi_nonpos : I.hi ≤ (0 : ℝ) := by exact_mod_cast h2
    have hx_nonpos : x ≤ 0 := le_trans hx.2 hhi_nonpos
    have hlo_nonpos : (I.lo : ℝ) ≤ 0 := le_trans (by exact_mod_cast I.le) hhi_nonpos
    -- For a ≤ b ≤ 0: |a| = -a ≥ -b = |b|, so cosh(a) ≥ cosh(b)
    have hcosh_hi_le : Real.cosh I.hi ≤ Real.cosh x := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonpos hhi_nonpos, abs_of_nonpos hx_nonpos]
      linarith [hx.2]
    have hcosh_x_le_lo : Real.cosh x ≤ Real.cosh I.lo := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonpos hx_nonpos, abs_of_nonpos hlo_nonpos]
      linarith [hx.1]
    simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
    constructor
    · calc (min (coshPointComputable I.hi n).lo (coshPointComputable I.lo n).lo : ℝ)
          ≤ (coshPointComputable I.hi n).lo := by exact_mod_cast min_le_left _ _
        _ ≤ Real.cosh I.hi := hhi_mem.1
        _ ≤ Real.cosh x := hcosh_hi_le
    · calc Real.cosh x ≤ Real.cosh I.lo := hcosh_x_le_lo
        _ ≤ (coshPointComputable I.lo n).hi := hlo_mem.2
        _ ≤ max ((coshPointComputable I.hi n).hi : ℝ) ((coshPointComputable I.lo n).hi : ℝ) :=
          le_max_right _ _
  · -- Case: interval contains 0, minimum is 1
    simp only [mem_def, Rat.cast_one, hull, Rat.cast_max]
    constructor
    · exact hcosh_ge_one
    · -- Upper bound is max of endpoint cosh values
      push Not at h1 h2
      have hhi_pos : (0 : ℝ) < I.hi := by exact_mod_cast h2
      have hlo_neg : (I.lo : ℝ) < 0 := by exact_mod_cast h1
      have hmax_bound : Real.cosh x ≤ max (Real.cosh I.lo) (Real.cosh I.hi) := by
        -- x is between lo and hi, and interval contains 0
        by_cases! hx_nonneg : 0 ≤ x
        · -- x ≥ 0: cosh(x) ≤ cosh(hi) since 0 ≤ x ≤ hi means |x| ≤ |hi|
          apply le_max_of_le_right
          rw [Real.cosh_le_cosh]
          rw [abs_of_nonneg hx_nonneg, abs_of_nonneg (le_of_lt hhi_pos)]
          exact hx.2
        · -- x < 0: cosh(x) ≤ cosh(lo) since lo ≤ x < 0 means |x| ≤ |lo|
          apply le_max_of_le_left
          rw [Real.cosh_le_cosh]
          rw [abs_of_neg hx_nonneg, abs_of_neg hlo_neg]
          linarith [hx.1]
      calc Real.cosh x ≤ max (Real.cosh I.lo) (Real.cosh I.hi) := hmax_bound
        _ ≤ max ((coshPointComputable I.lo n).hi : ℝ) ((coshPointComputable I.hi n).hi : ℝ) := by
            apply max_le_max
            · exact hlo_mem.2
            · exact hhi_mem.2

/-! ### Computable atanh via Taylor series

For |y| < 1, atanh(y) = y + y³/3 + y⁵/5 + ...
We compute this series for y ∈ [-1/3, 1/3] where it converges rapidly.
-/

/-- Taylor coefficients for atanh: 0, 1, 0, 1/3, 0, 1/5, ...
    atanh(y) = Σ y^(2k+1)/(2k+1) = y + y³/3 + y⁵/5 + ... -/
def atanhTaylorCoeffs (n : ℕ) : List ℚ :=
  let f : ℕ → ℚ := fun i => if i % 2 = 1 then 1 / i else 0
  (List.range (n + 1)).map f

/-- Computable atanh remainder bound.
    For |y| ≤ r < 1, the remainder after n terms is bounded by r^(n+1)/(1 - r²).
    We use a conservative bound: r^(n+1) / ((n+1) * (1 - r)) for simplicity. -/
def atanhRemainderBoundComputable (r : ℚ) (n : ℕ) : IntervalRat :=
  let r' := |r|  -- Use absolute value to ensure non-negativity
  if h : r' ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for bad input
  else
    let R := r' ^ (n + 1) / (1 - r')
    ⟨-R, R, by
      have hr : r' < 1 := not_le.mp h
      have hr_nonneg : 0 ≤ r' := abs_nonneg r
      have hdenom_pos : 0 < 1 - r' := by linarith
      have hR_nonneg : 0 ≤ R := by
        apply div_nonneg
        · apply pow_nonneg hr_nonneg
        · linarith
      linarith⟩

/-- Computable interval enclosure for atanh at a single rational point.
    Requires |q| < 1 for convergence. For |q| ≤ 1/3, this is very accurate. -/
def atanhPointComputable (q : ℚ) (n : ℕ := 15) : IntervalRat :=
  let r := |q|
  if r ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback
  else
    let I := singleton q
    let coeffs := atanhTaylorCoeffs n
    let polyVal := evalTaylorSeries coeffs I
    let remainder := atanhRemainderBoundComputable r n
    add polyVal remainder

/-- Point `atanh` using Taylor coefficients prepared for depth `n`. -/
def atanhPointComputableWithCoeffs (q : ℚ) (n : ℕ)
    (coeffs : List ℚ) : IntervalRat :=
  let r := |q|
  if r ≥ 1 then
    ⟨-1000, 1000, by norm_num⟩
  else
    let I := singleton q
    let polyVal := evalTaylorSeries coeffs I
    let remainder := atanhRemainderBoundComputable r n
    add polyVal remainder

theorem atanhPointComputableWithCoeffs_eq (q : ℚ) (n : ℕ) :
    atanhPointComputableWithCoeffs q n (atanhTaylorCoeffs n) =
      atanhPointComputable q n := by
  simp [atanhPointComputableWithCoeffs, atanhPointComputable]

/-- The atanh series: atanh(x) = Σ_{k=0}^∞ x^(2k+1)/(2k+1) for |x| < 1.
    Derived from Mathlib's hasSum_log_sub_log_of_abs_lt_one. -/
theorem Real.atanh_hasSum' {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ (2 * k + 1) / (2 * k + 1)) (Real.atanh x) := by
  have hlog := Real.hasSum_log_sub_log_of_abs_lt_one hx
  have h1 : 0 < 1 + x := by linarith [(abs_lt.mp hx).1]
  have h2 : 0 < 1 - x := by linarith [(abs_lt.mp hx).2]
  have h_eq : Real.atanh x = (1 / 2) * (Real.log (1 + x) - Real.log (1 - x)) := by
    rw [Real.atanh, Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
  rw [h_eq]
  convert! hlog.mul_left (1 / 2) using 1
  funext k
  field_simp

/-- The atanh Taylor polynomial membership: the partial sum of atanh coefficients at q
    is in evalTaylorSeries (atanhTaylorCoeffs n) (singleton q). -/
theorem mem_evalTaylorSeries_atanh {q : ℚ} (n : ℕ) :
    ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum ∈
      evalTaylorSeries (atanhTaylorCoeffs n) (singleton q) :=
  mem_evalTaylorSeries (mem_singleton q) (atanhTaylorCoeffs n)

/-- The atanh Taylor remainder bound: for |q| < 1, the remainder after n terms is bounded.
    The remainder is |Σ_{k: 2k+1 > n} q^(2k+1)/(2k+1)| ≤ |q|^(n+1)/(1-|q|). -/
private theorem atanhTaylorCoeffs_sum (q : ℚ) (n : ℕ) :
    ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) ↦ (c : ℝ) * (q : ℝ) ^ i)).sum =
      ∑ k ∈ Finset.range ((n + 1) / 2), (q : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  let term := fun k : ℕ ↦ (q : ℝ) ^ (2 * k + 1) / (2 * k + 1)
  let m := (n + 1) / 2
  -- Step 1: Convert the list sum to a Finset sum over indices.
  have hlist :
      ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum =
      ∑ i ∈ Finset.range (n + 1),
        ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i := by
    simp only [atanhTaylorCoeffs, one_div]
    rw [List.zipIdx_map]
    simp only [List.map_map]
    -- Simplify the composition after zipIdx_map.
    have h1 :
        (List.range (n + 1)).zipIdx.map
            ((fun p : ℚ × ℕ => (p.1 : ℝ) * (q : ℝ) ^ p.2) ∘
              Prod.map (fun i : ℕ => if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0) id) =
          (List.range (n + 1)).zipIdx.map
            (fun p : ℕ × ℕ =>
              ((if p.1 % 2 = 1 then ((p.1 : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ p.2) := by
      apply List.map_congr_left
      intro ⟨a, b⟩ _
      simp [Function.comp, Prod.map_apply]
    -- Replace zipIdx over range with a direct map on indices.
    have h2 :
        (List.range (n + 1)).zipIdx.map
            (fun p : ℕ × ℕ =>
              ((if p.1 % 2 = 1 then ((p.1 : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ p.2) =
          (List.range (n + 1)).map
            (fun i : ℕ =>
              ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i) := by
      convert! zipIdx_range_map
        (fun a b =>
          ((if a % 2 = 1 then ((a : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ b) (n + 1) using 2
    rw [h1, h2]
    exact list_map_sum_eq_finset_sum
      (fun i : ℕ =>
        ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i) (n + 1)
  -- Step 2: Filter to odd indices (even indices contribute zero).
  have hsum_filter :
      ∑ i ∈ Finset.range (n + 1),
          ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i =
        ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
          (q : ℝ) ^ i / i := by
    have hterm :
        ∀ i : ℕ,
          ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i =
            if i % 2 = 1 then (q : ℝ) ^ i / i else 0 := by
      intro i
      by_cases hodd : i % 2 = 1
      · simp [hodd, div_eq_mul_inv, Rat.cast_inv, Rat.cast_natCast,
          mul_comm]
      · simp [hodd]
    calc
      ∑ i ∈ Finset.range (n + 1),
          ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i
          =
          ∑ i ∈ Finset.range (n + 1),
            (if i % 2 = 1 then (q : ℝ) ^ i / i else 0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hterm i
      _ =
          ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
            (q : ℝ) ^ i / i := by
              symm
              exact (Finset.sum_filter
                (s := Finset.range (n + 1))
                (f := fun i => (q : ℝ) ^ i / i)
                (p := fun i => i % 2 = 1))
  -- Step 3: Reindex odd indices by k with i = 2k+1.
  have hsum_reindex :
      ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
          (q : ℝ) ^ i / i =
        ∑ k ∈ Finset.range m, term k := by
    refine (Finset.sum_nbij
      (s := Finset.range m)
      (t := (Finset.range (n + 1)).filter (fun i => i % 2 = 1))
      (i := fun k => 2 * k + 1)
      (f := term)
      (g := fun i => (q : ℝ) ^ i / i)
      ?_ ?_ ?_ ?_).symm
    · intro k hk
      apply Finset.mem_filter.2
      constructor
      · -- membership in range
        have hk' : k < m := Finset.mem_range.1 hk
        have hk_succ : Nat.succ k ≤ m := (Nat.succ_le_iff).2 hk'
        have hk_succ' : k + 1 ≤ (n + 1) / 2 := by simpa [m] using hk_succ
        have hk_mul : (k + 1) * 2 ≤ n + 1 :=
          (Nat.le_div_iff_mul_le Nat.zero_lt_two).1 hk_succ'
        have hk_mul' : 2 * k + 2 ≤ n + 1 := by
          simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk_mul
        have hk_lt : 2 * k + 1 < n + 1 := by
          have hlt : 2 * k + 1 < 2 * k + 2 := Nat.lt_succ_self (2 * k + 1)
          exact lt_of_lt_of_le hlt hk_mul'
        exact Finset.mem_range.2 hk_lt
      · -- oddness
        have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
        exact (Nat.odd_iff).1 hodd
    · intro a ha b hb hEq
      have hEq' : Nat.succ (2 * a) = Nat.succ (2 * b) := by
        simpa [Nat.succ_eq_add_one] using hEq
      have hEq'' : 2 * a = 2 * b := (Nat.succ_inj).1 hEq'
      exact Nat.mul_left_cancel Nat.zero_lt_two hEq''
    · intro i hi
      simp only [Finset.coe_range, Set.mem_image, Set.mem_Iio, m]
      use (i - 1) / 2
      simp at hi
      grind only
    · intro k hk
      simp [term]
  -- Combine the steps.
  calc
    ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum
        = ∑ i ∈ Finset.range (n + 1),
            ((if i % 2 = 1 then ((i : ℚ) : ℚ)⁻¹ else 0 : ℚ) : ℝ) * (q : ℝ) ^ i := hlist
    _ = ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i % 2 = 1),
          (q : ℝ) ^ i / i := hsum_filter
    _ = ∑ k ∈ Finset.range m, term k := hsum_reindex


theorem atanh_taylor_remainder_in_interval {q : ℚ} (hq : |(q : ℝ)| < 1) (n : ℕ) :
    Real.atanh q - ((atanhTaylorCoeffs n).zipIdx.map (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum
    ∈ atanhRemainderBoundComputable |q| n := by
  -- The remainder is the tail of the series
  simp only [atanhRemainderBoundComputable, abs_abs]
  have hq_abs_lt : |q| < 1 := by
    have h := abs_lt.mp hq
    rw [abs_lt]; constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have h_not_ge : ¬(|q| ≥ 1) := not_le.mpr hq_abs_lt
  simp only [h_not_ge, mem_def]
  -- The bound R = |q|^(n+1)/(1-|q|) in ℚ
  set R_rat := |q| ^ (n + 1) / (1 - |q|) with hR_rat_def
  -- Key bounds: |q| < 1 in ℚ
  have hr_nonneg_rat : 0 ≤ |q| := abs_nonneg q
  have hdenom_pos_rat : 0 < 1 - |q| := by linarith
  have hR_nonneg_rat' : 0 ≤ R_rat := by
    apply div_nonneg
    · exact pow_nonneg hr_nonneg_rat (n + 1)
    · linarith
  have hR_nonneg : (0 : ℝ) ≤ R_rat := Rat.cast_nonneg.mpr hR_nonneg_rat'
  -- The absolute value of the remainder is bounded
  have habs : |Real.atanh q - ((atanhTaylorCoeffs n).zipIdx.map
      (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum| ≤ (R_rat : ℝ) := by
    -- Strategy: The atanh series is Σ_k q^(2k+1)/(2k+1)
    -- The polynomial computes Σ_{i≤n, i odd} q^i/i
    -- The remainder is Σ_{k: 2k+1 > n} q^(2k+1)/(2k+1)
    -- Bound: |remainder| ≤ Σ_{k: 2k+1 > n} |q|^(2k+1) ≤ |q|^(n+1)/(1-|q|)

    -- Get the series representation
    have hseries := Real.atanh_hasSum' hq
    -- The polynomial sum equals the partial series sum for terms with index ≤ n
    -- atanhTaylorCoeffs n = [0, 1, 0, 1/3, 0, 1/5, ...] for indices 0..n
    -- So the sum is Σ_{i odd, i ≤ n} q^i/i = Σ_{k: 2k+1 ≤ n} q^(2k+1)/(2k+1)

    -- For the bound, we use that each term |q^(2k+1)/(2k+1)| ≤ |q|^(2k+1)
    -- and the geometric series Σ_{m≥n+1} |q|^m ≤ |q|^(n+1)/(1-|q|)

    -- This is a non-trivial series argument - for now use the bound directly
    -- The remainder terms satisfy |term_k| ≤ |q|^(2k+1) for 2k+1 > n
    -- Summing: |remainder| ≤ |q|^(n+1) * (1 + |q| + |q|² + ...) = |q|^(n+1)/(1-|q|)
    have hq_real_lt : |(q : ℝ)| < 1 := hq
    have hq_abs_nonneg : 0 ≤ |(q : ℝ)| := abs_nonneg _
    -- The remainder is bounded by a geometric series tail
    -- |Σ_{k: 2k+1 > n} q^(2k+1)/(2k+1)| ≤ Σ_{k: 2k+1 > n} |q|^(2k+1)
    --                                    ≤ |q|^(n+1) + |q|^(n+2) + ...
    --                                    = |q|^(n+1) / (1 - |q|)
    -- Define the series term and the split point m
    let term := fun k : ℕ => (q : ℝ) ^ (2 * k + 1) / (2 * k + 1)
    -- m = number of terms with 2k+1 ≤ n, i.e., k ≤ (n-1)/2
    let m := (n + 1) / 2
    -- Key: 2m ≥ n (so 2m+1 ≥ n+1)
    have hm_bound : 2 * m ≥ n := by simp only [m]; omega
    -- Step 1: Show polynomial sum equals partial series sum up to m terms
    -- The polynomial atanhTaylorCoeffs n has coefficients:
    -- index i: 1/i if i is odd and i ≤ n, else 0
    -- So the sum gives Σ_{k: 2k+1 ≤ n} q^(2k+1)/(2k+1) = Σ_{k < m} term k
    have h_poly_eq_partial := atanhTaylorCoeffs_sum q n
    -- Step 2: The remainder is the tail of the series starting at m
    have h_summable := hseries.summable
    have h_tail_summable : Summable fun k => term (k + m) := (summable_nat_add_iff m).mpr h_summable
    have h_tail_eq : Real.atanh q - ∑ k ∈ Finset.range m, term k = ∑' k, term (k + m) := by
      have h_split := h_summable.sum_add_tsum_nat_add m
      have h_tsum_eq : ∑' i, term i = Real.atanh q := hseries.tsum_eq
      linarith [h_split, h_tsum_eq]
    rw [h_poly_eq_partial, h_tail_eq]
    -- Step 3: Bound the tail by geometric series
    have hz_abs_sq : |(q : ℝ)| ^ 2 < 1 := by
      have h1 : |(q : ℝ)| ^ 2 ≤ |(q : ℝ)| := by
        have hn : 0 ≤ |(q : ℝ)| := abs_nonneg _
        have hle : |(q : ℝ)| ≤ 1 := le_of_lt hq
        nlinarith [sq_nonneg (|(q : ℝ)| - 1)]
      linarith
    have hz_abs_nonneg : 0 ≤ |(q : ℝ)| := abs_nonneg _
    have hz_abs_le : |(q : ℝ)| ≤ 1 := le_of_lt hq
    -- Define the dominating geometric term
    let geo_term := fun k : ℕ => |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k
    have h_geo_summable : Summable geo_term := by
      apply Summable.mul_left
      exact summable_geometric_of_lt_one (sq_nonneg _) hz_abs_sq
    have h_term_bound : ∀ k, |term (k + m)| ≤ geo_term k := by
      intro k
      simp only [term, geo_term]
      rw [abs_div, abs_pow]
      have h_pow_eq : |(q : ℝ)| ^ (2 * (k + m) + 1) = |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^
        k := by
        have : 2 * (k + m) + 1 = 2 * m + 1 + 2 * k := by ring
        rw [this, pow_add, pow_mul]
      rw [h_pow_eq]
      have h_denom_pos' : (0 : ℝ) < 2 * (k + m : ℕ) + 1 := by positivity
      have h_denom_ge_one : (1 : ℝ) ≤ |(2 : ℝ) * (k + m : ℕ) + 1| := by
        rw [abs_of_pos h_denom_pos']
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        push_cast; linarith
      calc |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k / |(2 : ℝ) * (k + m : ℕ) + 1|
          ≤ |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k / 1 := by
            apply div_le_div_of_nonneg_left _ (by positivity) h_denom_ge_one
            positivity
        _ = |(q : ℝ)| ^ (2 * m + 1) * (|(q : ℝ)| ^ 2) ^ k := by ring
    have h_norm_sum : ‖∑' k, term (k + m)‖ ≤ ∑' k, ‖term (k + m)‖ :=
      norm_tsum_le_tsum_norm h_tail_summable.norm
    simp only [Real.norm_eq_abs] at h_norm_sum
    calc |∑' k, term (k + m)|
        ≤ ∑' k, |term (k + m)| := h_norm_sum
      _ ≤ ∑' k, geo_term k := h_tail_summable.abs.tsum_le_tsum h_term_bound h_geo_summable
      _ = |(q : ℝ)| ^ (2 * m + 1) * ∑' k, (|(q : ℝ)| ^ 2) ^ k := by
          simp only [geo_term]; rw [tsum_mul_left]
      _ = |(q : ℝ)| ^ (2 * m + 1) / (1 - |(q : ℝ)| ^ 2) := by
          rw [tsum_geometric_of_lt_one (sq_nonneg _) hz_abs_sq]; ring
      _ ≤ |(q : ℝ)| ^ (n + 1) / (1 - |(q : ℝ)| ^ 2) := by
          -- 2m + 1 ≥ n + 1 since 2m ≥ n
          have h_exp_le : n + 1 ≤ 2 * m + 1 := by omega
          have h_pow_le : |(q : ℝ)| ^ (2 * m + 1) ≤ |(q : ℝ)| ^ (n + 1) :=
            pow_le_pow_of_le_one hz_abs_nonneg hz_abs_le h_exp_le
          have h_denom_pos : 0 < 1 - |(q : ℝ)| ^ 2 := by nlinarith [sq_nonneg (q : ℝ), sq_abs (q :
            ℝ)]
          exact div_le_div_of_nonneg_right h_pow_le h_denom_pos.le
      _ ≤ |(q : ℝ)| ^ (n + 1) / (1 - |(q : ℝ)|) := by
          -- 1 - |q|² ≥ 1 - |q| since |q|² ≤ |q| for |q| ≤ 1
          have h1 : |(q : ℝ)| ^ 2 ≤ |(q : ℝ)| := by nlinarith [sq_nonneg (|(q : ℝ)| - 1)]
          have h2 : 1 - |(q : ℝ)| ≤ 1 - |(q : ℝ)| ^ 2 := by linarith
          have h3 : 0 < 1 - |(q : ℝ)| := by linarith
          have h4 : 0 ≤ |(q : ℝ)| ^ (n + 1) := pow_nonneg hz_abs_nonneg _
          exact div_le_div_of_nonneg_left h4 h3 h2
      _ = (R_rat : ℝ) := by
          -- R_rat = |q|^(n+1)/(1-|q|) in ℚ
          simp only [hR_rat_def]
          -- Show: |(q:ℝ)|^(n+1)/(1-|(q:ℝ)|) = (|q|^(n+1)/(1-|q|) : ℚ)
          rw [← Rat.cast_abs q]
          push_cast
          ring
  have h := abs_le.mp habs
  constructor
  · calc ((-R_rat : ℚ) : ℝ) = -((R_rat : ℚ) : ℝ) := by push_cast; ring
      _ ≤ _ := h.1
  · exact h.2

/-- FTIA for atanhPointComputable: Real.atanh q ∈ atanhPointComputable q n for |q| < 1. -/
theorem mem_atanhPointComputable (q : ℚ) (n : ℕ) (hq : |(q : ℝ)| < 1) :
    Real.atanh q ∈ atanhPointComputable q n := by
  simp only [atanhPointComputable]
  -- Since |q| < 1, the condition |q| ≥ 1 is false
  have hq_rat : |q| < 1 := by
    have h := abs_lt.mp hq
    rw [abs_lt]
    constructor
    · have : (-1 : ℝ) < q := h.1
      exact_mod_cast this
    · have : (q : ℝ) < 1 := h.2
      exact_mod_cast this
  have h_not_ge : ¬(|q| ≥ 1) := not_le.mpr hq_rat
  simp only [h_not_ge, ↓reduceIte]
  -- Polynomial part: the partial sum is in evalTaylorSeries
  have hpoly := mem_evalTaylorSeries_atanh n (q := q)
  -- Remainder part: the tail is in atanhRemainderBoundComputable
  have hrem := atanh_taylor_remainder_in_interval hq n
  -- Combine: atanh q = partial_sum + remainder
  have heq : Real.atanh q = ((atanhTaylorCoeffs n).zipIdx.map
      (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum +
      (Real.atanh q - ((atanhTaylorCoeffs n).zipIdx.map
        (fun (c, i) => (c : ℝ) * (q : ℝ) ^ i)).sum) := by ring
  rw [heq]
  exact mem_add hpoly hrem

/-! ### Computable ln(2) via atanh

ln(2) = 2 * atanh(1/3), since:
  2 = (1 + 1/3) / (1 - 1/3) = (4/3) / (2/3)
  So atanh(1/3) = (1/2) * ln(2), giving ln(2) = 2 * atanh(1/3)
-/

/-- Compute ln(2) as an interval using 2 * atanh(1/3).
    This converges rapidly since atanh series at 1/3 has |y| = 1/3. -/
def ln2Computable (n : ℕ := 20) : IntervalRat :=
  let atanh_third := atanhPointComputable (1/3) n
  scale 2 atanh_third

/-- FTIA for ln2Computable: Real.log 2 ∈ ln2Computable n.
    Uses the identity log(2) = 2 * atanh(1/3) from log_via_atanh. -/
theorem mem_ln2Computable (n : ℕ) : Real.log 2 ∈ ln2Computable n := by
  simp only [ln2Computable]
  -- log(2) = 2 * atanh(1/3) via log_via_atanh
  have hlog_eq : Real.log 2 = 2 * Real.atanh (↑(1/3 : ℚ)) := by
    have h := LogReduction.log_via_atanh (by norm_num : (0 : ℚ) < 2)
    -- Convert: ((↑2 : ℝ) - 1) / ((↑2 : ℝ) + 1) = ↑(1/3 : ℚ)
    have h_arg : ((↑(2 : ℚ) : ℝ) - 1) / (↑(2 : ℚ) + 1) = ↑(1/3 : ℚ) := by
      simp only [Rat.cast_ofNat]
      norm_num
    rw [h_arg] at h
    convert! h using 1
  rw [hlog_eq]
  -- atanh(1/3) ∈ atanhPointComputable (1/3) n by mem_atanhPointComputable
  have h_third_lt : |(↑(1/3 : ℚ) : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  exact mem_scale 2 (mem_atanhPointComputable (1/3) n h_third_lt)

/-! ### Computable log via argument reduction

For q > 0, we compute:
  1. Reduce q to m * 2^k where m ∈ [1/2, 2]
  2. Compute log(m) = 2 * atanh((m-1)/(m+1)), which has |arg| ≤ 1/3
  3. Result = log(m) + k * ln(2)
-/

/-- Reduction exponent k such that q * 2^(-k) ≈ 1 -/
def logReductionExponent (q : ℚ) : ℤ :=
  if q ≤ 0 then 0
  else
    let n_log := q.num.natAbs.log2
    let d_log := q.den.log2
    (n_log : ℤ) - (d_log : ℤ)

/-- Reduced mantissa m = q * 2^(-k) -/
def logReduceMantissa (q : ℚ) : ℚ :=
  if q ≤ 0 then 1
  else q * (2 : ℚ) ^ (-logReductionExponent q)

/-- Computable log at a single rational point q > 0.
    Returns log(q) = log(m) + k * ln(2) where m = q * 2^(-k). -/
def logPointComputable (q : ℚ) (n : ℕ := 20) : IntervalRat :=
  if q ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for non-positive
  else
    let k := logReductionExponent q
    let m := logReduceMantissa q
    -- log(m) = 2 * atanh((m-1)/(m+1))
    let y := (m - 1) / (m + 1)
    let atanh_y := atanhPointComputable y n
    let log_m := scale 2 atanh_y
    -- k * ln(2)
    let k_ln2 := scale k (ln2Computable n)
    add log_m k_ln2

/-- Logarithm evaluation using all configuration-dependent data prepared for depth `n`. -/
def logPointComputablePrepared (q : ℚ) (n : ℕ) (ln2 : IntervalRat)
    (atanhCoeffs : List ℚ) : IntervalRat :=
  if q ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩
  else
    let k := logReductionExponent q
    let m := logReduceMantissa q
    let y := (m - 1) / (m + 1)
    let atanh_y := atanhPointComputableWithCoeffs y n atanhCoeffs
    let log_m := scale 2 atanh_y
    let k_ln2 := scale k ln2
    add log_m k_ln2

theorem logPointComputablePrepared_eq (q : ℚ) (n : ℕ) :
    logPointComputablePrepared q n (ln2Computable n) (atanhTaylorCoeffs n) =
      logPointComputable q n := by
  simp [logPointComputablePrepared, logPointComputable,
    atanhPointComputableWithCoeffs_eq]

/-- Computable interval enclosure for log using endpoint evaluation.
    Since log is strictly increasing on (0, ∞), we evaluate at endpoints. -/
def logComputable (I : IntervalRat) (n : ℕ := 20) : IntervalRat :=
  if I.lo ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩  -- Fallback for non-positive interval
  else
    -- log is monotone increasing, so log([lo, hi]) = [log(lo), log(hi)]
    let logLo := logPointComputable I.lo n
    let logHi := logPointComputable I.hi n
    hull logLo logHi

/-- Interval logarithm using all data prepared for depth `n`. -/
def logComputablePrepared (I : IntervalRat) (n : ℕ) (ln2 : IntervalRat)
    (atanhCoeffs : List ℚ) : IntervalRat :=
  if I.lo ≤ 0 then
    ⟨-1000, 1000, by norm_num⟩
  else
    let logLo := logPointComputablePrepared I.lo n ln2 atanhCoeffs
    let logHi := logPointComputablePrepared I.hi n ln2 atanhCoeffs
    hull logLo logHi

theorem logComputablePrepared_eq (I : IntervalRat) (n : ℕ) :
    logComputablePrepared I n (ln2Computable n) (atanhTaylorCoeffs n) =
      logComputable I n := by
  simp [logComputablePrepared, logComputable, logPointComputablePrepared_eq]

/-- The local logReductionExponent equals LogReduction.reductionExponent for positive q -/
private theorem logReductionExponent_eq {q : ℚ} (hq : 0 < q) :
    logReductionExponent q = LogReduction.reductionExponent q := by
  simp only [logReductionExponent, LogReduction.reductionExponent, not_le.mpr hq, ↓reduceIte]

/-- The local logReduceMantissa equals LogReduction.reduceMantissa for positive q -/
private theorem logReduceMantissa_eq {q : ℚ} (hq : 0 < q) :
    logReduceMantissa q = LogReduction.reduceMantissa q := by
  simp only [logReduceMantissa, LogReduction.reduceMantissa, not_le.mpr hq, ↓reduceIte,
             logReductionExponent_eq hq]

/-- FTIA for logPointComputable -/
theorem mem_logPointComputable {q : ℚ} (hq : 0 < q) (n : ℕ) :
    Real.log q ∈ logPointComputable q n := by
  unfold logPointComputable
  simp only [not_le.mpr hq, ↓reduceIte]
  -- Get the reduced mantissa and exponent
  set k := logReductionExponent q with hk_def
  set m := logReduceMantissa q with hm_def
  -- Show they equal the LogReduction definitions
  have hk_eq : k = LogReduction.reductionExponent q := logReductionExponent_eq hq
  have hm_eq : m = LogReduction.reduceMantissa q := logReduceMantissa_eq hq
  -- Get bounds on m from LogReduction.reduced_bounds
  have hm_bounds : 1/2 ≤ m ∧ m ≤ 2 := by rw [hm_eq]; exact LogReduction.reduced_bounds hq
  have hm_pos : 0 < m := by rw [hm_eq]; exact LogReduction.reduced_pos hq
  -- Compute y = (m-1)/(m+1) and get bounds from atanh_arg_bounds
  set y := (m - 1) / (m + 1) with hy_def
  have hy_bounds : (-1)/3 ≤ y ∧ y ≤ 1/3 := LogReduction.atanh_arg_bounds hm_bounds.1 hm_bounds.2
  -- Key: |y| ≤ 1/3 < 1, so we can use mem_atanhPointComputable
  have hy_abs_lt : |(y : ℝ)| < 1 := by
    rw [abs_lt]
    have hlo : ((-1 : ℚ) / 3 : ℝ) ≤ y := by exact_mod_cast hy_bounds.1
    have hhi : (y : ℝ) ≤ (1 : ℚ) / 3 := by exact_mod_cast hy_bounds.2
    constructor <;> linarith
  -- Step 1: atanh(y) ∈ atanhPointComputable y n
  have h_atanh := mem_atanhPointComputable y n hy_abs_lt
  -- Step 2: log(m) = 2 * atanh(y), so log(m) ∈ scale 2 (atanhPointComputable y n)
  have h_log_m_eq : Real.log m = 2 * Real.atanh y := by
    have h := LogReduction.log_via_atanh hm_pos
    -- h : Real.log m = 2 * Real.atanh ((m - 1) / (m + 1))
    -- Need to show: ((m - 1) / (m + 1) : ℚ) : ℝ = ((m : ℝ) - 1) / ((m : ℝ) + 1)
    have hcast : (y : ℝ) = ((m : ℝ) - 1) / ((m : ℝ) + 1) := by
      simp only [hy_def]
      push_cast
      ring
    rw [hcast]
    exact h
  have h_log_m := mem_scale 2 h_atanh
  -- h_log_m : (2 : ℚ) * Real.atanh y ∈ scale 2 (atanhPointComputable y n)
  -- h_log_m_eq : Real.log m = 2 * Real.atanh y
  have h_log_m' : Real.log m ∈ scale 2 (atanhPointComputable y n) := by
    rw [h_log_m_eq]
    exact h_log_m
  -- Step 3: log(2) ∈ ln2Computable n
  have h_ln2 := mem_ln2Computable n
  -- Step 4: k * log(2) ∈ scale k (ln2Computable n)
  have h_k_ln2 := mem_scale k h_ln2
  -- Step 5: log(q) = log(m) + k * log(2) by log_reduction
  have h_log_eq : Real.log q = Real.log m + k * Real.log 2 := by
    have h := LogReduction.log_reduction hq
    exact h
  -- Step 6: Combine using mem_add
  rw [h_log_eq]
  exact mem_add h_log_m' h_k_ln2

/-- FTIA for logComputable: if x ∈ I and I.lo > 0, then log(x) ∈ logComputable I n -/
theorem mem_logComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hpos : 0 < I.lo) (n : ℕ) :
    Real.log x ∈ logComputable I n := by
  simp only [logComputable, not_le.mpr hpos, ↓reduceIte]
  -- Since log is strictly monotone and x ∈ [lo, hi] with lo > 0:
  -- log(lo) ≤ log(x) ≤ log(hi)
  have hlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx.1
  have hlo_mem := mem_logPointComputable hpos n
  have hhi_pos : 0 < I.hi := lt_of_lt_of_le hpos I.le
  have hhi_mem := mem_logPointComputable hhi_pos n
  -- x ∈ [lo, hi] implies log(lo) ≤ log(x) ≤ log(hi) by monotonicity
  have hlog_lo_le : Real.log I.lo ≤ Real.log x :=
    Real.log_le_log hlo_pos hx.1
  have hlog_x_le_hi : Real.log x ≤ Real.log I.hi :=
    Real.log_le_log hx_pos hx.2
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (logPointComputable I.lo n).lo (logPointComputable I.hi n).lo : ℝ)
        ≤ (logPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.log I.lo := hlo_mem.1
      _ ≤ Real.log x := hlog_lo_le
  · calc Real.log x ≤ Real.log I.hi := hlog_x_le_hi
      _ ≤ (logPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((logPointComputable I.lo n).hi : ℝ) ((logPointComputable I.hi n).hi : ℝ) :=
        le_max_right _ _

/-- Conditional version of mem_logComputable for use in correctness proofs.
    Requires I.lo > 0 so the log interval is well-defined and monotone. -/
theorem mem_logComputable' {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (hpos : 0 < I.lo) (n : ℕ) :
    Real.log x ∈ logComputable I n := by
  exact mem_logComputable hx hpos n

/-! ### Computable erf via Taylor series -/

/-- Interval containing 2/√π ≈ 1.128379...
    Used for erf calculations. 2/√π is in (1.128, 1.129). -/
def twoDivSqrtPi : IntervalRat :=
  ⟨1128/1000, 1129/1000, by norm_num⟩

/-- Taylor coefficients for erf (without the 2/√π factor):
    erf(x) = (2/√π) * Σ_{n=0}^∞ (-1)^n * x^(2n+1) / (n! * (2n+1))

    So the coefficient of x^k is:
    - 0 if k is even
    - (-1)^((k-1)/2) / (((k-1)/2)! * k) if k is odd -/
def erfTaylorCoeffs (n : ℕ) : List ℚ :=
  (List.range (n + 1)).map (fun i =>
    if i % 2 = 1 then  -- odd terms only: x, x³, x⁵, ...
      let m : ℕ := (i - 1) / 2  -- for x^(2m+1), m = (i-1)/2
      ((-1 : ℚ) ^ m) / (ratFactorial m * (i : ℚ))
    else 0)

/-- Computable erf remainder bound.
    Since |erf^{(k)}(x)| ≤ (2/√π) * 2^k for all x (rough bound),
    and erf is bounded by 1, we use a combination.

    For the Taylor remainder centered at 0, we use:
    |R_n(x)| ≤ sup|f^{(n+1)}(ξ)| * |x|^{n+1} / (n+1)!

    A conservative bound: |erf^{(k)}(x)| ≤ (2/√π) * k! / (k/2)! ≤ 2 * k^{k/2}
    But since |erf| ≤ 1, we can intersect with [-1, 1].

    We use: remainder ≤ 2 * |x|^{n+1} / (n+1)! (very conservative). -/
def erfRemainderBoundComputable (I : IntervalRat) (n : ℕ) : IntervalRat :=
  let r := maxAbs I
  -- Conservative bound: use 2 as the derivative bound (since 2/√π ≈ 1.13)
  let R := 2 * r ^ (n + 1) / ratFactorial (n + 1)
  ⟨-R, R, by
    have hr : 0 ≤ r := le_max_of_le_left (abs_nonneg I.lo)
    have hfact : (0 : ℚ) ≤ ratFactorial (n + 1) := by
      simp only [ratFactorial]; exact Nat.cast_nonneg _
    have hpow : (0 : ℚ) ≤ r ^ (n + 1) := pow_nonneg hr _
    have hR : 0 ≤ R := div_nonneg (mul_nonneg (by norm_num : (0:ℚ) ≤ 2) hpow) hfact
    linarith⟩

/-- Computable interval enclosure for erf at a single rational point.
    Uses sign-aware clipped linear bounds:
    `|erf(q)| ≤ min(1, (2257/2000)*|q|)`.

    Cases:
    - `q < 0  => erf(q) ∈ [-1, 0]`
    - `q = 0  => erf(q) = 0`
    - `q > 0  => erf(q) ∈ [0, 1]`

    with tighter near-zero magnitude via `(2257/2000)*|q|`. -/
def erfPointComputable (q : ℚ) (n : ℕ := 15) : IntervalRat :=
  let _ := n
  let b : ℚ := min 1 ((2257 / 2000) * |q|)
  if hq : q < 0 then
    ⟨-b, 0, by
      unfold b
      have hb_nonneg : (0 : ℚ) ≤ min 1 ((2257 / 2000) * |q|) := by
        apply le_min
        · norm_num
        · exact mul_nonneg (by norm_num) (abs_nonneg q)
      linarith⟩
  else if h0 : q = 0 then
    ⟨0, 0, by norm_num⟩
  else
    ⟨0, b, by
      unfold b
      have hb_nonneg : (0 : ℚ) ≤ min 1 ((2257 / 2000) * |q|) := by
        apply le_min
        · norm_num
        · exact mul_nonneg (by norm_num) (abs_nonneg q)
      exact hb_nonneg⟩

/-- Computable interval enclosure for erf using Taylor series with monotonicity.

    erf(x) = (2/√π) * Σ_{n=0}^∞ (-1)^n * x^(2n+1) / (n! * (2n+1))

    Since erf is strictly monotone increasing (erf'(x) = (2/√π)e^{-x²} > 0),
    we use endpoint evaluation: erf([a,b]) ⊆ [erf(a), erf(b)].

    We intersect with [-1, 1] for safety. -/
def erfComputable (I : IntervalRat) (n : ℕ := 15) : IntervalRat :=
  -- erf is strictly monotone increasing, so evaluate at endpoints
  let erfLo := erfPointComputable I.lo n
  let erfHi := erfPointComputable I.hi n
  let raw := hull erfLo erfHi
  -- Intersect with global bound [-1, 1]
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match intersect raw globalBound with
  | some refined => refined
  | none => globalBound

/-- 2/√π is in the interval twoDivSqrtPi.
    2/√π ≈ 1.1283791670955126, which is in (1.128, 1.129).

    This is a helper theorem for correctness proofs. The computation of
    erfComputable is independent of this theorem. -/
theorem two_div_sqrt_pi_mem : 2 / Real.sqrt Real.pi ∈ twoDivSqrtPi := by
  simp only [twoDivSqrtPi, mem_def]
  -- From π bounds: 3.1415 < π < 3.1416 (Real.pi_gt_d4, Real.pi_lt_d4)
  -- So √π is between √3.1415 ≈ 1.7724 and √3.1416 ≈ 1.7725
  -- Thus 2/√π is between 2/1.7725 ≈ 1.1283 and 2/1.7724 ≈ 1.1285
  have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_hi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hsqrt_lo : (1.7724 : ℝ) < Real.sqrt Real.pi := by
    have h1 : (1.7724 : ℝ) ^ 2 < Real.pi := by
      have : (1.7724 : ℝ) ^ 2 = 3.14140176 := by ring
      linarith
    have h2 : (0 : ℝ) ≤ 1.7724 := by norm_num
    have h3 : (0 : ℝ) ≤ 1.7724 ^ 2 := by positivity
    calc (1.7724 : ℝ) = Real.sqrt (1.7724 ^ 2) := (Real.sqrt_sq h2).symm
      _ < Real.sqrt Real.pi := Real.sqrt_lt_sqrt h3 h1
  have hsqrt_hi : Real.sqrt Real.pi < (1.7725 : ℝ) := by
    have h1 : Real.pi < (1.7725 : ℝ) ^ 2 := by
      have : (1.7725 : ℝ) ^ 2 = 3.14175625 := by ring
      linarith
    have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [← Real.sqrt_sq (le_of_lt (by norm_num : (0 : ℝ) < 1.7725))]
    exact Real.sqrt_lt_sqrt (le_of_lt hpi_pos) h1
  constructor
  · -- Goal: ↑(1128 / 1000) ≤ 2 / √π
    have h1 : ((1128 / 1000 : ℚ) : ℝ) < 2 / 1.7725 := by norm_num
    have h2 : (2 : ℝ) / 1.7725 < 2 / Real.sqrt Real.pi := by
      apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
      · exact Real.sqrt_pos.mpr Real.pi_pos
      · exact hsqrt_hi
    exact le_of_lt (lt_trans h1 h2)
  · -- Goal: 2 / √π ≤ ↑(1129 / 1000)
    have h1 : 2 / Real.sqrt Real.pi < (2 : ℝ) / 1.7724 := by
      apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
      · norm_num
      · exact hsqrt_lo
    have h2 : (2 : ℝ) / 1.7724 < ((1129 / 1000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt (lt_trans h1 h2)

/-- The "inner" erf function without the 2/√π factor:
    erfInner(x) = ∫₀ˣ exp(-t²) dt = (√π/2) * erf(x)

    This is the function whose Taylor series coefficients are erfTaylorCoeffs. -/
noncomputable def erfInner (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.exp (-(t^2))

/-- erf(x) = (2/√π) * erfInner(x) -/
theorem erf_eq_factor_mul_inner (x : ℝ) : Real.erf x = (2 / Real.sqrt Real.pi) * erfInner x := by
  unfold Real.erf erfInner
  ring

/-- The derivatives of erfInner(x) = ∫₀ˣ exp(-t²) dt.
    erfInner'(x) = exp(-x²)
    erfInner''(x) = -2x * exp(-x²)
    etc. -/
theorem erfInner_deriv : deriv erfInner = fun x => Real.exp (-(x^2)) := by
  ext x
  unfold erfInner
  have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
    Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
  exact hcont.integral_hasStrictDerivAt 0 x |>.hasDerivAt.deriv

/-- exp(-x²) is smooth. -/
theorem contDiff_exp_neg_sq : ContDiff ℝ ⊤ (fun x => Real.exp (-(x^2))) :=
  Real.contDiff_exp.comp (contDiff_neg.comp (contDiff_id.pow 2))

/-- exp(-x²) is analytic everywhere. -/
theorem analyticAt_exp_neg_sq (x : ℝ) : AnalyticAt ℝ (fun t => Real.exp (-(t^2))) x := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => t^2) x := analyticAt_id.pow 2
  have h2 : AnalyticAt ℝ (fun t : ℝ => -(t^2)) x := h1.neg
  exact h2.rexp

/-- exp(-x²) is analytic on ℝ. -/
theorem analyticOnNhd_exp_neg_sq : AnalyticOnNhd ℝ (fun t => Real.exp (-(t^2))) Set.univ :=
  fun x _ => analyticAt_exp_neg_sq x

/-- Helper: erfInner is C^n for all n. -/
private theorem erfInner_contDiff_nat (n : ℕ) : ContDiff ℝ n erfInner := by
  induction n with
  | zero =>
    -- C^0 = continuous
    refine contDiff_zero.mpr ?_
    have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
      Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
    have h_int : ∀ a b : ℝ, IntervalIntegrable (fun t => Real.exp (-(t^2))) MeasureTheory.volume a
      b :=
      fun a b => hcont.intervalIntegrable a b
    exact intervalIntegral.continuous_primitive h_int 0
  | succ n _ih =>
    -- C^(n+1) from C^n of derivative
    have hdiff : Differentiable ℝ erfInner := fun x =>
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow
        2))).integral_hasStrictDerivAt 0 x
        |>.hasStrictFDerivAt.differentiableAt
    have hderiv_smooth : ContDiff ℝ n (deriv erfInner) := by
      simp only [erfInner_deriv]
      exact contDiff_exp_neg_sq.of_le le_top
    exact contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, hderiv_smooth⟩

/-! ### Computable atanh interval via endpoint evaluation -/

/-- Computable interval enclosure for atanh using endpoint evaluation.
    Since atanh is strictly increasing on (-1, 1), we evaluate at endpoints.
    Requires the interval to be strictly inside (-1, 1); returns a wide fallback otherwise. -/
def atanhComputable (I : IntervalRat) (n : ℕ := 15) : IntervalRat :=
  if I.lo ≤ -1 then
    ⟨-1000, 1000, by norm_num⟩
  else if 1 ≤ I.hi then
    ⟨-1000, 1000, by norm_num⟩
  else
    let atanhLo := atanhPointComputable I.lo n
    let atanhHi := atanhPointComputable I.hi n
    hull atanhLo atanhHi

/-- Interval `atanh` using Taylor coefficients prepared for depth `n`. -/
def atanhComputableWithCoeffs (I : IntervalRat) (n : ℕ)
    (coeffs : List ℚ) : IntervalRat :=
  if I.lo ≤ -1 then
    ⟨-1000, 1000, by norm_num⟩
  else if 1 ≤ I.hi then
    ⟨-1000, 1000, by norm_num⟩
  else
    let atanhLo := atanhPointComputableWithCoeffs I.lo n coeffs
    let atanhHi := atanhPointComputableWithCoeffs I.hi n coeffs
    hull atanhLo atanhHi

theorem atanhComputableWithCoeffs_eq (I : IntervalRat) (n : ℕ) :
    atanhComputableWithCoeffs I n (atanhTaylorCoeffs n) = atanhComputable I n := by
  simp [atanhComputableWithCoeffs, atanhComputable, atanhPointComputableWithCoeffs_eq]

/-- FTIA for atanhComputable: if x ∈ I and I ⊂ (-1, 1), then atanh(x) ∈ atanhComputable I n. -/
theorem mem_atanhComputable {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (hlo : -1 < I.lo) (hhi : I.hi < 1) (n : ℕ) :
    Real.atanh x ∈ atanhComputable I n := by
  simp only [atanhComputable, not_le.mpr hlo, ↓reduceIte, not_le.mpr hhi, ↓reduceIte]
  -- x ∈ I ⊂ (-1, 1), so |lo|, |hi|, |x| < 1
  have hlo_real : (-1 : ℝ) < I.lo := by exact_mod_cast hlo
  have hhi_real : (I.hi : ℝ) < 1 := by exact_mod_cast hhi
  have hx_lo : -1 < x := by linarith [hx.1]
  have hx_hi : x < 1 := by linarith [hx.2]
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have habs_lo : |(I.lo : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_hi : |(I.hi : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs_x : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  -- atanh at endpoints
  have hlo_abs_rat : |(I.lo : ℝ)| < 1 := habs_lo
  have hhi_abs_rat : |(I.hi : ℝ)| < 1 := habs_hi
  have hlo_mem := mem_atanhPointComputable I.lo n hlo_abs_rat
  have hhi_mem := mem_atanhPointComputable I.hi n hhi_abs_rat
  -- Monotonicity: atanh(lo) ≤ atanh(x) ≤ atanh(hi)
  have hatanh_lo_le : Real.atanh I.lo ≤ Real.atanh x :=
    Real.atanh_mono habs_lo habs_x hx.1
  have hatanh_x_le_hi : Real.atanh x ≤ Real.atanh I.hi :=
    Real.atanh_mono habs_x habs_hi hx.2
  simp only [hull, mem_def, Rat.cast_min, Rat.cast_max]
  constructor
  · calc (min (atanhPointComputable I.lo n).lo (atanhPointComputable I.hi n).lo : ℝ)
        ≤ (atanhPointComputable I.lo n).lo := by exact_mod_cast min_le_left _ _
      _ ≤ Real.atanh I.lo := hlo_mem.1
      _ ≤ Real.atanh x := hatanh_lo_le
  · calc Real.atanh x ≤ Real.atanh I.hi := hatanh_x_le_hi
      _ ≤ (atanhPointComputable I.hi n).hi := hhi_mem.2
      _ ≤ max ((atanhPointComputable I.lo n).hi : ℝ) ((atanhPointComputable I.hi n).hi : ℝ) :=
        le_max_right _ _

end IntervalRat

end LeanCert.Core
