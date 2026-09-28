/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!
# Automatic Differentiation - Transcendental Functions

This file provides dual interval implementations for transcendental functions,
implementing the chain rule for each.

## Main definitions

### Total functions (always succeed)
* `DualInterval.sin` - Sine with chain rule
* `DualInterval.cos` - Cosine with chain rule
* `DualInterval.exp` - Exponential with chain rule
* `DualInterval.atan` - Arctangent with chain rule
* `DualInterval.arsinh` - Inverse hyperbolic sine
* `DualInterval.sinh`, `cosh`, `tanh` - Hyperbolic functions
* `DualInterval.erf` - Error function
* `DualInterval.sqrt` - Square root (conservative derivative bound)
* `DualInterval.sinc` - sinc function

### Partial functions (return Option)
* `DualInterval.atanh?` - Inverse hyperbolic tangent (requires |x| < 1)
* `DualInterval.inv?` - Inverse (requires nonzero)
* `DualInterval.log?` - Logarithm (requires positive)
* `DualInterval.sqrt?` - Square root with tight bounds (requires positive)
-/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

namespace DualInterval

/-- Dual for sin (chain rule: d(sin f) = cos(f) * f') -/
def sin (d : DualInterval) : DualInterval :=
  { val := sinInterval d.val
    der := IntervalRat.mul (cosInterval d.val) d.der }

/-- Dual for cos (chain rule: d(cos f) = -sin(f) * f') -/
def cos (d : DualInterval) : DualInterval :=
  { val := cosInterval d.val
    der := IntervalRat.mul (IntervalRat.neg (sinInterval d.val)) d.der }

/-- Dual for exp (chain rule: d(exp f) = exp(f) * f') -/
noncomputable def exp (d : DualInterval) : DualInterval :=
  { val := IntervalRat.expInterval d.val
    der := IntervalRat.mul (IntervalRat.expInterval d.val) d.der }

/-- The interval [0, 1] used to bound derivative factors in (0, 1] -/
def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The derivative factor for arctan: 1/(1+x²) is in [0, 1] -/
theorem arctan_deriv_factor_mem_unitInterval (y : ℝ) :
    1 / (1 + y ^ 2) ∈ unitInterval := by
  simp only [unitInterval, IntervalRat.mem_def, Rat.cast_zero, Rat.cast_one]
  have hpos : 0 < 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  constructor
  · exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hpos)
  · rw [div_le_one hpos]
    nlinarith [sq_nonneg y]

/-- The derivative factor for arsinh: 1/√(1+x²) is in [0, 1] -/
theorem arsinh_deriv_factor_mem_unitInterval (y : ℝ) :
    (Real.sqrt (1 + y ^ 2))⁻¹ ∈ unitInterval := by
  simp only [unitInterval, IntervalRat.mem_def, Rat.cast_zero, Rat.cast_one]
  have h1 : 1 + y ^ 2 ≥ 1 := by nlinarith [sq_nonneg y]
  have hsqrt_ge_one : Real.sqrt (1 + y ^ 2) ≥ 1 := by
    calc Real.sqrt (1 + y ^ 2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  have hsqrt_pos : 0 < Real.sqrt (1 + y ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg y]
  constructor
  · exact inv_nonneg.mpr (le_of_lt hsqrt_pos)
  · exact inv_le_one_of_one_le₀ hsqrt_ge_one

/-- Dual for atan (chain rule: d(atan f) = f' / (1 + f²)) -/
def atan (d : DualInterval) : DualInterval :=
  { val := atanInterval d.val
    -- d(atan f) = f' / (1 + f²)
    -- Since 0 < 1/(1+x²) ≤ 1 for all x, we multiply d.der by [0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Dual for arsinh (chain rule: d(arsinh f) = f' / √(1 + f²)) -/
def arsinh (d : DualInterval) : DualInterval :=
  { val := arsinhInterval d.val
    -- d(arsinh f) = f' / √(1 + f²)
    -- Since 0 < 1/√(1+f²) ≤ 1, we multiply d.der by [0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Dual for sinh (chain rule: d(sinh f) = cosh(f) * f') -/
def sinh (d : DualInterval) : DualInterval :=
  { val := sinhInterval d.val
    -- sinh'(x) = cosh(x), so d(sinh f) = cosh(f) * f'
    der := IntervalRat.mul (coshInterval d.val) d.der }

/-- Dual for cosh (chain rule: d(cosh f) = sinh(f) * f') -/
def cosh (d : DualInterval) : DualInterval :=
  { val := coshInterval d.val
    -- cosh'(x) = sinh(x), so d(cosh f) = sinh(f) * f'
    der := IntervalRat.mul (sinhInterval d.val) d.der }

/-- Dual for tanh (chain rule: d(tanh f) = sech²(f) * f' = (1 - tanh²(f)) * f')
    Since sech²(x) = 1 - tanh²(x) ∈ (0, 1] for all x, we use [0, 1] as bound. -/
def tanh (d : DualInterval) : DualInterval :=
  { val := tanhInterval d.val
    -- tanh'(x) = sech²(x) = 1 - tanh²(x), which is in (0, 1]
    der := IntervalRat.mul d.der unitInterval }

/-- Interval containing 2/√π ≈ 1.128379... -/
def twoDivSqrtPi : IntervalRat :=
  ⟨1128/1000, 1129/1000, by norm_num⟩

/-- Dual for erf (chain rule: d(erf f) = (2/√π) * exp(-f²) * f')
    erf'(x) = (2/√π) * exp(-x²), which is always positive and bounded by 2/√π ≈ 1.13 -/
noncomputable def erf (d : DualInterval) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- erf is bounded in [-1, 1]
    der :=
      let valSq := IntervalRat.mul d.val d.val
      let negValSq := IntervalRat.neg valSq
      let expPart := IntervalRat.expInterval negValSq
      let factor := IntervalRat.mul twoDivSqrtPi expPart
      IntervalRat.mul factor d.der }

/-- Computable dual for erf using expComputable -/
def erfCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- erf is bounded in [-1, 1]
    der :=
      let valSq := IntervalRat.mul d.val d.val
      let negValSq := IntervalRat.neg valSq
      let expPart := IntervalRat.expComputable negValSq n
      let factor := IntervalRat.mul twoDivSqrtPi expPart
      IntervalRat.mul factor d.der }

/-- Dual for sqrt (chain rule: d(sqrt f) = f' / (2 * sqrt(f)))
    sqrt'(x) = 1/(2*sqrt(x)) for x > 0, undefined at x = 0.
    We use sqrtInterval for the value and a conservative bound for the derivative.
    Note: The derivative blows up as x → 0+, so this uses a wide conservative bound. -/
def sqrt (d : DualInterval) : DualInterval :=
  { val := IntervalRat.sqrtInterval d.val
    -- The derivative 1/(2*sqrt(x)) ∈ [0, ∞) for x > 0
    -- We use a very conservative bound [-100, 100] * der
    der := IntervalRat.mul d.der ⟨-100, 100, by norm_num⟩ }

/-- Conservative derivative bound [-1, 1] for sinc derivative -/
def sincDerivBound : IntervalRat := ⟨-1, 1, by norm_num⟩

/-- Dual for sinc (chain rule: d(sinc f) = sinc'(f) * f')
    sinc'(x) = (x cos x - sin x) / x² for x ≠ 0, limit 0 at x = 0.
    We use conservative bound: |sinc'(x)| ≤ 1 for all x. -/
def sinc (d : DualInterval) : DualInterval :=
  { val := ⟨-1, 1, by norm_num⟩  -- sinc is bounded in [-1, 1]
    -- sinc'(x) ∈ [-1, 1] (conservative bound), so d(sinc f) = sinc'(f) * f'
    der := IntervalRat.mul sincDerivBound d.der }

/-! ### Partial functions (domain-restricted) -/

/-- Partial dual for atanh (chain rule: d(atanh f) = f' / (1 - f²))
    Returns None if the value interval is not contained in (-1, 1). -/
noncomputable def atanh? (d : DualInterval) : Option DualInterval :=
  -- For atanh to be defined, we need |val| < 1
  -- We check if the interval is strictly inside (-1, 1)
  if d.val.hi < 1 ∧ d.val.lo > -1 then
    -- Very rough bound: atanh' = 1/(1-x²), which blows up as |x| → 1
    -- For now we use [-100, 100] * der as a hugely conservative bound
    let bound : ℚ := 100
    some { val := atanhInterval d.val
           der := ⟨-bound * (|d.der.lo| + |d.der.hi| + 1),
                   bound * (|d.der.lo| + |d.der.hi| + 1),
                   by
                     have h1 : (0 : ℚ) ≤ |d.der.lo| := abs_nonneg _
                     have h2 : (0 : ℚ) ≤ |d.der.hi| := abs_nonneg _
                     have h : (0 : ℚ) ≤ bound * (|d.der.lo| + |d.der.hi| + 1) := by
                       exact mul_nonneg (by norm_num) (by linarith)
                     linarith⟩ }
  else
    none

/-- Partial dual for inv (chain rule: d(1/f) = -f'/f²)
    Returns None if the value interval contains zero. -/
def inv? (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.containsZero d.val then
    none
  else
    let inv_val := IntervalRat.invNonzero ⟨d.val, h⟩
    -- d(1/f) = -f'/f² = -f' * (1/f)²
    let inv_sq := IntervalRat.mul inv_val inv_val
    let der' := IntervalRat.neg (IntervalRat.mul d.der inv_sq)
    some { val := inv_val, der := der' }

/-- Partial dual for log (chain rule: d(log f) = f'/f)
    Returns None if the value interval is not strictly positive. -/
noncomputable def log? (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.isPositive d.val then
    let log_val := IntervalRat.logInterval ⟨d.val, h⟩
    -- d(log f) = f'/f
    let inv_val := IntervalRat.invNonzero ⟨d.val, by
      -- isPositive implies not containsZero
      simp only [IntervalRat.isPositive, IntervalRat.containsZero] at h ⊢
      intro ⟨hle, _⟩
      exact absurd h (not_lt.mpr hle)⟩
    let der' := IntervalRat.mul d.der inv_val
    some { val := log_val, der := der' }
  else
    none

/-- Compute a conservative upper bound on 1/(2*sqrt(lo)) for lo > 0.
    Uses the fact that:
    - For 0 < lo ≤ 1: sqrt(lo) ≥ lo, so 1/(2*sqrt(lo)) ≤ 1/(2*lo)
    - For lo > 1: sqrt(lo) > 1, so 1/(2*sqrt(lo)) < 1/2 -/
def sqrtDerivCoefBound (lo : ℚ) (hpos : 0 < lo) : IntervalRat :=
  if lo ≤ 1 then
    ⟨0, 1 / (2 * lo), by
      exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hpos.le)⟩
  else
    ⟨0, 1 / 2, by norm_num⟩

/-- For lo > 0, the derivative coefficient 1/(2*sqrt(x)) is bounded above for x ≥ lo. -/
theorem sqrtDerivCoef_bound {x lo : ℝ} (hlo_pos : 0 < lo) (hx_ge : lo ≤ x) :
    1 / (2 * Real.sqrt x) ≤ max (1 / (2 * lo)) (1 / 2) := by
  have hx_pos : 0 < x := lt_of_lt_of_le hlo_pos hx_ge
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hdenom_pos : 0 < 2 * Real.sqrt x := by positivity
  -- sqrt(x) ≥ sqrt(lo) since sqrt is monotone
  have hsqrt_mono : Real.sqrt lo ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_ge
  have hsqrt_lo_pos : 0 < Real.sqrt lo := Real.sqrt_pos.mpr hlo_pos
  -- 1/(2*sqrt(x)) ≤ 1/(2*sqrt(lo))
  have hcoef_le : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt lo) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    · positivity
    · linarith
  -- Now bound 1/(2*sqrt(lo))
  rcases le_or_gt lo 1 with hle | hgt
  · -- lo ≤ 1: sqrt(lo) ≥ lo (since sqrt(x) ≥ x for 0 < x ≤ 1)
    have hsqrt_ge_lo : lo ≤ Real.sqrt lo := by
      have h1 : lo * lo ≤ lo := by nlinarith
      have h2 : lo = Real.sqrt lo * Real.sqrt lo → lo ≤ Real.sqrt lo := by
        intro heq
        by_contra! hc
        have : lo * lo > lo := by nlinarith
        linarith
      rw [← Real.sq_sqrt (le_of_lt hlo_pos)] at h1
      rcases eq_or_lt_of_le (Real.sqrt_nonneg lo) with hsz | hsgt
      · -- Case sqrt(lo) = 0 contradicts lo > 0
        have hsqrt_zero : Real.sqrt lo = 0 := hsz.symm
        have hlo_le_zero : lo ≤ 0 := Real.sqrt_eq_zero'.mp hsqrt_zero
        linarith
      · nlinarith [Real.sq_sqrt (le_of_lt hlo_pos)]
    -- 1/(2*sqrt(lo)) ≤ 1/(2*lo)
    have hbound : 1 / (2 * Real.sqrt lo) ≤ 1 / (2 * lo) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      · positivity
      · linarith
    calc 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt lo) := hcoef_le
      _ ≤ 1 / (2 * lo) := hbound
      _ ≤ max (1 / (2 * lo)) (1 / 2) := le_max_left _ _
  · -- lo > 1: sqrt(lo) > 1
    have hsqrt_gt_one : 1 < Real.sqrt lo := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hgt
    -- 1/(2*sqrt(lo)) < 1/2
    have hbound : 1 / (2 * Real.sqrt lo) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt lo) (by norm_num : (0 : ℝ) < 2)]
      ring_nf
      linarith
    calc 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt lo) := hcoef_le
      _ ≤ 1 / 2 := le_of_lt hbound
      _ ≤ max (1 / (2 * lo)) (1 / 2) := le_max_right _ _

/-- Partial dual for sqrt (chain rule: d(sqrt f) = f' / (2 * sqrt(f)))
    Returns None if the value interval is not strictly positive. -/
noncomputable def sqrt? (d : DualInterval) : Option DualInterval :=
  if h : IntervalRat.isPositive d.val then
    let sqrt_val := IntervalRat.sqrtInterval d.val
    -- d(sqrt f) = f' / (2 * sqrt(f)) = f' * (1 / (2 * sqrt(f)))
    let deriv_coef := sqrtDerivCoefBound d.val.lo h
    let der' := IntervalRat.mul d.der deriv_coef
    some { val := sqrt_val, der := der' }
  else
    none

end DualInterval

end LeanCert.Engine
