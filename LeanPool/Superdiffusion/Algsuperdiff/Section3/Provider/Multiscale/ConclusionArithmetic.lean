/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Numerics

/-!
# ConclusionArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The arithmetic cores of `p.bfA.multiscalebound`, Step 3

ABK26, proof of Proposition `p.bfA.multiscalebound`, **Step 3**.  Having
decomposed the block matrix over the Whitney simplices (Step 1) and bounded the
wave influence (Step 2), the manuscript sums the per-layer contributions over
the layer index `k`, selects `k_0 := c E^{-2} gamma^{-1}`, and collapses the
two small factors coming from `l.bad.cubes.density` into a single improved
exponential.

This module isolates the **pure real-arithmetic** content of that step, over
abstract reals with no ABK carrier in sight.  Two development rules force the
split: `nlinarith`/`linarith` must never see `rpow` or `exp` applied to a
compound carrier expression, and the `k_0` collapse is an `exp`/`rpow`
computation.  The carrier-level layer series that consumes these cores is
`Provider.Multiscale.ConclusionAssembly`.

## The square-root layer-density correction

With only the mass form available the `k`-sum of the `exp(-cE^{-2}gamma^{-1})`
leg diverges.

The consequence is proved locally here:

* the layer series runs at ratio `3^{-1/4}`
  (`tsum_geometric_three_rpow_neg_quarter`, with its summability twin
  `summable_geometric_three_rpow_neg_quarter`) rather than at the printed
  `3^{-3/4}`.

The cost is an absolute inflation of the Step-3 constant by
`(1 - 3^{-1/4})^{-1} / (1 - 3^{-3/4})^{-1}`, exactly
`1 + 3^{-1/4} + 3^{-1/2}`, a number between `2.33` and `2.34`.  It is a
constant of the carrier-level assembly, not of this module.

The deterministic half used here is `three_rpow_le_two_add_indicator`, `3^x <= 2
+ 3^x 1_{x > 3^{-4}}` for `x >= 0`, which is's own display.

## References

* ABK26, `p.bfA.multiscalebound`, Step 3.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

/-! ## `log 3`

`Percolation.Numerics` supplies `1 <= log 3 <= 2`.  The `k_0` collapse uses the
sharper upper bound `log 3 <= 3/2` for comfort (: `log 3 <= 2` would in fact
suffice — `2b·log 3 <= 4/9 <= 17/36`; convenience, not necessity). -/

/-- `exp (1/2) <= 2`, i.e. `e <= 4`. -/
private theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [(Real.exp_pos (1 / 2 : ℝ)).le, h1, h2]

/-- `log 3 <= 3/2`, sharper than `Percolation.log_three_le_two`. -/
theorem log_three_le_three_halves : Real.log 3 ≤ 3 / 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2 : ℝ) := Real.add_one_le_exp _
  have h3 : Real.exp (3 / 2 : ℝ) = Real.exp 1 * Real.exp (1 / 2 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith [h1, h2, (Real.exp_pos (1 : ℝ)).le, (Real.exp_pos (1 / 2 : ℝ)).le]

/-! ## The Cauchy-Schwarz step

`min{a, b} <= sqrt(a b)`: the interpolation that lets the capped layer bad mass
be spent half against the layer's own mass and half against the density bound. -/

/-- **The `min`/Cauchy-Schwarz step.**  For nonnegative `a`, `b`, `min a b <= sqrt
(a * b)`. -/
theorem min_le_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ Real.sqrt (a * b) := by
  have hmin : 0 ≤ min a b := le_min ha hb
  have hsq : min a b ^ 2 ≤ a * b := by
    have h1 : min a b ≤ a := min_le_left a b
    have h2 : min a b ≤ b := min_le_right a b
    nlinarith [hmin, h1, h2]
  calc min a b = Real.sqrt (min a b ^ 2) := (Real.sqrt_sq hmin).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hsq


/-! ## Square roots of the two elementary profiles -/

/-- `sqrt (3^t) = 3^{t/2}`. -/
theorem sqrt_three_rpow (t : ℝ) : Real.sqrt ((3 : ℝ) ^ t) = (3 : ℝ) ^ (t / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- `sqrt (exp x) = exp (x/2)`. -/
theorem sqrt_exp (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

/-- Subadditivity of the square root: `sqrt (a + c) <= sqrt a + sqrt c`. -/
theorem sqrt_add_le_sqrt_add_sqrt {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    Real.sqrt (a + c) ≤ Real.sqrt a + Real.sqrt c := by
  have hsum : (0 : ℝ) ≤ Real.sqrt a + Real.sqrt c :=
    add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c)
  have hsq : a + c ≤ (Real.sqrt a + Real.sqrt c) ^ 2 := by
    have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have h2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg c, h1, h2]
  calc Real.sqrt (a + c) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt c) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt a + Real.sqrt c := Real.sqrt_sq hsum

/-! ## Core 1a: the `k_0` collapse at the corrected (square-root) density -/

/-- **The `k_0` collapse** (`p.bfA.multiscalebound` Step 3, at the `min`-capped
layer density).

```
3^{2 b t} (exp(-t) + 3^{-t/2})^{1/2}  <=  2 exp(-t/36) ,
```

valid whenever `9 b <= 1` (true for the manuscript's `b = 2^{-20}`).

The exponent `1/36`, in place of the `1/4` of the printed
`k0_exponent_collapse`, is the entire quantitative cost; it is absorbed by the
manuscript's own "selecting `k_0 := c E^{-2} gamma^{-1}` for a sufficiently
small `c > 0`", i.e. by relabelling `c |-> c/36`. -/
theorem k0_sqrt_collapse {b t : ℝ} (hb0 : 0 ≤ b) (hb9 : 9 * b ≤ 1) (ht : 0 ≤ t) :
    (3 : ℝ) ^ (2 * b * t) * Real.sqrt (Real.exp (-t) + (3 : ℝ) ^ (-(t / 2)))
      ≤ 2 * Real.exp (-(t / 36)) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hl1 : (1 : ℝ) ≤ Real.log 3 := one_le_log_three
  have hl2 : Real.log 3 ≤ 3 / 2 := log_three_le_three_halves
  have hbt : 0 ≤ 2 * b * t := by positivity
  have hgrow : (0 : ℝ) < (3 : ℝ) ^ (2 * b * t) := Real.rpow_pos_of_pos h3pos _
  -- split the square root of the two-term density bound
  have hsplit : Real.sqrt (Real.exp (-t) + (3 : ℝ) ^ (-(t / 2)))
      ≤ Real.exp (-(t / 2)) + (3 : ℝ) ^ (-(t / 4)) := by
    refine le_trans (sqrt_add_le_sqrt_add_sqrt (Real.exp_pos _).le
      (Real.rpow_nonneg (by norm_num) _)) ?_
    have h1 : Real.sqrt (Real.exp (-t)) = Real.exp (-(t / 2)) := by
      rw [sqrt_exp]; congr 1; ring
    have h2 : Real.sqrt ((3 : ℝ) ^ (-(t / 2))) = (3 : ℝ) ^ (-(t / 4)) := by
      rw [sqrt_three_rpow]; congr 1; ring
    rw [h1, h2]
  -- leg 1: `3^{2bt} exp(-t/2) <= exp(-t/36)`
  have hterm1 : (3 : ℝ) ^ (2 * b * t) * Real.exp (-(t / 2)) ≤ Real.exp (-(t / 36)) := by
    rw [Real.rpow_def_of_pos h3pos, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hstep : Real.log 3 * (2 * b * t) ≤ 3 / 2 * (2 * b * t) :=
      mul_le_mul_of_nonneg_right hl2 hbt
    nlinarith [hstep, hb9, ht, hb0]
  -- leg 2: `3^{2bt} 3^{-t/4} = 3^{(2b - 1/4)t} <= exp(-t/36)`
  have hterm2 : (3 : ℝ) ^ (2 * b * t) * (3 : ℝ) ^ (-(t / 4)) ≤ Real.exp (-(t / 36)) := by
    rw [← Real.rpow_add h3pos, Real.rpow_def_of_pos h3pos]
    refine Real.exp_le_exp.mpr ?_
    have hexp : 2 * b * t + -(t / 4) ≤ -(t / 36) := by nlinarith [hb9, ht, hb0]
    have hneg : 2 * b * t + -(t / 4) ≤ 0 := by nlinarith [hb9, ht, hb0]
    nlinarith [hl1, hexp, hneg]
  calc (3 : ℝ) ^ (2 * b * t) * Real.sqrt (Real.exp (-t) + (3 : ℝ) ^ (-(t / 2)))
      ≤ (3 : ℝ) ^ (2 * b * t) * (Real.exp (-(t / 2)) + (3 : ℝ) ^ (-(t / 4))) :=
        mul_le_mul_of_nonneg_left hsplit hgrow.le
    _ = (3 : ℝ) ^ (2 * b * t) * Real.exp (-(t / 2))
          + (3 : ℝ) ^ (2 * b * t) * (3 : ℝ) ^ (-(t / 4)) := by ring
    _ ≤ 2 * Real.exp (-(t / 36)) := by linarith [hterm1, hterm2]

/-! ## Core 1b: the printed `k_0` collapse -/


/-! ## Core 2: the layer geometric series -/

theorem three_rpow_neg_quarter_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) :=
  Real.rpow_nonneg (by norm_num) _

theorem three_rpow_neg_quarter_lt_one : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := by
  have h : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < (3 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  simpa using h

theorem three_rpow_neg_three_quarters_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (-(3 / 4 : ℝ)) :=
  Real.rpow_nonneg (by norm_num) _


/-- **The layer-summation geometric series at the corrected ratio.**  After
the `min`/Cauchy-Schwarz step the collar leg of layer `k` carries the extra
factor `3^{k/2}`, so the printed ratio `3^{-3/4}` degrades to `3^{-1/4}`; the
sum still converges. -/
theorem tsum_geometric_three_rpow_neg_quarter :
    ∑' k : ℕ, ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k = (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ :=
  tsum_geometric_of_lt_one three_rpow_neg_quarter_nonneg three_rpow_neg_quarter_lt_one

theorem summable_geometric_three_rpow_neg_quarter :
    Summable fun k : ℕ => ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k :=
  summable_geometric_of_lt_one three_rpow_neg_quarter_nonneg three_rpow_neg_quarter_lt_one


/-! ## The exact constant inflation -/


/-! ## The deterministic split -/

/-- **The deterministic half's `3^{gamma hsep}` reduction**
(`p.bfA.multiscalebound` Step 3).

```
3^x  <=  1 + 3 x 1_{x <= 3^{-4}} + 3^x 1_{x > 3^{-4}}  <=  2 + 3^x 1_{x > 3^{-4}}
```

for `x >= 0`, using `3 * 3^{-4} < 1` for the deterministic step.  This is that
display, at the sharper deterministic estimate `3^x <= exp(1/2) <= 2` on
`0 <= x <= 3^{-4}`. -/
theorem three_rpow_le_two_add_indicator {x : ℝ} (hx : 0 ≤ x) :
    (3 : ℝ) ^ x ≤ 2 + (if (81 : ℝ)⁻¹ < x then (3 : ℝ) ^ x else 0) := by
  by_cases hcase : (81 : ℝ)⁻¹ < x
  · rw [ite_eq_left hcase]
    linarith
  · rw [ite_eq_right hcase]
    push Not at hcase
    have hl2 : Real.log 3 ≤ 2 := log_three_le_two
    have hlog : Real.log 3 * x ≤ 1 / 2 := by nlinarith [hx, hcase, hl2]
    calc (3 : ℝ) ^ x = Real.exp (Real.log 3 * x) :=
          Real.rpow_def_of_pos (by norm_num) x
      _ ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr hlog
      _ ≤ 2 := exp_half_le_two
      _ ≤ 2 + 0 := by norm_num

end

end Algsuperdiff.Section3.Provider.Multiscale
