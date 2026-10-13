/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenEnvelopeInputGauge

/-!
# GammaTenGaugeScalarCap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two **scalar** gauge factors of the Besov legs are capped

ABK26, `e.shom.h.bounds`, read at Step 2 of `l.approximate.recurrence.formula`,
`e.Fz.def`.

## The gap this module fills

`Closure.GammaTenEnvelopeInputGauge.cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_potential`
and `..._flux` identify the Besov tower of each gauged leg of `bfF_z` with a
*scalar multiple* of the tower of the raw field, the two scalars being

```
  c_1 = sqrt(sigma_0) . sqrt(shom_n)^{-1} ,   c_2 = sqrt(sigma_0)^{-1} . sqrt(shom_n) ,
```

at `sigma_0 = shom_{n+h-1}`.  `Closure.GammaTenStripEnvelopeTwoLeg` carries
`|c_1| <= C_g` and `|c_2| <= C_g` as binders and no producer exists.  The
proved `PrincipalResponseComposeDisplayTwo.gaugeRatio_sigmaBar_le_readingConst`
caps the **ratio** `max(shom_{n+h-1}/shom_n, shom_n/shom_{n+h-1})` by the
absolute `4 . 3^9`; each `|c_i|` is the square root of one of those two
quotients, and a square root of a number above `1` is below the number itself.
That is the whole content.

## What is proved

* `sqrt_le_self_of_one_le` --- `sqrt C <= C` for `1 <= C`.
* `abs_sqrt_mul_inv_sqrt_le` --- `|sqrt a . (sqrt b)^{-1}| <= C` from
  `a / b <= C` and `1 <= C`, for positive `a`, `b`.
* `abs_gaugeScalar_potential_le`, `abs_gaugeScalar_flux_le` --- the two caps at
  the closure's own pair of gauges, from the proved ratio cap carried as the
  binder `hgauge`.

## Binders

Only `hgauge`, the same binder
`Closure.GammaTenCloserGauge.blockVecNormSum_blockGaugeUp_le_gammaTenGaugeConst`
already carries and which `Closure.ClosureInteriorSplit` discharges inline from
`PrincipalResponseComposeDisplayTwo.gaugeRatio_sigmaBar_le_readingConst`.  No
smallness gate, no moment, no measurability and no sample-space proposition
occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `e.shom.h.bounds`, `l.approximate.recurrence.formula` Step 2,
  `e.Fz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## Two elementary steps -/

/-- A square root of a number at least `1` is at most that number. -/
theorem sqrt_le_self_of_one_le {C : ℝ} (hC : 1 ≤ C) : Real.sqrt C ≤ C := by
  have h0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg C, sq_nonneg (Real.sqrt C - 1)]

/-- **The scalar gauge factor is the square root of the gauge quotient**, hence
capped by any cap at least `1` on that quotient.

on `ha`, `hb`, `hC` and `hab`. -/
theorem abs_sqrt_mul_inv_sqrt_le {a b C : ℝ} (ha : 0 ≤ a) (hC : 1 ≤ C)
    (hab : a / b ≤ C) : |Real.sqrt a * (Real.sqrt b)⁻¹| ≤ C := by
  have hquot : Real.sqrt a * (Real.sqrt b)⁻¹ = Real.sqrt (a / b) := by
    rw [div_eq_mul_inv, Real.sqrt_mul ha, Real.sqrt_inv]
  rw [hquot, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_trans (Real.sqrt_le_sqrt hab) (sqrt_le_self_of_one_le hC)

/-! ## The two caps at the closure's pair of gauges -/

/-- **The potential leg's scalar gauge factor is capped by `4 . 3^9`.**

on `hgauge`. -/
theorem abs_gaugeScalar_potential_le (M : ABKModel d) (n : ℤ) (h : ℕ)
    (hgauge : gaugeRatio (Annealed.sigmaBar M n)
        (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤ 4 * (3 : ℝ) ^ (9 : ℕ)) :
    |Real.sqrt (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ) *
        (Real.sqrt (Annealed.sigmaBar M n : ℝ))⁻¹| ≤ 4 * (3 : ℝ) ^ (9 : ℕ) := by
  refine abs_sqrt_mul_inv_sqrt_le
    (le_of_lt (Annealed.sigmaBar M (n + (h : ℤ) - 1)).2) (by norm_num) ?_
  refine le_trans ?_ hgauge
  exact le_max_left _ _

/-- **The flux leg's scalar gauge factor is capped by `4 . 3^9`.**

on `hgauge`. -/
theorem abs_gaugeScalar_flux_le (M : ABKModel d) (n : ℤ) (h : ℕ)
    (hgauge : gaugeRatio (Annealed.sigmaBar M n)
        (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤ 4 * (3 : ℝ) ^ (9 : ℕ)) :
    |(Real.sqrt (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ))⁻¹ *
        Real.sqrt (Annealed.sigmaBar M n : ℝ)| ≤ 4 * (3 : ℝ) ^ (9 : ℕ) := by
  have hcomm : (Real.sqrt (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ))⁻¹ *
      Real.sqrt (Annealed.sigmaBar M n : ℝ) =
      Real.sqrt (Annealed.sigmaBar M n : ℝ) *
        (Real.sqrt (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ))⁻¹ := by
    ring
  rw [hcomm]
  refine abs_sqrt_mul_inv_sqrt_le (le_of_lt (Annealed.sigmaBar M n).2) (by norm_num) ?_
  refine le_trans ?_ hgauge
  exact le_max_right _ _

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
