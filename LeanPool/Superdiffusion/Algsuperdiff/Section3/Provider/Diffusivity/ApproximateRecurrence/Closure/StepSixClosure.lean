/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.StepSixArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.TwoSidedTargets
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePDef

/-!
# StepSixClosure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 6 at the carriers: from the annealed block bound to the printed displays

Step 6 of `l.approximate.recurrence.formula` reads the doubled quadratic form
of `bfAhom_m` at the probe load `P = bfAhom_{m-h}^{-1/2}(e'; e)` in two
special directions:

* `e = 0`, `|e'| = 1`, where the form collapses to `shom_m shom_{m-h}^{-1}`;
* `e' = 0`, `|e| = 1`, where it collapses to the reciprocal.

This module bolts them onto the arithmetic fold of `Closure.StepSixArithmetic`
and produces the two printed displays `RecurrenceUpperDisplay` and
`RecurrenceLowerDisplay` of `Closure.TwoSidedTargets`.

Everything here is **unconditional real arithmetic at the genuine carriers**: no
measure, no corrector, no localization scale, no in-flight endpoint.  What the
two theorems still take as binders is exactly the numeric content the two
predecessor lanes owe:

* `hswitch`, the outcome of Steps 1--3 and the limit passage --- the doubled form
  bounded by `(1 + delta) * gauge + rem` --- and
* `hgauge`, the outcome of Step 4 (upper leg) or Step 5 (lower leg).

The junction module `Closure.Junctions` names the producers of both.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 6.
* ABK26, `e.what.do.we.have`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The upper leg -/

/-- **The first line of `e.what.do.we.have`, from the annealed block bound.**

`hswitch` is the `e = 0` reading of Step 6's opening chain: the doubled form of
`bfAhom_{n+h}` at `P = bfAhom_n^{-1/2}(e'; 0)` bounded by `(1 + delta) * gauge
+ rem`.  `hgauge` is `e.lower.bound.pre1`.

Unconditional: every binder is either a numeric inequality or the unit
normalization `|e'| = 1`. -/
theorem upperDisplay_of_annealedBlockBound (M : ABKModel d) {C E delta gauge rem : ℝ}
    {n : ℤ} {h : ℕ} {e' : Vec d} (he' : vecNormSq e' = 1)
    (hdelta : 0 ≤ delta)
    (hcap : shellDrift M n h ≤ shellIncrementCap)
    (hswitch : blockVecDot (recurrenceP (Annealed.sigmaBar M n) 0 e')
        (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M (n + (h : ℤ))))
          (recurrenceP (Annealed.sigmaBar M n) 0 e')) ≤ (1 + delta) * gauge + rem)
    (hgauge : gauge ≤ 1 + shellDrift M n h)
    (habsorb : (1 + shellIncrementCap) * delta + rem ≤ recurrenceFlatError M C E) :
    RecurrenceUpperDisplay M C E n h := by
  rw [blockVecDot_recurrenceP_annealedLimitBlock_potential_unit _ _ he',
    div_eq_mul_inv] at hswitch
  have hfold := ratio_le_of_switch_upper hdelta hcap hswitch hgauge
  unfold RecurrenceUpperDisplay
  linarith [hfold, habsorb]

/-! ## The lower leg -/

/-- **The second line of `e.what.do.we.have`, from the annealed block bound.**

`hswitch` is the `e' = 0` reading of Step 6's opening chain; `hgauge` is
`e.lower.bound.pre2` in its three-summand form `1 - drift + cross + osc`, with
`cross` the quadratic `h`-error and `osc` the `cgamma^15` oscillation remainder
of `e.lower.bound.oscillations`.

`habsorbCross` moves `2 * cross` under the printed `C h^2 shom_n^{-4} 3^{4
cgamma (n+h)}`, and `habsorbFlat` moves the rest under the printed flat error.

Unconditional. -/
theorem lowerDisplay_of_annealedBlockBound (M : ABKModel d)
    {C E delta gauge rem cross osc : ℝ}
    {n : ℤ} {h : ℕ} {e : Vec d} (he : vecNormSq e = 1)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hcross : 0 ≤ cross) (hosc : 0 ≤ osc)
    (hswitch : blockVecDot (recurrenceP (Annealed.sigmaBar M n) e 0)
        (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M (n + (h : ℤ))))
          (recurrenceP (Annealed.sigmaBar M n) e 0)) ≤ (1 + delta) * gauge + rem)
    (hgauge : gauge ≤ 1 - shellDrift M n h + cross + osc)
    (habsorbCross : 2 * cross ≤
      C * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
        (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)))
    (habsorbFlat : 2 * osc + delta + rem ≤ recurrenceFlatError M C E) :
    RecurrenceLowerDisplay M C E n h := by
  rw [blockVecDot_recurrenceP_annealedLimitBlock_flux_unit _ _ he,
    div_eq_mul_inv] at hswitch
  have hA : 0 ≤ shellDrift M n h := shellDrift_nonneg M n h
  have hfold :=
    ratio_le_of_switch_lower hdelta hdelta1 hA hcross hosc hswitch hgauge
  unfold RecurrenceLowerDisplay
  linarith [hfold, habsorbCross, habsorbFlat]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
