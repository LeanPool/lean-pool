/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# StepSixArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 6 of `l.approximate.recurrence.formula`: the deterministic fold

Step 6 combines three inputs into the two printed one-sided estimates of
`e.what.do.we.have`:

* the basic split and its localization remainder (`e.lower.bound.basic.split`,
  `e.lower.bound.localization.terms`), contributing an additive `cgamma^10`;
* the principal comparison `e.lower.bound.principal.one`, which supplies the
  multiplicative switch factor `1 +^2 |log cgamma|^2 cgamma` and an additive
  `cgamma^6`;
* the two gauge estimates `e.lower.bound.pre1` and `e.lower.bound.pre2`.

Once those are in hand the passage to the printed displays is *pure real
arithmetic*: one distributes the switch factor over the gauge bound and folds
the products back into the printed error terms.  This module proves exactly that
arithmetic, over abstract reals, with no model, no measure and no carrier.

## The two folds

* `ratio_le_of_switch_upper` --- the `e = 0` branch.  From
  `ratio <= (1 + delta) * gauge + rem` and `gauge <= 1 + A` one gets
  `ratio <= 1 + A + ((1 + Acap) * delta + rem)`, the printed upper display with
  its flat error.  The cap `Acap` on the shell increment is what makes the
  cross term `delta * A` foldable into a flat error; it is supplied at the
  carriers by `Closure.ShellIncrementCap`.
* `ratio_le_of_switch_lower` --- the `e' = 0` branch.  From `ratio <= (1 +
  delta) * gauge + rem` and `gauge <= 1 - A + cross + osc` one gets `ratio <= 1
  - A + 2 * cross + (2 * osc + delta + rem)`.  Here the sign of the drift is
  what does the work: `-delta * A <= 0`, so the cross term is dropped rather
  than capped, and no bound on `A` is needed on this side.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 6.
* ABK26, `e.what.do.we.have`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

/-! ## The upper fold -/

/-- **Step 6, the `e = 0` branch, as real arithmetic.**

`ratio` is `shom_m shom_{m-h}^{-1}`; `delta` is the switch excess `C E^2 |log
cgamma|^2 cgamma` of `e.lower.bound.principal.one`; `rem` collects the additive
remainders `cgamma^6 + cgamma^10`; `gauge` is the left-hand side of
`e.lower.bound.pre1`; and `A` is the signed shell increment `(log 3) cstar
shom_{m-h}^{-2} sum_{k=m-h+1}^m 3^{2 cgamma k}`.

The conclusion is the printed upper display with the flat error
`(1 + Acap) * delta + rem`. -/
theorem ratio_le_of_switch_upper {ratio delta gauge rem A Acap : ℝ}
    (hdelta : 0 ≤ delta) (hAcap : A ≤ Acap)
    (hswitch : ratio ≤ (1 + delta) * gauge + rem)
    (hgauge : gauge ≤ 1 + A) :
    ratio ≤ 1 + A + ((1 + Acap) * delta + rem) := by
  have hfac : (0 : ℝ) ≤ 1 + delta := by linarith
  have h1 : (1 + delta) * gauge ≤ (1 + delta) * (1 + A) :=
    mul_le_mul_of_nonneg_left hgauge hfac
  have h2 : delta * A ≤ delta * Acap := mul_le_mul_of_nonneg_left hAcap hdelta
  nlinarith [hswitch, h1, h2]

/-! ## The lower fold -/

/-- **Step 6, the `e' = 0` branch, as real arithmetic.**

`ratio` is `shom_{m-h} shom_m^{-1}`; `gauge` is the left-hand side of
`e.lower.bound.pre2`; `A` is the same signed shell increment as above, now
entering with a minus sign; `cross` is the quadratic `h`-error
`C h^2 shom_{m-h}^{-4} 3^{4 cgamma m}`; `osc` is the `cgamma^15` oscillation
remainder of `e.lower.bound.oscillations`.

The hypotheses `0 <= A`, `0 <= cross`, `0 <= osc` and `delta <= 1` are the
manuscript's own standing facts (`A` is a limit of expected energies, `cross`
and `osc` are norms, and `delta` is small by `e.cgamma.constraints`). -/
theorem ratio_le_of_switch_lower {ratio delta gauge rem A cross osc : ℝ}
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hA : 0 ≤ A)
    (hcross : 0 ≤ cross) (hosc : 0 ≤ osc)
    (hswitch : ratio ≤ (1 + delta) * gauge + rem)
    (hgauge : gauge ≤ 1 - A + cross + osc) :
    ratio ≤ 1 - A + 2 * cross + (2 * osc + delta + rem) := by
  have hfac : (0 : ℝ) ≤ 1 + delta := by linarith
  have h1 : (1 + delta) * gauge ≤ (1 + delta) * (1 - A + cross + osc) :=
    mul_le_mul_of_nonneg_left hgauge hfac
  have h2 : (0 : ℝ) ≤ delta * A := mul_nonneg hdelta hA
  have h3 : delta * cross ≤ cross := by nlinarith
  have h4 : delta * osc ≤ osc := by nlinarith
  nlinarith [hswitch, h1, h2, h3, h4]

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
