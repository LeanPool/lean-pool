/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ShellIncrementCap
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration.Core

/-!
# TwoSidedTargets

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.what.do.we.have`: the two one-sided targets, and their consumption shape

This module does two things and nothing else.

1. It **transcribes** the two displayed inequalities of `e.what.do.we.have` at
   the repository's own carriers: the genuine running diffusivity
   `Annealed.sigmaBar` and the recurrence pair `(n, n+h)`.  Nothing is asserted
   about them here --- they are `Prop`-valued definitions, the statements that
   the two-sided closure of `l.approximate.recurrence.formula` has to
   produce.

2. It proves, **unconditionally**, that those two displays deliver exactly the
   two hypotheses `hupper` and `hlower` of
   `RecurrenceIntegration.integrate_approx_recurrence`, at the sequence
   `s = fun m => (Annealed.sigmaBar M m : ℝ)`.  This is the carrier match the
   root assembly needs, and it is pure arithmetic: no measure, no corrector, no
   in-flight endpoint.

## The printed displays

```
  shom_{n+h} shom_n^{-1}
    <= 1 + (log 3) cstar shom_n^{-2} sum_{k=n+1}^{n+h} 3^{2 cgamma k}
         + C E^2 |log cgamma|^2 cgamma ,
  shom_n shom_{n+h}^{-1}
    <= 1 - (log 3) cstar shom_n^{-2} sum_{k=n+1}^{n+h} 3^{2 cgamma k}
         + C h^2 shom_n^{-4} 3^{4 cgamma (n+h)}
         + C E^2 |log cgamma|^2 cgamma .
```

`|log cgamma|^2` is rendered `Real.log M.gamma ^ 2` --- the square of the log,
which equals the square of its absolute value --- so that the shape agrees
verbatim with `principalResponseSwitchBudget`, the budget the principal-response
terminal produces.  The drift `(log 3) cstar shom_n^{-2} sum ...` is
`Closure.shellDrift`, and it is exactly `shom_n^{-2}` times the `A_{n,m}` of
`e.A.def` (`RecurrenceIntegration.recurrenceIncrement`); `shellDrift_eq` records
that identity.

## The asymmetry of the two bridges

`hupper` follows from the upper display alone.  `hlower` needs **both**: the
printed lower display carries its error flat and against the *ratio*, while
`e.assump.lower.modified` carries it against `s n`.  Converting costs a bound
on `shom_{n+h} shom_n^{-1}`, and the cheapest such bound is the upper display
itself together with the absolute cap `shellIncrementCap`.

## References

* ABK26, `e.what.do.we.have`.
* ABK26, `e.assump.upper`, `e.assump.lower.modified`, `e.A.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

noncomputable section

variable {d : ℕ}

/-! ## The printed error budget -/

/-- The printed flat error `C E^2 |log cgamma|^2 cgamma` of both lines of
`e.what.do.we.have`. -/
def recurrenceFlatError (M : ABKModel d) (C E : ℝ) : ℝ :=
  C * E ^ 2 * Real.log M.gamma ^ 2 * M.gamma

theorem recurrenceFlatError_nonneg (M : ABKModel d) {C E : ℝ} (hC : 0 ≤ C) :
    0 ≤ recurrenceFlatError M C E := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  unfold recurrenceFlatError
  positivity

/-! ## The two displays -/

/-- **The first line of `e.what.do.we.have`.**

```
  shom_{n+h} shom_n^{-1}
    <= 1 + (log 3) cstar shom_n^{-2} sum_{k=n+1}^{n+h} 3^{2 cgamma k}
         + C E^2 |log cgamma|^2 cgamma .
```
-/
def RecurrenceUpperDisplay (M : ABKModel d) (C E : ℝ) (n : ℤ) (h : ℕ) : Prop :=
  (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
    1 + shellDrift M n h + recurrenceFlatError M C E

/-- **The second line of `e.what.do.we.have`.**

```
  shom_n shom_{n+h}^{-1}
    <= 1 - (log 3) cstar shom_n^{-2} sum_{k=n+1}^{n+h} 3^{2 cgamma k}
         + C h^2 shom_n^{-4} 3^{4 cgamma (n+h)}
         + C E^2 |log cgamma|^2 cgamma .
```

The manuscript prints one and the same `C` in front of the quadratic `h`-error
and in front of the flat error; that is transcribed literally. -/
def RecurrenceLowerDisplay (M : ABKModel d) (C E : ℝ) (n : ℤ) (h : ℕ) : Prop :=
  (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M (n + (h : ℤ)) : ℝ))⁻¹ ≤
    1 - shellDrift M n h
      + C * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
      + recurrenceFlatError M C E

/-! ## The degenerate shell `h = 0`

The manuscript quantifies over `h in N`.  At `h = 0` the shell of `e.def.w` is
empty, both correctors vanish and both printed lines reduce to `1 <= 1 + error`.
Proving that case here means the closure node's own proof may assume `0 < h`
without weakening the contract. -/

theorem shellDrift_zero (M : ABKModel d) (n : ℤ) : shellDrift M n 0 = 0 := by
  unfold shellDrift
  have hempty : Finset.Icc (n + 1) (n + ((0 : ℕ) : ℤ)) = ∅ :=
    Finset.Icc_eq_empty (by omega)
  rw [hempty]
  simp

theorem recurrenceUpperDisplay_zero (M : ABKModel d) {C E : ℝ} (hC : 0 ≤ C)
    (n : ℤ) : RecurrenceUpperDisplay M C E n 0 := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hn : n + ((0 : ℕ) : ℤ) = n := by omega
  unfold RecurrenceUpperDisplay
  rw [shellDrift_zero, hn, mul_inv_cancel₀ hpos.ne']
  linarith [recurrenceFlatError_nonneg M (E := E) hC]

theorem recurrenceLowerDisplay_zero (M : ABKModel d) {C E : ℝ} (hC : 0 ≤ C)
    (n : ℤ) : RecurrenceLowerDisplay M C E n 0 := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hn : n + ((0 : ℕ) : ℤ) = n := by omega
  unfold RecurrenceLowerDisplay
  rw [shellDrift_zero, hn, mul_inv_cancel₀ hpos.ne']
  have hzero : C * (((0 : ℕ) : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
      (3 : ℝ) ^ (4 * M.gamma * ((n : ℤ) : ℝ)) = 0 := by
    simp
  rw [hzero]
  linarith [recurrenceFlatError_nonneg M (E := E) hC]

/-! ## The drift is the `e.A.def` increment, gauged -/

/-- `shellDrift` is `shom_n^{-2}` times the increment `A_{n,m}` of `e.A.def`, at `m
= n + h`. -/
theorem shellDrift_eq (M : ABKModel d) (n : ℤ) (h : ℕ) :
    shellDrift M n h =
      recurrenceIncrement (Disorder.cstar M) M.gamma n (n + (h : ℤ)) *
        (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ := by
  unfold shellDrift recurrenceIncrement
  ring

/-! ## The upper bridge -/

/-- **`e.assump.upper` from the printed upper display.**

Multiplying the ratio display by `shom_n > 0` converts it verbatim into the
hypothesis `hupper` of `integrate_approx_recurrence`, with

```
  E_integration cgamma  =  C E^2 |log cgamma|^2 cgamma .
```

Unconditional: the only binder is the display itself. -/
theorem sigmaBar_le_of_upperDisplay (M : ABKModel d) {C E : ℝ} {n : ℤ} {h : ℕ}
    (hup : RecurrenceUpperDisplay M C E n h) :
    (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) ≤
      (1 + recurrenceFlatError M C E) * (Annealed.sigmaBar M n : ℝ) +
        recurrenceIncrement (Disorder.cstar M) M.gamma n (n + (h : ℤ)) *
          ((Annealed.sigmaBar M n : ℝ))⁻¹ := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hmul := mul_le_mul_of_nonneg_right hup hpos.le
  rw [shellDrift_eq] at hmul
  have hcancel : (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) *
      ((Annealed.sigmaBar M n : ℝ))⁻¹ * (Annealed.sigmaBar M n : ℝ) =
      (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  refine le_trans hmul (le_of_eq ?_)
  field_simp
  ring

/-! ## The ratio cap -/

/-- The upper display, together with the absolute drift cap, bounds the
diffusivity ratio by an explicit constant.  This is what the lower bridge spends
to move the flat error from the ratio onto `shom_n`. -/
theorem sigmaBar_ratio_le (M : ABKModel d) {C E : ℝ} {n : ℤ} {h : ℕ}
    (hup : RecurrenceUpperDisplay M C E n h)
    (hcap : shellDrift M n h ≤ shellIncrementCap)
    (herr : recurrenceFlatError M C E ≤ 1) :
    (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) ≤
      (2 + shellIncrementCap) * (Annealed.sigmaBar M n : ℝ) := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hchain : (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) *
      ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤ 2 + shellIncrementCap := by
    refine le_trans hup ?_
    linarith [hcap, herr]
  have hmul := mul_le_mul_of_nonneg_right hchain hpos.le
  have hcancel : (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) *
      ((Annealed.sigmaBar M n : ℝ))⁻¹ * (Annealed.sigmaBar M n : ℝ) =
      (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) := by
    field_simp
  rwa [hcancel] at hmul

/-! ## The lower bridge -/

/-- **`e.assump.lower.modified` from the two printed displays.**

The conclusion is exactly the `hlower` hypothesis of
`integrate_approx_recurrence` at

```
  s          = fun m => (Annealed.sigmaBar M m : R) ,
  A_{n,m}    = recurrenceIncrement (cstar M) cgamma n (n+h) ,
  E_integration = (2 + shellIncrementCap) C E^2 |log cgamma|^2 ,
  F             = C .
```

`hup` is needed only through the ratio cap: it is what turns the printed
ratio-carried error into an error carried by `s n`, at the cost of the single
factor `2 + shellIncrementCap`.  Unconditional otherwise. -/
theorem sigmaBar_ge_of_displays (M : ABKModel d) {C E : ℝ} {n : ℤ} {h : ℕ}
    (hC : 0 ≤ C)
    (hup : RecurrenceUpperDisplay M C E n h)
    (hlo : RecurrenceLowerDisplay M C E n h)
    (hcap : shellDrift M n h ≤ shellIncrementCap)
    (herr : recurrenceFlatError M C E ≤ 1) :
    (1 - (2 + shellIncrementCap) * (C * E ^ 2 * Real.log M.gamma ^ 2) * M.gamma) *
          (Annealed.sigmaBar M n : ℝ) +
        recurrenceIncrement (Disorder.cstar M) M.gamma n (n + (h : ℤ)) *
          (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 *
          (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) -
        C * (((n + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) ^ 2 *
          (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
          (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) ≤
      (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) := by
  have hposn : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hposm : (0 : ℝ) < (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) :=
    (Annealed.sigmaBar M (n + (h : ℤ))).2
  -- multiply the printed lower display by `shom_{n+h} > 0`
  have hmul := mul_le_mul_of_nonneg_right hlo hposm.le
  rw [shellDrift_eq] at hmul
  have hcancel : (Annealed.sigmaBar M n : ℝ) *
      ((Annealed.sigmaBar M (n + (h : ℤ)) : ℝ))⁻¹ *
      (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) = (Annealed.sigmaBar M n : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  -- rewrite the two gauge powers as powers of the inverse
  have hinv2 : (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ =
      (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 := by
    rw [inv_pow]
  have hinv4 : (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ =
      (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 := by
    rw [inv_pow]
  rw [hinv2, hinv4] at hmul
  -- the printed `h^2` and the integration lemma's `(m - n)^2` are the same number
  have hhcast : (((n + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) = ((h : ℝ)) := by
    push_cast
    ring
  rw [hhcast]
  -- the flat error is moved from `shom_{n+h}` onto `shom_n`
  have hratio := sigmaBar_ratio_le M hup hcap herr
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hbudget0 : (0 : ℝ) ≤ C * E ^ 2 * Real.log M.gamma ^ 2 * M.gamma := by
    positivity
  have hmove : recurrenceFlatError M C E * (Annealed.sigmaBar M (n + (h : ℤ)) : ℝ) ≤
      (2 + shellIncrementCap) * (C * E ^ 2 * Real.log M.gamma ^ 2) * M.gamma *
        (Annealed.sigmaBar M n : ℝ) := by
    have hstep := mul_le_mul_of_nonneg_left hratio hbudget0
    unfold recurrenceFlatError
    nlinarith [hstep]
  nlinarith [hmul, hmove]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
