/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.NodeContract
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Junctions

/-!
# ClosureFinalArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The closure node's parameter arithmetic

ABK26, `l.approximate.recurrence.formula`, (the standing hypotheses and
the quantifier range) and `e.cgamma.constraints`.

`Closure.NodeContract.TwoSidedClosure` quantifies its constant `C` *outside* the
model and uses it twice: as the largeness threshold `C c⋆^{-1} <= E` of the
standing hypothesis, and as the constant of the two printed displays.  The two
uses pull in opposite directions --- a larger `C` strengthens the hypothesis and
weakens the conclusion --- so the node's proof is free to enlarge `C`.  This
module carries the four pieces of bookkeeping that enlargement needs.

## What is supplied

* `inductionState_mono` --- the induction state is downward closed in its scale
  parameter.  `Frozen.Section3.inductionState` is literally two `forall m <= m0`
  clauses, so this is immediate; the closure node needs it to feed the state at
  `m0 - 1` into producers that ask for it at `n + h - 1`.
* `recurrenceUpperDisplay_mono`, `recurrenceLowerDisplay_mono` --- both printed
  displays are monotone in the constant `C`.  This is what lets the closure
  merge the upper display's `closureConstant` with the lower display's
  `max closureConstant (2 F)`.
* `closureRegimeConst` and the two regime facts
  `gamma_le_exp_neg_one_of_regime`, `three_mul_switchBudget_le_one_of_regime`:
  at a large enough absolute threshold `C`, the manuscript's own standing
  hypotheses `C c⋆^{-1} <= E` and `cgamma <= E^{-5}` already give the two
  smallness facts grants, namely `cgamma <= e^{-1}` and `3 *
  principalResponseSwitchBudget M <= 1`.  Neither is assumed anywhere below:
  both are *derived* from the contract's own antecedents.

## The two regime derivations

Write `K0 = principalResponseBudgetConst * 3^128`, so that
`principalResponseSwitchBudget M = K0 E^2 (log cgamma)^2 cgamma`.

`c⋆ <= 3/2` (`Disorder.cstar_le_three_halves`), so `C c⋆^{-1} <= E` gives
`E >= 2C/3`; and `E >= 1` with `cgamma <= E^{-5}` gives `cgamma <= E^{-1}`.
Hence `cgamma <= 3/(2C) <= 1/3 <= e^{-1}` as soon as `C >= 9/2`.

For the budget, put `t = sqrt (sqrt cgamma)`, so `t^4 = cgamma` and
`log cgamma = 4 log t`.  From `log u <= u - 1` at `u = t^{-1}`,
`-log t <= t^{-1}`, so `(log cgamma)^2 <= 16 t^{-2}` and

```
  cgamma (log cgamma)^2 <= t^4 . 16 t^{-2} = 16 t^2 = 16 sqrt cgamma .
```

With `cgamma <= E^{-5}` and `sqrt (E^5) = E^2 sqrt E`,
`E^2 sqrt cgamma <= (sqrt E)^{-1}`, so

```
  3 principalResponseSwitchBudget M E 64 <= 48 K0 (sqrt E)^{-1} <= 1
```

as soon as `sqrt E >= 48 K0`, which `E >= 2C/3 >= (48 K0)^2` gives.
`closureRegimeConst` is `9 + (3/2)(48 K0)^2`, which covers both.

## References

* ABK26, `l.approximate.recurrence.formula`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## The induction state is downward closed -/

/-- **`Frozen.Section3.inductionState` is downward closed in its scale.**

The frozen definition is two clauses of the form `forall m, m <= m0 -> ...`, so
lowering `m0` only shrinks the range of both. -/
theorem inductionState_mono {M : ABKModel d} {m0 m1 : ℤ}
    {Ec : {E : ℝ // 1 ≤ E}} (hle : m1 ≤ m0)
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M m0 Ec) :
    Algsuperdiff.Frozen.Section3.inductionState M m1 Ec :=
  ⟨fun m hm => hstate.1 m (le_trans hm hle), fun m hm => hstate.2 m (le_trans hm hle)⟩

/-! ## The two displays are monotone in the constant -/

/-- The flat error is monotone in the constant. -/
theorem recurrenceFlatError_mono (M : ABKModel d) {C C' E : ℝ} (hCC : C ≤ C') :
    recurrenceFlatError M C E ≤ recurrenceFlatError M C' E := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hbase : (0 : ℝ) ≤ E ^ 2 * Real.log M.gamma ^ 2 * M.gamma := by positivity
  unfold recurrenceFlatError
  calc C * E ^ 2 * Real.log M.gamma ^ 2 * M.gamma
      = C * (E ^ 2 * Real.log M.gamma ^ 2 * M.gamma) := by ring
    _ ≤ C' * (E ^ 2 * Real.log M.gamma ^ 2 * M.gamma) :=
        mul_le_mul_of_nonneg_right hCC hbase
    _ = C' * E ^ 2 * Real.log M.gamma ^ 2 * M.gamma := by ring

/-- **The upper display is monotone in the constant.** -/
theorem recurrenceUpperDisplay_mono (M : ABKModel d) {C C' E : ℝ} {n : ℤ} {h : ℕ}
    (hCC : C ≤ C') (hup : RecurrenceUpperDisplay M C E n h) :
    RecurrenceUpperDisplay M C' E n h := by
  have hmono := recurrenceFlatError_mono M (E := E) hCC
  unfold RecurrenceUpperDisplay at hup ⊢
  linarith

/-- **The lower display is monotone in the constant.** -/
theorem recurrenceLowerDisplay_mono (M : ABKModel d) {C C' E : ℝ} {n : ℤ} {h : ℕ}
    (hCC : C ≤ C') (hlo : RecurrenceLowerDisplay M C E n h) :
    RecurrenceLowerDisplay M C' E n h := by
  have hmono := recurrenceFlatError_mono M (E := E) hCC
  have hs : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hr := Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num)
    (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
  have hbase : (0 : ℝ) ≤ ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
      (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by positivity
  have hquad : C * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
        (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) ≤
      C' * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
        (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by
    calc C * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
        = C * (((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) := by ring
      _ ≤ C' * (((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hCC hbase
      _ = C' * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
            (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ)) := by ring
  unfold RecurrenceLowerDisplay at hlo ⊢
  linarith

/-! ## The regime threshold -/

/-- The absolute threshold at which the manuscript's standing hypotheses `C c⋆^{-1}
<= E` and `cgamma <= E^{-5}` already deliver the two smallness facts grants.
It depends on nothing. -/
def closureRegimeConst : ℝ :=
  9 + (3 / 2) * (48 * (principalResponseBudgetConst * 3 ^ (128 : ℕ))) ^ 2

theorem closureRegimeConst_pos : 0 < closureRegimeConst := by
  have h1 : (0 : ℝ) < principalResponseBudgetConst := principalResponseBudgetConst_pos
  have h2 : (0 : ℝ) ≤ (3 / 2 : ℝ) * (48 * (principalResponseBudgetConst * 3 ^ (128 : ℕ))) ^ 2 := by
    positivity
  unfold closureRegimeConst
  linarith

/-! ### The regime lower bound on `E` -/

/-- From the contract's own two antecedents, `E` is at least `2C/3`. -/
theorem two_thirds_mul_le_of_regime (M : ABKModel d) {C : ℝ} (hC : 0 ≤ C)
    {Ec : {E : ℝ // 1 ≤ E}} (hCE : C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ)) :
    2 / 3 * C ≤ (Ec : ℝ) := by
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcstar32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hinv : (2 / 3 : ℝ) ≤ (Disorder.cstar M)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcstar0]
    calc Disorder.cstar M ≤ 3 / 2 := hcstar32
      _ = (2 / 3 : ℝ)⁻¹ := by norm_num
  calc 2 / 3 * C = C * (2 / 3 : ℝ) := by ring
    _ ≤ C * (Disorder.cstar M)⁻¹ := mul_le_mul_of_nonneg_left hinv hC
    _ ≤ (Ec : ℝ) := hCE

/-- `cgamma <= E^{-5}` and `E >= 1` give `cgamma <= E^{-1}`. -/
theorem gamma_le_inv_of_regime (M : ABKModel d) {Ec : {E : ℝ // 1 ≤ E}}
    (hgammaE : M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ)) : M.gamma ≤ ((Ec : ℝ))⁻¹ := by
  have hE1 : (1 : ℝ) ≤ (Ec : ℝ) := Ec.2
  have hE0 : (0 : ℝ) < (Ec : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  have hpow : (Ec : ℝ) ≤ (Ec : ℝ) ^ (5 : ℕ) := by
    calc (Ec : ℝ) = (Ec : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (Ec : ℝ) ^ (5 : ℕ) := pow_le_pow_right₀ hE1 (by norm_num)
  have hzpow : (Ec : ℝ) ^ (-5 : ℤ) = ((Ec : ℝ) ^ (5 : ℕ))⁻¹ := by
    rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  rw [hzpow] at hgammaE
  refine le_trans hgammaE ?_
  have h := one_div_le_one_div_of_le hE0 hpow
  rwa [one_div, one_div] at h

/-! ### The two regime facts -/

/-- **`cgamma <= e^{-1}` is a consequence of the contract's own antecedents**,
at the absolute threshold `closureRegimeConst`. -/
theorem gamma_le_exp_neg_one_of_regime (M : ABKModel d) {C : ℝ}
    (hCbig : closureRegimeConst ≤ C) {Ec : {E : ℝ // 1 ≤ E}}
    (hCE : C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ))
    (hgammaE : M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ)) :
    M.gamma ≤ Real.exp (-1) := by
  have hK0 : (0 : ℝ) < principalResponseBudgetConst := principalResponseBudgetConst_pos
  have hsq : (0 : ℝ) ≤ (3 / 2 : ℝ) * (48 * (principalResponseBudgetConst * 3 ^ (128 : ℕ))) ^ 2 := by
    positivity
  have hC9 : (9 : ℝ) ≤ C := by
    have : (9 : ℝ) ≤ closureRegimeConst := by unfold closureRegimeConst; linarith
    linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hEbig := two_thirds_mul_le_of_regime M hC0 hCE
  have hE6 : (6 : ℝ) ≤ (Ec : ℝ) := by linarith
  have hE0 : (0 : ℝ) < (Ec : ℝ) := by linarith
  have hinv : ((Ec : ℝ))⁻¹ ≤ 1 / 6 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hE0 (by norm_num)]
    linarith
  have hgi := gamma_le_inv_of_regime M hgammaE
  have hexp : (1 : ℝ) / 6 ≤ Real.exp (-1) := by
    have h1 : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := by
      rw [Real.exp_neg]
    have h4 : (2.7182818286 : ℝ) ≤ ((1 : ℝ) / 6)⁻¹ := by norm_num
    rw [h3, le_inv_comm₀ (by norm_num) h2]
    linarith
  linarith [hgi, hinv, hexp]

/-- An elementary logarithmic bound: for `0 < g <= 1`,
`g (log g)^2 <= 16 sqrt g`. -/
theorem mul_log_sq_le_sixteen_mul_sqrt {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    g * Real.log g ^ 2 ≤ 16 * Real.sqrt g := by
  set t : ℝ := Real.sqrt (Real.sqrt g) with ht
  have hsq0 : 0 < Real.sqrt g := Real.sqrt_pos.2 hg0
  have ht0 : 0 < t := Real.sqrt_pos.2 hsq0
  have ht2 : t ^ 2 = Real.sqrt g := Real.sq_sqrt (Real.sqrt_nonneg g)
  have ht4 : t ^ 4 = g := by
    have h : t ^ 4 = (t ^ 2) ^ 2 := by ring
    rw [h, ht2, Real.sq_sqrt hg0.le]
  have hlogt : Real.log g = 4 * Real.log t := by
    rw [← ht4, Real.log_pow]
    norm_num
  have hbound : -Real.log t ≤ t⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t⁻¹ from inv_pos.2 ht0)
    rw [Real.log_inv] at h
    linarith
  have hlognn : 0 ≤ -Real.log g := by
    have := Real.log_nonpos hg0.le hg1
    linarith
  have hleg : -Real.log g ≤ 4 * t⁻¹ := by
    rw [hlogt]
    linarith
  have hsqle : Real.log g ^ 2 ≤ (4 * t⁻¹) ^ 2 := by
    have h : (-Real.log g) ^ 2 ≤ (4 * t⁻¹) ^ 2 := by
      exact pow_le_pow_left₀ hlognn hleg 2
    nlinarith [h]
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hfin : g * (4 * t⁻¹) ^ 2 = 16 * Real.sqrt g := by
    rw [← ht2, ← ht4]
    field_simp
    ring
  calc g * Real.log g ^ 2 ≤ g * (4 * t⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left hsqle hg0.le
    _ = 16 * Real.sqrt g := hfin

/-- **`3 principalResponseSwitchBudget M <= 1` is a consequence of the contract's
own antecedents**, at the absolute threshold `closureRegimeConst`. -/
theorem three_mul_switchBudget_le_one_of_regime (M : ABKModel d) {C : ℝ}
    (hCbig : closureRegimeConst ≤ C) {Ec : {E : ℝ // 1 ≤ E}}
    (hCE : C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ))
    (hgammaE : M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ)) :
    3 * principalResponseSwitchBudget M Ec 64 ≤ 1 := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hK0 : (0 : ℝ) < principalResponseBudgetConst := principalResponseBudgetConst_pos
  set K0 : ℝ := principalResponseBudgetConst * 3 ^ (128 : ℕ) with hK0def
  have hK0pos : (0 : ℝ) < K0 := by rw [hK0def]; positivity
  have hC0 : (0 : ℝ) ≤ C := by
    have := closureRegimeConst_pos
    linarith
  have hEbig := two_thirds_mul_le_of_regime M hC0 hCE
  have hthresh : (48 * K0) ^ 2 ≤ 2 / 3 * C := by
    have h : (3 / 2 : ℝ) * (48 * K0) ^ 2 ≤ C := by
      have h9 : (0 : ℝ) ≤ 9 := by norm_num
      unfold closureRegimeConst at hCbig
      rw [← hK0def] at hCbig
      linarith
    linarith
  have hE1 : (1 : ℝ) ≤ (Ec : ℝ) := Ec.2
  have hE0 : (0 : ℝ) < (Ec : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  have hEsq : (48 * K0) ^ 2 ≤ (Ec : ℝ) := le_trans hthresh hEbig
  -- `sqrt E >= 48 K0`
  have hsqrtE : 48 * K0 ≤ Real.sqrt (Ec : ℝ) := by
    have h := Real.sqrt_le_sqrt hEsq
    rwa [Real.sqrt_sq (by positivity)] at h
  -- `gamma (log gamma)^2 <= 16 sqrt gamma`
  have hgamma1 : M.gamma ≤ 1 := by
    have hgi := gamma_le_inv_of_regime M hgammaE
    have : ((Ec : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; exact hE1
    linarith
  have hlog := mul_log_sq_le_sixteen_mul_sqrt hgamma0 hgamma1
  -- `sqrt gamma <= (E^2 sqrt E)⁻¹`
  have hzpow : (Ec : ℝ) ^ (-5 : ℤ) = ((Ec : ℝ) ^ (5 : ℕ))⁻¹ := by
    rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  have hsqrtpow : Real.sqrt ((Ec : ℝ) ^ (5 : ℕ)) = (Ec : ℝ) ^ 2 * Real.sqrt (Ec : ℝ) := by
    have hrw : (Ec : ℝ) ^ (5 : ℕ) = ((Ec : ℝ) ^ 2) ^ 2 * (Ec : ℝ) := by ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsqrtgamma : Real.sqrt M.gamma ≤ ((Ec : ℝ) ^ 2 * Real.sqrt (Ec : ℝ))⁻¹ := by
    have h := Real.sqrt_le_sqrt (le_trans hgammaE (le_of_eq hzpow))
    rwa [Real.sqrt_inv, hsqrtpow] at h
  have hsqrtE0 : (0 : ℝ) < Real.sqrt (Ec : ℝ) := Real.sqrt_pos.2 hE0
  -- assemble
  have hEsq0 : (0 : ℝ) < (Ec : ℝ) ^ 2 := by positivity
  have hkey : (Ec : ℝ) ^ 2 * (M.gamma * Real.log M.gamma ^ 2) ≤
      16 * (Real.sqrt (Ec : ℝ))⁻¹ := by
    have h1 : (Ec : ℝ) ^ 2 * (M.gamma * Real.log M.gamma ^ 2) ≤
        (Ec : ℝ) ^ 2 * (16 * Real.sqrt M.gamma) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : (Ec : ℝ) ^ 2 * (16 * Real.sqrt M.gamma) ≤
        (Ec : ℝ) ^ 2 * (16 * ((Ec : ℝ) ^ 2 * Real.sqrt (Ec : ℝ))⁻¹) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hsqrtgamma (by norm_num)
    have h3 : (Ec : ℝ) ^ 2 * (16 * ((Ec : ℝ) ^ 2 * Real.sqrt (Ec : ℝ))⁻¹) =
        16 * (Real.sqrt (Ec : ℝ))⁻¹ := by
      field_simp
    linarith
  have hbudget : 3 * principalResponseSwitchBudget M Ec 64 =
      3 * K0 * ((Ec : ℝ) ^ 2 * (M.gamma * Real.log M.gamma ^ 2)) := by
    rw [principalResponseSwitchBudget_eq, hK0def]
    ring
  rw [hbudget]
  have hstep : 3 * K0 * ((Ec : ℝ) ^ 2 * (M.gamma * Real.log M.gamma ^ 2)) ≤
      3 * K0 * (16 * (Real.sqrt (Ec : ℝ))⁻¹) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hfinal : 3 * K0 * (16 * (Real.sqrt (Ec : ℝ))⁻¹) ≤ 1 := by
    rw [mul_comm (16 : ℝ) ((Real.sqrt (Ec : ℝ))⁻¹), ← mul_assoc]
    rw [mul_comm (3 * K0 * (Real.sqrt (Ec : ℝ))⁻¹) (16 : ℝ)]
    rw [show (16 : ℝ) * (3 * K0 * (Real.sqrt (Ec : ℝ))⁻¹) =
      (48 * K0) * (Real.sqrt (Ec : ℝ))⁻¹ by ring]
    rw [mul_inv_le_iff₀ hsqrtE0, one_mul]
    exact hsqrtE
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
