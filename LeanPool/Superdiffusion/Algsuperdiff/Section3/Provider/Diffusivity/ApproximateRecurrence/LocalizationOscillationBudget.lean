/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationParams
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.ShellNormalization

/-!
# LocalizationOscillationBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `gamma^{15}` budget of `e.lower.bound.oscillations`

ABK26, `l.approximate.recurrence.formula`, `e.lower.bound.oscillations`.  The
printed chain ends

```
  ... <= C 3^{-(m-h-n)} + C shom_{m-h}^{-1} 3^{-(m-h-n)} 3^{cgamma(m-h)} cgamma^{-1}
         + C 3^{-(K-m+h)/4}  <=  cgamma^{15} .
```

`LocalizationOscillationDisplay.lean` proves the *first* inequality of that
chain, in the sharper form that carries the buffer gap `N = m - h - n` instead
of `cgamma^{-1}` and has no boundary term (the interior grid carries none).
This module proves the *second* inequality: at the corrected buffer the three
surviving terms fall below `cgamma^{15}` once `cgamma` is below an explicit
threshold.

Everything here is arithmetic over abstract reals or about the two scale
functions of `LocalizationParams`; no field, no measure and no corrector
appears.

## Main results

* `rpow_three_neg_recurrenceGap_le_gamma_pow` -- the gap factor at the *full*
  gap: `3^{-a ceil|log_3 gamma|} <= gamma^a`.  (`LocalizationParams` states the
  quarter-gap form, which is what Step 3 consumes; Step 2's oscillation display
  consumes the full gap.)
* `recurrenceGap_mul_gamma_le` -- the log-loss bound `N gamma <= 3a`.
* `sigmaBarInv_mul_rpow_gamma_shell_le` -- the normalization
  `shom_{m-h}^{-1} 3^{cgamma (m-h)} <= sqrt(24 . 3^18)`, from the deterministic
  head `Corrector.inv_sigmaBarSq_mul_shellWidth_le` and `h >= 1`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport

noncomputable section

/-! ## The gap factor at the full gap -/

/-- **The gap factor at the full corrected gap.**  For every multiplier `a`, `3^{-a
ceil|log_3 gamma|} <= gamma^a` on `0 < gamma <= 1`.  This is the quarter-gap
gate of `LocalizationParams` raised to the fourth power.: on `hgamma0`,
`hgamma1`. -/
theorem rpow_three_neg_recurrenceGap_le_gamma_pow (a : ℕ) {gamma : ℝ}
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    (3 : ℝ) ^ (-((recurrenceGap a gamma : ℕ) : ℝ)) ≤ gamma ^ (a : ℕ) := by
  have hbase := rpow_three_neg_recurrenceGap_div_four_le_rpow a (t := (a : ℝ) / 4)
    hgamma0 hgamma1 le_rfl
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((recurrenceGap a gamma : ℕ) : ℝ) / 4)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hL : ((3 : ℝ) ^ (-(((recurrenceGap a gamma : ℕ) : ℝ) / 4))) ^ (4 : ℕ)
      = (3 : ℝ) ^ (-((recurrenceGap a gamma : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(((recurrenceGap a gamma : ℕ) : ℝ) / 4))) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hR : (gamma ^ ((a : ℝ) / 4)) ^ (4 : ℕ) = gamma ^ (a : ℕ) := by
    rw [← Real.rpow_natCast (gamma ^ ((a : ℝ) / 4)) 4, ← Real.rpow_mul hgamma0.le,
      show (a : ℝ) / 4 * ((4 : ℕ) : ℝ) = (a : ℝ) by push_cast; ring]
    exact Real.rpow_natCast gamma a
  have hpow := pow_le_pow_left₀ hnn hbase 4
  rwa [hL, hR] at hpow

/-! ## The log-loss bound -/

/-- **The corrected gap loses only one power of `gamma`.** `a ceil|log_3 gamma| .
gamma <= 3a` on `0 < gamma <= 1`.  The route is the coverage estimate
`ceil|log_3 gamma| <= 2 sqrt(gamma^{-1}) + 1` of `LocalizationParams` together
with `gamma sqrt(gamma^{-1}) <= 1`.: on `hgamma0`, `hgamma1`. -/
theorem recurrenceGap_mul_gamma_le (a : ℕ) {gamma : ℝ}
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    ((recurrenceGap a gamma : ℕ) : ℝ) * gamma ≤ 3 * (a : ℝ) := by
  have hx0 : (0 : ℝ) < gamma⁻¹ := inv_pos.mpr hgamma0
  have hx : (1 : ℝ) ≤ gamma⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hgamma0]
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt gamma⁻¹ := by
    have h1 : Real.sqrt (1 : ℝ) ≤ Real.sqrt gamma⁻¹ := Real.sqrt_le_sqrt hx
    simpa using h1
  have hssq : Real.sqrt gamma⁻¹ ^ 2 = gamma⁻¹ := Real.sq_sqrt hx0.le
  have hsle : Real.sqrt gamma⁻¹ ≤ gamma⁻¹ := by nlinarith [hssq, hs1]
  have hcancel : gamma⁻¹ * gamma = 1 := inv_mul_cancel₀ (ne_of_gt hgamma0)
  have hsg : Real.sqrt gamma⁻¹ * gamma ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hsle hgamma0.le
    linarith [hcancel, this]
  have hceil := logThreeCeil_le_two_mul_sqrt_add_one hgamma0 hgamma1
  have hcast : ((recurrenceGap a gamma : ℕ) : ℝ) = (a : ℝ) * (logThreeCeil gamma : ℝ) := by
    simp [recurrenceGap]
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hstep : (logThreeCeil gamma : ℝ) * gamma ≤ 3 := by
    have h1 : (logThreeCeil gamma : ℝ) * gamma ≤ (2 * Real.sqrt gamma⁻¹ + 1) * gamma :=
      mul_le_mul_of_nonneg_right hceil hgamma0.le
    nlinarith [h1, hsg, hgamma1, hgamma0]
  calc ((recurrenceGap a gamma : ℕ) : ℝ) * gamma
      = (a : ℝ) * ((logThreeCeil gamma : ℝ) * gamma) := by rw [hcast]; ring
    _ ≤ (a : ℝ) * 3 := mul_le_mul_of_nonneg_left hstep ha0
    _ = 3 * (a : ℝ) := by ring

/-! ## The shell normalization -/

/-- The absolute constant of the shell normalization: `sqrt(24 . 3^18)`. -/
def shellNormalizationConst : ℝ := Real.sqrt (24 * (3 : ℝ) ^ (18 : ℝ))

theorem shellNormalizationConst_nonneg : 0 ≤ shellNormalizationConst :=
  Real.sqrt_nonneg _

/-- **`shom_{m-h}^{-1} 3^{cgamma (m-h)} <= sqrt(24 . 3^18)`.**

This is the deterministic head `Corrector.inv_sigmaBarSq_mul_shellWidth_le`
(which reads `shom_{m-h}^{-2} h 3^{2 cgamma m} <= 24 . 3^18`) used at `h >= 1`
and at `m - h <= m`.  It is the normalization the second and third terms of
`e.lower.bound.oscillations` consume.

: on the induction state `hS` and the three source gates `hhpos : 0 < h`, `hm :
m - h <= m0`, `hh : h <= 6 cstar cgamma^{-1}`. -/
theorem sigmaBarInv_mul_rpow_gamma_shell_le {d : ℕ} (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {m : ℤ} {h : ℕ} (hhpos : 0 < h) (hm : m - (h : ℤ) ≤ m0)
    (hh : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹) :
    ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
        (3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ))) ≤ shellNormalizationConst := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsigma : 0 < (Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) :=
    (Annealed.sigmaBar_characterization M (m - (h : ℤ))).1
  have hhead := Corrector.inv_sigmaBarSq_mul_shellWidth_le M hS hm hh
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhpos
  have hrppos : (0 : ℝ) < (3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hA0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
      (3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ))) :=
    mul_nonneg (inv_pos.2 hsigma).le hrppos.le
  have hrp : ((3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ)))) ^ (2 : ℕ)
      = (3 : ℝ) ^ (2 * M.gamma * (((m - (h : ℤ) : ℤ) : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ)))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hsq : (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
        (3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ)))) ^ (2 : ℕ) =
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (((m - (h : ℤ) : ℤ) : ℝ))) := by
    rw [mul_pow, hrp, inv_pow]
  have hexp : (3 : ℝ) ^ (2 * M.gamma * (((m - (h : ℤ) : ℤ) : ℝ))) ≤
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcast : ((m - (h : ℤ) : ℤ) : ℝ) = (m : ℝ) - (h : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [hgamma, hh1]
  have hinvpos : (0 : ℝ) < ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ := by positivity
  have hrp2pos : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hchain : (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
        (3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ)))) ^ (2 : ℕ) ≤
      24 * (3 : ℝ) ^ (18 : ℝ) := by
    have h1 : (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
        (3 : ℝ) ^ (M.gamma * (((m - (h : ℤ) : ℤ) : ℝ)))) ^ (2 : ℕ) ≤
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      rw [hsq]
      exact mul_le_mul_of_nonneg_left hexp hinvpos.le
    have h2 : ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) ≤
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) ^ 2)⁻¹ * (h : ℝ) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
      nlinarith [hinvpos, hh1, hrp2pos]
    linarith [h1, h2, hhead]
  have hsqrt := Real.sqrt_le_sqrt hchain
  rwa [Real.sqrt_sq hA0] at hsqrt

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
