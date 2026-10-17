/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SiteTailCalibration

/-!
# SiteTailCalibrationV2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Site-tail calibration at the successor logarithmic exponents

The successor error-moment estimate leads to the Markov exponent

```
p = c ε² γ⁻¹ |log γ|⁻⁶
```

and to the accuracy floor `K √γ |log γ|^(7/2)`.  Besides the shell and path
gates already present in the earlier calibration, the constant `K` includes
`2 e C`, which absorbs the additive square-root logarithm in the error-moment
amplitude.

This module records the successor constants and the five numerical gates used
by the percolation path estimate.  It also records the three elementary upper
bounds needed when the successor exponent is inserted into the error,
regularity, and shell tails.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## Successor constants -/

/-- The Markov exponent at the successor logarithmic scale. -/
def siteMarkovExponentV2 (M : ABKModel d) (c ep : ℝ) : ℝ :=
  c * ep ^ 2 * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)

/-- The squared bad-site rate before the separation shift. -/
def siteBadRateSqV2 (M : ABKModel d) (c ep : ℝ) : ℝ :=
  siteMarkovExponentV2 M c ep / 2

/-- The squared bad-site rate after the separation shift. -/
def siteTailRateSqV2 (d : ℕ) (M : ABKModel d) (c ep : ℝ) : ℝ :=
  siteBadRateSqV2 M c ep *
    (3 : ℝ) ^ (-(sitePathExponent * (Provider.Percolation.sepShift d : ℝ)))

/-- The bad-site rate after the separation shift. -/
def siteTailRateV2 (d : ℕ) (M : ABKModel d) (c ep : ℝ) : ℝ :=
  Real.sqrt (siteTailRateSqV2 d M c ep)

/-- The constant in the successor lower bound for the accuracy parameter.
The last summand is the contribution of the additive square-root logarithm in
the error-moment amplitude. -/
def siteEpsLowerConstV2 (d : ℕ) (c Cinj Cpath C : ℝ) : ℝ :=
  (siteThresholdConst Cinj)⁻¹ +
    Real.sqrt (2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
      (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) * c⁻¹) +
    2 * Real.exp 1 * C

theorem siteEpsLowerConstV2_pos (d : ℕ) {c Cinj Cpath C : ℝ}
    (hCinj : 0 < Cinj) (hC : 0 ≤ C) :
    0 < siteEpsLowerConstV2 d c Cinj Cpath C := by
  have hthreshold : (0 : ℝ) < (siteThresholdConst Cinj)⁻¹ :=
    inv_pos.2 (siteThresholdConst_pos hCinj)
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
      (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) * c⁻¹) :=
    Real.sqrt_nonneg _
  have hamp : (0 : ℝ) ≤ 2 * Real.exp 1 * C := by positivity
  rw [siteEpsLowerConstV2]
  linarith only [hthreshold, hsqrt, hamp]

theorem inv_siteThresholdConst_le_siteEpsLowerConstV2
    (d : ℕ) {c Cinj Cpath C : ℝ} (hC : 0 ≤ C) :
    (siteThresholdConst Cinj)⁻¹ ≤ siteEpsLowerConstV2 d c Cinj Cpath C := by
  rw [siteEpsLowerConstV2]
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
      (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) * c⁻¹) :=
    Real.sqrt_nonneg _
  have hamp : (0 : ℝ) ≤ 2 * Real.exp 1 * C := by positivity
  linarith only [hsqrt, hamp]

theorem two_exp_mul_le_siteEpsLowerConstV2
    (d : ℕ) {c Cinj Cpath C : ℝ} (hCinj : 0 < Cinj) :
    2 * Real.exp 1 * C ≤ siteEpsLowerConstV2 d c Cinj Cpath C := by
  rw [siteEpsLowerConstV2]
  have hthreshold : (0 : ℝ) ≤ (siteThresholdConst Cinj)⁻¹ :=
    (inv_pos.2 (siteThresholdConst_pos hCinj)).le
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
      (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) * c⁻¹) :=
    Real.sqrt_nonneg _
  linarith only [hthreshold, hsqrt]

/-- The third summand of the floor absorbs the additive term in the
error-moment amplitude. -/
theorem two_exp_mul_sqrt_mul_rpow_le_of_epsLowerV2
    (M : ABKModel d) {c Cinj Cpath C ep : ℝ} (hCinj : 0 < Cinj)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    2 * Real.exp 1 * C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep := by
  have hs : (0 : ℝ) ≤ Real.sqrt M.gamma := Real.sqrt_nonneg _
  have hl : (0 : ℝ) ≤ Real.rpow |Real.log M.gamma| (7 / 2) :=
    (Real.rpow_pos_of_pos (abs_log_gamma_pos M) _).le
  refine (mul_le_mul_of_nonneg_right ?_ hl).trans hlow
  exact mul_le_mul_of_nonneg_right (two_exp_mul_le_siteEpsLowerConstV2 d hCinj) hs

/-! ## Positivity and logarithmic powers -/

theorem siteMarkovExponentV2_pos (M : ABKModel d) {c ep : ℝ}
    (hc : 0 < c) (hep : 0 < ep) : 0 < siteMarkovExponentV2 M c ep := by
  have hg : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 M.shellPrefix.gamma_pos
  have hl : (0 : ℝ) < |Real.log M.gamma| ^ (-6 : ℤ) :=
    zpow_pos (abs_log_gamma_pos M) _
  rw [siteMarkovExponentV2]
  positivity

theorem abs_log_gamma_zpow_neg_six_le_one (M : ABKModel d) :
    |Real.log M.gamma| ^ (-6 : ℤ) ≤ 1 := by
  have h6 : (1 : ℝ) ≤ |Real.log M.gamma| ^ (6 : ℕ) :=
    one_le_pow₀ (one_le_abs_log_gamma M)
  rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ h6

theorem abs_log_gamma_zpow_neg_six_le_inv (M : ABKModel d) :
    |Real.log M.gamma| ^ (-6 : ℤ) ≤ |Real.log M.gamma|⁻¹ := by
  have hl := one_le_abs_log_gamma M
  have hlpos := abs_log_gamma_pos M
  rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  have hmono : |Real.log M.gamma| ≤ |Real.log M.gamma| ^ (6 : ℕ) := by
    calc |Real.log M.gamma| = |Real.log M.gamma| ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ |Real.log M.gamma| ^ (6 : ℕ) := pow_le_pow_right₀ hl (by norm_num)
  exact inv_anti₀ hlpos hmono

theorem pos_of_epsLowerV2 (M : ABKModel d) {c Cinj Cpath C ep : ℝ}
    (hCinj : 0 < Cinj) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) : 0 < ep := by
  have hK : (0 : ℝ) < siteEpsLowerConstV2 d c Cinj Cpath C :=
    siteEpsLowerConstV2_pos d hCinj hC
  have hs : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 M.shellPrefix.gamma_pos
  have hl : (0 : ℝ) < Real.rpow |Real.log M.gamma| (7 / 2) :=
    Real.rpow_pos_of_pos (abs_log_gamma_pos M) _
  have hfloor : (0 : ℝ) < siteEpsLowerConstV2 d c Cinj Cpath C *
      Real.sqrt M.gamma * Real.rpow |Real.log M.gamma| (7 / 2) := by positivity
  exact lt_of_lt_of_le hfloor hlow

/-! ## The core lower bound -/

/-- The successor accuracy floor forces the Markov exponent above the common
path-bound gate. -/
theorem le_siteMarkovExponentV2_of_epsLower (M : ABKModel d)
    {c Cinj Cpath C ep : ℝ} (hc : 0 < c) (hCinj : 0 < Cinj) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
        (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) ≤
      siteMarkovExponentV2 M c ep := by
  let K := siteEpsLowerConstV2 d c Cinj Cpath C
  let l := |Real.log M.gamma|
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hl : (0 : ℝ) < l := abs_log_gamma_pos M
  have hl1 : (1 : ℝ) ≤ l := one_le_abs_log_gamma M
  have hK : (0 : ℝ) < K := siteEpsLowerConstV2_pos d hCinj hC
  have hs : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 hg
  have hlpow : l ^ (3 : ℕ) ≤ Real.rpow l (7 / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
  have hweak : K * Real.sqrt M.gamma * l ^ (3 : ℕ) ≤ ep := by
    exact (mul_le_mul_of_nonneg_left hlpow (mul_nonneg hK.le hs.le)).trans hlow
  have hfloorpos : (0 : ℝ) < K * Real.sqrt M.gamma * l ^ (3 : ℕ) := by positivity
  have hsq : (K * Real.sqrt M.gamma * l ^ (3 : ℕ)) ^ 2 =
      K ^ 2 * M.gamma * l ^ (6 : ℕ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hg.le, ← pow_mul]
  have hep2 : K ^ 2 * M.gamma * l ^ (6 : ℕ) ≤ ep ^ 2 := by
    rw [← hsq]
    exact pow_le_pow_left₀ hfloorpos.le hweak 2
  have hident : K ^ 2 * M.gamma * l ^ (6 : ℕ) * M.gamma⁻¹ * l ^ (-6 : ℤ) =
      K ^ 2 := by
    field_simp
  have hKle : K ^ 2 ≤ ep ^ 2 * M.gamma⁻¹ * l ^ (-6 : ℤ) := by
    rw [← hident]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hep2 (inv_nonneg.2 hg.le)) (zpow_pos hl _).le
  have hstep : c * K ^ 2 ≤ siteMarkovExponentV2 M c ep := by
    rw [siteMarkovExponentV2]
    simpa only [l, mul_assoc] using mul_le_mul_of_nonneg_left hKle hc.le
  let X := 2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
    (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ))
  have hX : (0 : ℝ) ≤ X := by
    have hB := one_le_gateBracket Cpath
    have hS := one_le_shiftFactor d
    dsimp only [X]
    positivity
  have hsqrt_le : Real.sqrt (X * c⁻¹) ≤ K := by
    dsimp only [K, X]
    rw [siteEpsLowerConstV2]
    have hthreshold : (0 : ℝ) ≤ (siteThresholdConst Cinj)⁻¹ :=
      (inv_pos.2 (siteThresholdConst_pos hCinj)).le
    have hamp : (0 : ℝ) ≤ 2 * Real.exp 1 * C := by positivity
    linarith only [hthreshold, hamp]
  have hXc : (0 : ℝ) ≤ X * c⁻¹ := mul_nonneg hX (inv_nonneg.2 hc.le)
  have hXle : X * c⁻¹ ≤ K ^ 2 := by
    calc X * c⁻¹ = Real.sqrt (X * c⁻¹) ^ 2 := (Real.sq_sqrt hXc).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
  have hcancel : X = c * (X * c⁻¹) := by
    dsimp only [X]
    field_simp
  calc X = c * (X * c⁻¹) := hcancel
    _ ≤ c * K ^ 2 := mul_le_mul_of_nonneg_left hXle hc.le
    _ ≤ siteMarkovExponentV2 M c ep := hstep

/-! ## The five path-bound gates -/

theorem one_le_siteMarkovExponentV2_of_epsLower (M : ABKModel d)
    {c Cinj Cpath C ep : ℝ} (hc : 0 < c) (hCinj : 0 < Cinj) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    1 ≤ siteMarkovExponentV2 M c ep := by
  have hcore := le_siteMarkovExponentV2_of_epsLower M hc hCinj hC hlow
  have h2 : (2 : ℝ) ≤ 2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
      (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) := by
    calc (2 : ℝ) = 2 * 1 * 1 := by ring
      _ ≤ 2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
          (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) := by
        have hB := one_le_gateBracket Cpath
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num))
          (one_le_shiftFactor d) zero_le_one (by linarith only [hB])
  linarith only [hcore, h2]

theorem log_three_le_siteBadRateSqV2_of_epsLower (M : ABKModel d)
    {c Cinj Cpath C ep : ℝ} (hc : 0 < c) (hCinj : 0 < Cinj) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    Real.log 3 ≤ siteBadRateSqV2 M c ep := by
  have hcore := le_siteMarkovExponentV2_of_epsLower M hc hCinj hC hlow
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hprod : 2 * Real.log 3 ≤
      2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
        (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) := by
    have hsq : (0 : ℝ) ≤ (16 * Cpath) ^ 2 := sq_nonneg _
    calc 2 * Real.log 3 = 2 * Real.log 3 * 1 := by ring
      _ ≤ 2 * (1 + Real.log 3 + (16 * Cpath) ^ 2) *
          (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) := by
        have hB : Real.log 3 ≤ 1 + Real.log 3 + (16 * Cpath) ^ 2 := by
          linarith only [hsq]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num))
          (one_le_shiftFactor d) zero_le_one (by linarith only [hlog, hsq])
  rw [siteBadRateSqV2]
  linarith only [hcore, hprod]

theorem one_le_siteThresholdConst_mul_of_epsLowerV2 (M : ABKModel d)
    {c Cinj Cpath C ep : ℝ} (hCinj : 0 < Cinj) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    1 ≤ siteThresholdConst Cinj * ep * (Real.sqrt M.gamma)⁻¹ := by
  have hs : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 M.shellPrefix.gamma_pos
  have hkappa : 0 < siteThresholdConst Cinj := siteThresholdConst_pos hCinj
  have hlpow : (1 : ℝ) ≤ Real.rpow |Real.log M.gamma| (7 / 2) :=
    Real.one_le_rpow (one_le_abs_log_gamma M) (by norm_num)
  have hK := inv_siteThresholdConst_le_siteEpsLowerConstV2 d
    (c := c) (Cinj := Cinj) (Cpath := Cpath) hC
  have hKpos : (0 : ℝ) < siteEpsLowerConstV2 d c Cinj Cpath C :=
    siteEpsLowerConstV2_pos d hCinj hC
  have hchain : (siteThresholdConst Cinj)⁻¹ * Real.sqrt M.gamma ≤ ep := by
    refine le_trans ?_ hlow
    calc (siteThresholdConst Cinj)⁻¹ * Real.sqrt M.gamma
        = (siteThresholdConst Cinj)⁻¹ * Real.sqrt M.gamma * 1 := by ring
      _ ≤ siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
          Real.rpow |Real.log M.gamma| (7 / 2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hK hs.le) hlpow zero_le_one
          (mul_nonneg hKpos.le hs.le)
  have hdiv : (siteThresholdConst Cinj)⁻¹ ≤ ep * (Real.sqrt M.gamma)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hchain (inv_nonneg.2 hs.le)
    rwa [mul_assoc, mul_inv_cancel₀ hs.ne', mul_one] at h
  have hmul := mul_le_mul_of_nonneg_left hdiv hkappa.le
  rwa [mul_inv_cancel₀ hkappa.ne', ← mul_assoc] at hmul

theorem gateBracket_le_siteTailRateSqV2_of_epsLower (M : ABKModel d)
    {c Cinj Cpath C ep : ℝ} (hc : 0 < c) (hCinj : 0 < Cinj) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    1 + Real.log 3 + (16 * Cpath) ^ 2 ≤ siteTailRateSqV2 d M c ep := by
  have hcore := le_siteMarkovExponentV2_of_epsLower M hc hCinj hC hlow
  have hinvpos : (0 : ℝ) <
      (3 : ℝ) ^ (-(sitePathExponent * (Provider.Percolation.sepShift d : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcancel :
      (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) *
        (3 : ℝ) ^ (-(sitePathExponent * (Provider.Percolation.sepShift d : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  rw [siteTailRateSqV2, siteBadRateSqV2]
  calc 1 + Real.log 3 + (16 * Cpath) ^ 2
      = (1 + Real.log 3 + (16 * Cpath) ^ 2) *
          (3 : ℝ) ^ (sitePathExponent * (Provider.Percolation.sepShift d : ℝ)) *
          (3 : ℝ) ^ (-(sitePathExponent * (Provider.Percolation.sepShift d : ℝ))) := by
        rw [mul_assoc, hcancel, mul_one]
    _ ≤ siteMarkovExponentV2 M c ep / 2 *
          (3 : ℝ) ^ (-(sitePathExponent * (Provider.Percolation.sepShift d : ℝ))) := by
      refine mul_le_mul_of_nonneg_right ?_ hinvpos.le
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith only [hcore]

theorem one_le_siteTailRateV2_of_epsLower (M : ABKModel d)
    {c Cinj Cpath C ep : ℝ} (hc : 0 < c) (hCinj : 0 < Cinj) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    1 ≤ siteTailRateV2 d M c ep := by
  have h1 : (1 : ℝ) ≤ siteTailRateSqV2 d M c ep :=
    (one_le_gateBracket Cpath).trans
      (gateBracket_le_siteTailRateSqV2_of_epsLower M hc hCinj hC hlow)
  rw [siteTailRateV2]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (siteTailRateSqV2 d M c ep) := Real.sqrt_le_sqrt h1

theorem pathBoundGate_le_siteTailRateV2_of_epsLower (M : ABKModel d)
    {c Cinj Cpath C ep : ℝ} (hc : 0 < c) (hCinj : 0 < Cinj)
    (hCpath : 0 ≤ Cpath) (hC : 0 ≤ C)
    (hlow : siteEpsLowerConstV2 d c Cinj Cpath C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep) :
    Cpath * (1 / 4 : ℝ)⁻¹ * (sitePathExponent - 1)⁻¹ ≤ siteTailRateV2 d M c ep := by
  have hbase := gateBracket_le_siteTailRateSqV2_of_epsLower M hc hCinj hC hlow
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsq : (16 * Cpath) ^ 2 ≤ siteTailRateSqV2 d M c ep := by
    linarith only [hbase, hlog]
  have hgate : Cpath * (1 / 4 : ℝ)⁻¹ * (sitePathExponent - 1)⁻¹ = 16 * Cpath := by
    rw [sitePathExponent]
    ring_nf
  have h16 : (0 : ℝ) ≤ 16 * Cpath := by positivity
  rw [hgate, siteTailRateV2]
  calc 16 * Cpath = Real.sqrt ((16 * Cpath) ^ 2) := (Real.sqrt_sq h16).symm
    _ ≤ Real.sqrt (siteTailRateSqV2 d M c ep) := Real.sqrt_le_sqrt hsq

/-! ## Upper gates for the three tail estimates -/

theorem siteMarkovExponentV2_le_range (M : ABKModel d) {c Crange ep : ℝ}
    (hCrange : 0 < Crange) (hc : c ≤ Crange⁻¹) (hep : 0 < ep) (hep4 : ep ≤ 1 / 4) :
    siteMarkovExponentV2 M c ep ≤
      Crange⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
  have hginv : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 M.shellPrefix.gamma_pos
  have hsq : ep ^ 2 ≤ 1 := by nlinarith only [hep, hep4]
  calc siteMarkovExponentV2 M c ep
      ≤ Crange⁻¹ * 1 * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
        rw [siteMarkovExponentV2]
        have hpow : (0 : ℝ) ≤ |Real.log M.gamma| ^ (-6 : ℤ) :=
          (zpow_pos (abs_log_gamma_pos M) _).le
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right
            (mul_le_mul hc hsq (sq_nonneg ep) (inv_nonneg.2 hCrange.le)) hginv.le)
          (abs_log_gamma_zpow_neg_six_le_inv M) hpow
          (mul_nonneg (mul_nonneg (inv_nonneg.2 hCrange.le) zero_le_one) hginv.le)
    _ = Crange⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by ring

theorem siteMarkovExponentV2_le_regularity (M : ABKModel d) {c creg ep : ℝ}
    (hc : c ≤ creg) (hcreg : 0 ≤ creg) (hep : 0 < ep) (hep4 : ep ≤ 1 / 4) :
    siteMarkovExponentV2 M c ep ≤
      creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) * Real.log 2 := by
  have hginv : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 M.shellPrefix.gamma_pos
  have hlogpow : (0 : ℝ) < |Real.log M.gamma| ^ (-6 : ℤ) :=
    zpow_pos (abs_log_gamma_pos M) _
  have hsq : ep ^ 2 ≤ 1 / 16 := by nlinarith only [hep, hep4]
  have h16 : (1 : ℝ) / 16 ≤ Real.log 2 := by
    linarith only [Real.log_two_gt_d9]
  rw [siteMarkovExponentV2]
  calc c * ep ^ 2 * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)
      ≤ creg * (1 / 16) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul hc hsq (sq_nonneg ep) hcreg) hginv.le)
          hlogpow.le
    _ ≤ creg * Real.log 2 * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h16 hcreg) hginv.le)
          hlogpow.le
    _ = creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) * Real.log 2 := by ring

theorem siteMarkovExponentV2_le_shell (M : ABKModel d) {c Cinj ep : ℝ}
    (hc : c ≤ siteThresholdConst Cinj ^ 2) :
    siteMarkovExponentV2 M c ep ≤
      siteThresholdConst Cinj ^ 2 * ep ^ 2 * M.gamma⁻¹ := by
  have hginv : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 M.shellPrefix.gamma_pos
  have hep2 : (0 : ℝ) ≤ ep ^ 2 := sq_nonneg _
  rw [siteMarkovExponentV2]
  calc c * ep ^ 2 * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)
      ≤ siteThresholdConst Cinj ^ 2 * ep ^ 2 * M.gamma⁻¹ * 1 := by
        have hpow : (0 : ℝ) ≤ |Real.log M.gamma| ^ (-6 : ℤ) :=
          (zpow_pos (abs_log_gamma_pos M) _).le
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hep2) hginv.le)
          (abs_log_gamma_zpow_neg_six_le_one M) hpow
          (mul_nonneg (mul_nonneg (sq_nonneg _) hep2) hginv.le)
    _ = siteThresholdConst Cinj ^ 2 * ep ^ 2 * M.gamma⁻¹ := by ring

end

end Algsuperdiff.Section5.Support
