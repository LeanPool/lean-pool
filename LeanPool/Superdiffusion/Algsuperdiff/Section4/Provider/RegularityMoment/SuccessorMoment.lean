/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.RegularityMoment.PointwiseBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.RegularityMoment.ScaleMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MomentHolder
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalArith
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.S5ErrorMomentBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SiteTailCalibrationV2

/-!
# SuccessorMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Successor moment bound for the localized regularity

The pointwise regularity estimate is combined with moments of its minimal-scale
factor and of the localized error.  The logarithmic loss in the exponent keeps
the doubled exponent inside both available moment ranges.
-/

namespace Algsuperdiff.Section4.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.RegularityMoment
open Algsuperdiff.Section4.Provider.BoundsEaL
open Algsuperdiff.Section4.Provider.Regularity
open Algsuperdiff.Section5.Support
open _root_.HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

private theorem lintegral_rpow_le_of_lintegral_rpow_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {F : Omega → ℝ≥0∞} {p q R : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (hF : AEMeasurable F mu)
    (hq : (∫⁻ omega, F omega ^ q ∂mu) ≤ ENNReal.ofReal R ^ q) :
    (∫⁻ omega, F omega ^ p ∂mu) ≤ ENNReal.ofReal R ^ p := by
  have hq0 : 0 < q := hp.trans_le hpq
  have hnorm := eLpNorm'_le_eLpNorm'_of_exponent_le hp hpq mu hF.aestronglyMeasurable
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm] at hnorm
  simp only [enorm_eq_self] at hnorm
  have hqroot : (∫⁻ omega, F omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal R := by
    refine (ENNReal.rpow_le_rpow hq (by positivity)).trans_eq ?_
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  have hpRoot : (∫⁻ omega, F omega ^ p ∂mu) ^ (1 / p) ≤ ENNReal.ofReal R :=
    hnorm.trans hqroot
  have hraise := ENNReal.rpow_le_rpow hpRoot hp.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one] at hraise

private theorem lintegral_one_add_rpow_le {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {E : Omega → ℝ≥0∞} {q A : ℝ}
    (hq : 1 ≤ q) (hE : AEMeasurable E mu) (hA : 0 ≤ A)
    (hmom : (∫⁻ omega, E omega ^ q ∂mu) ≤ ENNReal.ofReal A ^ q) :
    (∫⁻ omega, (1 + E omega) ^ q ∂mu) ≤ ENNReal.ofReal (1 + A) ^ q := by
  let f : Omega → ℝ≥0∞ := fun _ => 1
  have hmink := ENNReal.lintegral_Lp_add_le (μ := mu) (f := f) (g := E)
    measurable_const.aemeasurable hE hq
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hconst : (∫⁻ omega, f omega ^ q ∂mu) ^ (1 / q) = 1 := by
    simp only [f, ENNReal.one_rpow, lintegral_const, measure_univ, mul_one]
  have hEroot : (∫⁻ omega, E omega ^ q ∂mu) ^ (1 / q) ≤ ENNReal.ofReal A := by
    refine (ENNReal.rpow_le_rpow hmom (by positivity)).trans_eq ?_
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  have hroot : (∫⁻ omega, (1 + E omega) ^ q ∂mu) ^ (1 / q) ≤
      ENNReal.ofReal (1 + A) := by
    refine hmink.trans ?_
    rw [hconst, ENNReal.ofReal_add zero_le_one hA, ENNReal.ofReal_one]
    exact add_le_add (le_refl 1) hEroot
  have hraise := ENNReal.rpow_le_rpow hroot hq0.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one] at hraise

private theorem abs_log_le_rpow_neg_sixteenth {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    |Real.log g| ≤ 16 * g ^ (-(1 / 16) : ℝ) := by
  have hpow : (0 : ℝ) < g ^ (-(1 / 16) : ℝ) := Real.rpow_pos_of_pos hg0 _
  have hlog : Real.log (g ^ (-(1 / 16) : ℝ)) ≤ g ^ (-(1 / 16) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpow
  have hrw : Real.log (g ^ (-(1 / 16) : ℝ)) = -(1 / 16 : ℝ) * Real.log g :=
    Real.log_rpow hg0 _
  have hlog0 : Real.log g ≤ 0 := Real.log_nonpos hg0.le hg1
  rw [abs_of_nonpos hlog0]
  rw [hrw] at hlog
  linarith only [hlog, hpow]

private theorem gamma_log_six_le {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    g * |Real.log g| ^ (6 : ℕ) ≤ 262144 * g ^ (1 / 4 : ℝ) := by
  have hlog := abs_log_le_rpow_neg_eighth hg0 hg1
  have hp := pow_le_pow_left₀ (abs_nonneg _) hlog 6
  have hgid : g * g ^ (-(1 / 8) * (6 : ℝ)) = g ^ (1 / 4 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one g]
    rw [← Real.rpow_add hg0]
    norm_num
  have hid : g * (8 * g ^ (-(1 / 8) : ℝ)) ^ (6 : ℕ) =
      262144 * g ^ (1 / 4 : ℝ) := by
    rw [mul_pow]
    norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg0.le]
    calc g * (262144 * g ^ (-(1 / 8) * (6 : ℝ))) =
          262144 * (g * g ^ (-(1 / 8) * (6 : ℝ))) := by ring
      _ = 262144 * g ^ (1 / 4 : ℝ) := by rw [hgid]
  calc g * |Real.log g| ^ (6 : ℕ) ≤ g * (8 * g ^ (-(1 / 8) : ℝ)) ^ (6 : ℕ) :=
      mul_le_mul_of_nonneg_left hp hg0.le
    _ = 262144 * g ^ (1 / 4 : ℝ) := hid

private theorem sqrt_gamma_log_seven_half_le {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hlog1 : 1 ≤ |Real.log g|) :
    Real.sqrt g * |Real.log g| ^ (3 : ℕ) * Real.sqrt |Real.log g| ≤
      65536 * g ^ (1 / 4 : ℝ) := by
  have hlog := abs_log_le_rpow_neg_sixteenth hg0 hg1
  have hp := pow_le_pow_left₀ (abs_nonneg _) hlog 4
  have hsqrtlog : Real.sqrt |Real.log g| ≤ |Real.log g| := by
    rw [Real.sqrt_le_iff]
    exact ⟨abs_nonneg _, by nlinarith only [hlog1]⟩
  have hprod : |Real.log g| ^ (3 : ℕ) * Real.sqrt |Real.log g| ≤
      |Real.log g| ^ (4 : ℕ) := by
    calc |Real.log g| ^ (3 : ℕ) * Real.sqrt |Real.log g| ≤
          |Real.log g| ^ (3 : ℕ) * |Real.log g| :=
        mul_le_mul_of_nonneg_left hsqrtlog (pow_nonneg (abs_nonneg _) _)
      _ = |Real.log g| ^ (4 : ℕ) := by ring
  have hpow : |Real.log g| ^ (4 : ℕ) ≤
      (16 * g ^ (-(1 / 16) : ℝ)) ^ (4 : ℕ) := hp
  have hgid : g ^ (1 / 2 : ℝ) * g ^ (-(1 / 16) * (4 : ℝ)) =
      g ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hg0]
    norm_num
  have hid : Real.sqrt g * (16 * g ^ (-(1 / 16) : ℝ)) ^ (4 : ℕ) =
      65536 * g ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, mul_pow]
    norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg0.le]
    calc g ^ (1 / 2 : ℝ) * (65536 * g ^ (-(1 / 16) * (4 : ℝ))) =
          65536 * (g ^ (1 / 2 : ℝ) * g ^ (-(1 / 16) * (4 : ℝ))) := by ring
      _ = 65536 * g ^ (1 / 4 : ℝ) := by rw [hgid]
  calc Real.sqrt g * |Real.log g| ^ (3 : ℕ) * Real.sqrt |Real.log g|
      = Real.sqrt g * (|Real.log g| ^ (3 : ℕ) * Real.sqrt |Real.log g|) := by ring
    _ ≤ Real.sqrt g * |Real.log g| ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt g * (16 * g ^ (-(1 / 16) : ℝ)) ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
    _ = 65536 * g ^ (1 / 4 : ℝ) := hid

/-- The localized regularity moment bound at the successor logarithmic
exponent. -/
theorem s5_regularity_moment_bound_v2_provider
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 c C : ℝ, 0 < gamma0 ∧ 0 < c ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ (n : ℤ) (y : Vec d),
        (∫⁻ omega, localizedRegularity M n y omega ^
              (c * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal C ^ (c * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)) := by
  classical
  by_cases hmodel : Nonempty (ABKModel d)
  · let M0 := Classical.choice hmodel
    have hdim : 2 ≤ d := M0.shellPrefix.dimension
    obtain ⟨gammaP, Ctail, Camp, hgammaP, hCtail, hCamp, hpoint⟩ :=
      exists_localizedRegularity_pointwise_bound d cstar hdim hcstar
    obtain ⟨gammaS, c0, K, hgammaS, hc0, hK, hscale⟩ :=
      exists_minimalScaleFactor_moment_bound (d := d) Ctail hCtail
    obtain ⟨gammaE, CE, hgammaE, hCE, herror⟩ :=
      Algsuperdiff.Frozen.Section4.s5_error_moment_bound d cstar hcstar
    let c := min (c0 / 2) (2 * CE)⁻¹
    let gammaOne := min ((2 * c / 262144) ^ (4 : ℕ))
      ((1 / (CE * 65536)) ^ (4 : ℕ))
    let gamma0 := min gammaP (min gammaE (min gammaS (min (Real.exp (-7)) gammaOne)))
    let C := Camp * K * (2 + CE * Real.sqrt (2 * c))
    have hc : 0 < c := lt_min (div_pos hc0 (by norm_num)) (inv_pos.2 (by positivity))
    have hgammaOne : 0 < gammaOne := lt_min (by positivity) (by positivity)
    have hgamma0 : 0 < gamma0 :=
      lt_min hgammaP (lt_min hgammaE (lt_min hgammaS (lt_min (Real.exp_pos _) hgammaOne)))
    have hC : 0 < C := by dsimp only [C]; positivity
    refine ⟨gamma0, c, C, hgamma0, hc, hC, ?_⟩
    intro M hcstarM hgamma n y
    have hgam : 0 < M.gamma := M.shellPrefix.gamma_pos
    have hgam1 : M.gamma ≤ 1 := M.shellPrefix.gamma_le_quarter.trans (by norm_num)
    have hlog1 : 1 ≤ |Real.log M.gamma| := one_le_abs_log_gamma M
    have hgP : M.gamma ≤ gammaP := hgamma.trans (min_le_left _ _)
    have hgE : M.gamma ≤ gammaE :=
      hgamma.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hgS : M.gamma ≤ gammaS :=
      hgamma.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hgOne : M.gamma ≤ gammaOne := hgamma.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
    let p := c * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)
    have hp : 0 < p := by
      dsimp only [p]
      exact mul_pos (mul_pos hc (inv_pos.2 hgam)) (zpow_pos (abs_log_gamma_pos M) _)
    obtain ⟨X, hXmeas, hXtail, hpointwise⟩ := hpoint M hcstarM hgP n y
    have h2p_le_scale : 2 * p ≤ c0 * M.gamma⁻¹ := by
      have hc_le : c ≤ c0 / 2 := min_le_left _ _
      have hlogpow : |Real.log M.gamma| ^ (-6 : ℤ) ≤ 1 :=
        abs_log_gamma_zpow_neg_six_le_one M
      have hnonneg : 0 ≤ M.gamma⁻¹ := (inv_pos.2 hgam).le
      calc 2 * p = (2 * c) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
            dsimp only [p]; ring
        _ ≤ c0 * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
            gcongr
            linarith only [hc_le]
        _ ≤ c0 * M.gamma⁻¹ * 1 := by gcongr
        _ = c0 * M.gamma⁻¹ := by ring
    have hscaleTop := hscale M X hXmeas hgS hXtail
    have hscale2p :
        (∫⁻ omega, ENNReal.ofReal (Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) ^
            (2 * p) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal K ^ (2 * p) :=
      lintegral_rpow_le_of_lintegral_rpow_le (by positivity) h2p_le_scale
        ((Real.continuous_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).measurable.comp
          (measurable_const.mul
            ((measurable_of_countable (f := fun k : ℕ => (k : ℝ))).comp hXmeas))).ennreal_ofReal.aemeasurable
        hscaleTop
    have hgammaLog := gamma_log_six_le hgam hgam1
    have hgammaQuarter : M.gamma ^ (1 / 4 : ℝ) ≤ 2 * c / 262144 := by
      have hle : M.gamma ≤ (2 * c / 262144) ^ (4 : ℕ) := hgOne.trans (min_le_left _ _)
      have hbase : 0 ≤ 2 * c / 262144 := by positivity
      have := Real.rpow_le_rpow hgam.le hle (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase] at this
      norm_num at this
      exact this
    have hpOne : 1 ≤ 2 * p := by
      have hsmall : M.gamma * |Real.log M.gamma| ^ (6 : ℕ) ≤ 2 * c := by
        exact hgammaLog.trans (by
          have := mul_le_mul_of_nonneg_left hgammaQuarter (by norm_num : (0 : ℝ) ≤ 262144)
          linarith only [this])
      dsimp only [p]
      rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]
      rw [show 2 * (c * M.gamma⁻¹ * (|Real.log M.gamma| ^ (6 : ℕ))⁻¹) =
          (2 * c * M.gamma⁻¹) * (|Real.log M.gamma| ^ (6 : ℕ))⁻¹ by ring]
      rw [le_mul_inv_iff₀ (pow_pos (abs_log_gamma_pos M) 6),
        ← div_eq_mul_inv, le_div_iff₀ hgam]
      linarith only [hsmall]
    have h2pRange : 2 * p ≤ CE⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
      have hcCE : 2 * c ≤ CE⁻¹ := by
        have hmin : c ≤ (2 * CE)⁻¹ := min_le_right _ _
        calc 2 * c ≤ 2 * (2 * CE)⁻¹ := mul_le_mul_of_nonneg_left hmin (by norm_num)
          _ = CE⁻¹ := by field_simp
      have hlogpow := abs_log_gamma_zpow_neg_six_le_inv M
      have hginv0 : 0 ≤ M.gamma⁻¹ := (inv_pos.2 hgam).le
      have hz0 : 0 ≤ |Real.log M.gamma| ^ (-6 : ℤ) :=
        (zpow_pos (abs_log_gamma_pos M) _).le
      calc
        2 * p = (2 * c) * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
          dsimp only [p]
          ring
        _ ≤ CE⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcCE hginv0) hz0
        _ ≤ CE⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ :=
          mul_le_mul_of_nonneg_left hlogpow (mul_nonneg (inv_pos.2 hCE).le hginv0)
    have herror2p := herror M hcstarM hgE (2 * p) n y hpOne h2pRange
    have hampSmall : CE * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) *
        Real.sqrt |Real.log M.gamma| ≤ 1 := by
      have hbase := sqrt_gamma_log_seven_half_le hgam hgam1 hlog1
      have hquarter : M.gamma ^ (1 / 4 : ℝ) ≤ 1 / (CE * 65536) := by
        have hle : M.gamma ≤ (1 / (CE * 65536)) ^ (4 : ℕ) :=
          hgOne.trans (min_le_right _ _)
        have hbase0 : 0 ≤ 1 / (CE * 65536) := by positivity
        have := Real.rpow_le_rpow hgam.le hle (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0] at this
        norm_num at this
        rw [show 1 / (CE * 65536) = 1 / 65536 * CE⁻¹ by field_simp]
        exact this
      calc CE * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) *
            Real.sqrt |Real.log M.gamma|
          = CE * (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) *
              Real.sqrt |Real.log M.gamma|) := by ring
        _ ≤ CE * (65536 * M.gamma ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hbase hCE.le
        _ ≤ CE * (65536 * (1 / (CE * 65536))) := by gcongr
        _ = 1 := by field_simp
    have hsqrtTerm : CE * Real.sqrt (2 * p) * Real.sqrt M.gamma *
        |Real.log M.gamma| ^ (3 : ℕ) = CE * Real.sqrt (2 * c) := by
      have hlogpos := abs_log_gamma_pos M
      have hsqrtid : Real.sqrt (2 * p) * Real.sqrt M.gamma =
          Real.sqrt (2 * c) * |Real.log M.gamma|⁻¹ ^ (3 : ℕ) := by
        dsimp only [p]
        rw [show |Real.log M.gamma| ^ (-6 : ℤ) =
          (|Real.log M.gamma|⁻¹ ^ (3 : ℕ)) ^ (2 : ℕ) by
            rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast,
              ← inv_pow, ← pow_mul]]
        rw [show 2 * (c * M.gamma⁻¹ * (|Real.log M.gamma|⁻¹ ^ 3) ^ 2) =
          (2 * c) * (M.gamma⁻¹ * (|Real.log M.gamma|⁻¹ ^ 3) ^ 2) by ring,
          Real.sqrt_mul (by positivity : 0 ≤ 2 * c),
          Real.sqrt_mul (by positivity : 0 ≤ M.gamma⁻¹), Real.sqrt_inv M.gamma]
        rw [Real.sqrt_sq (by positivity : 0 ≤ |Real.log M.gamma|⁻¹ ^ (3 : ℕ))]
        have hsne : Real.sqrt M.gamma ≠ 0 := (Real.sqrt_pos.2 hgam).ne'
        rw [show Real.sqrt (2 * c) *
            ((Real.sqrt M.gamma)⁻¹ * |Real.log M.gamma|⁻¹ ^ 3) * Real.sqrt M.gamma =
            Real.sqrt (2 * c) * ((Real.sqrt M.gamma)⁻¹ * Real.sqrt M.gamma) *
              |Real.log M.gamma|⁻¹ ^ 3 by ring,
          inv_mul_cancel₀ hsne, mul_one]
      calc
        CE * Real.sqrt (2 * p) * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)
            = CE * (Real.sqrt (2 * p) * Real.sqrt M.gamma) *
                |Real.log M.gamma| ^ (3 : ℕ) := by ring
        _ = CE * (Real.sqrt (2 * c) * |Real.log M.gamma|⁻¹ ^ (3 : ℕ)) *
                |Real.log M.gamma| ^ (3 : ℕ) := by rw [hsqrtid]
        _ = CE * Real.sqrt (2 * c) := by field_simp
    have hAmp : CE * (Real.sqrt (2 * p) + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) ≤
        CE * Real.sqrt (2 * c) + 1 := by
      calc CE * (Real.sqrt (2 * p) + Real.sqrt |Real.log M.gamma|) *
            Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)
          = CE * Real.sqrt (2 * p) * Real.sqrt M.gamma * |Real.log M.gamma| ^ 3 +
              CE * Real.sqrt M.gamma * |Real.log M.gamma| ^ 3 *
                Real.sqrt |Real.log M.gamma| := by ring
        _ = CE * Real.sqrt (2 * c) +
              CE * Real.sqrt M.gamma * |Real.log M.gamma| ^ 3 *
                Real.sqrt |Real.log M.gamma| := by rw [hsqrtTerm]
        _ ≤ CE * Real.sqrt (2 * c) + 1 := add_le_add (le_refl _) hampSmall
    have herrorSimple :
        (∫⁻ omega, localizedError M n y omega ^ (2 * p)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (CE * Real.sqrt (2 * c) + 1) ^ (2 * p) :=
      herror2p.trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hAmp) (by positivity))
    have honeError :
        (∫⁻ omega, (1 + localizedError M n y omega) ^ (2 * p)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (2 + CE * Real.sqrt (2 * c)) ^ (2 * p) := by
      simpa only [show 1 + (CE * Real.sqrt (2 * c) + 1) =
          2 + CE * Real.sqrt (2 * c) by ring] using
        (lintegral_one_add_rpow_le hpOne (measurable_localizedError M n y).aemeasurable
          (by positivity) herrorSimple)
    have hscaled :
        (∫⁻ omega, ENNReal.ofReal
              (Camp * Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) ^ (2 * p)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (Camp * K) ^ (2 * p) := by
      have hCamp0 : 0 ≤ Camp := hCamp.le
      have hfactorMeas : Measurable (fun omega => ENNReal.ofReal
          (Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) ^ (2 * p)) :=
        ENNReal.continuous_rpow_const.measurable.comp
          (((Real.continuous_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).measurable.comp
            (measurable_const.mul
              ((measurable_of_countable (f := fun k : ℕ => (k : ℝ))).comp hXmeas))).ennreal_ofReal)
      calc
        (∫⁻ omega, ENNReal.ofReal
              (Camp * Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) ^ (2 * p)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure)
            = ENNReal.ofReal Camp ^ (2 * p) *
                ∫⁻ omega, ENNReal.ofReal
                  (Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) ^ (2 * p)
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
                rw [← lintegral_const_mul _ hfactorMeas]
                apply lintegral_congr
                intro omega
                rw [ENNReal.ofReal_mul hCamp0, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        _ ≤ ENNReal.ofReal Camp ^ (2 * p) * ENNReal.ofReal K ^ (2 * p) :=
              mul_le_mul_right hscale2p _
        _ = ENNReal.ofReal (Camp * K) ^ (2 * p) := by
              rw [ENNReal.ofReal_mul hCamp0, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    have hprod := lintegral_rpow_mul_le_of_moments (mu :=
        (Cutoff.cutoffSampleLaw M).toMeasure) hp
      ((measurable_const.mul
        ((Real.continuous_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).measurable.comp
          (measurable_const.mul
            ((measurable_of_countable (f := fun k : ℕ => (k : ℝ))).comp hXmeas)))).ennreal_ofReal).aemeasurable
      ((measurable_const.add (measurable_localizedError M n y)).aemeasurable)
      (mul_nonneg hCamp.le hK.le) hscaled honeError
    refine (lintegral_mono_ae (hpointwise.mono fun omega hw =>
      ENNReal.rpow_le_rpow hw hp.le)).trans ?_
    exact hprod.trans_eq (by dsimp only [C])
  · refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim

end

end Algsuperdiff.Section4.Provider
