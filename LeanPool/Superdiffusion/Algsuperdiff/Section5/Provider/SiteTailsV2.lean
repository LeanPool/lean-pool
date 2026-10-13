/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.S5ErrorMomentBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SiteTailCalibrationV2

/-!
# SiteTailsV2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Per-site tails at the successor logarithmic exponents

The localized-error leg is obtained from the Section 4 error-moment estimate.
The localized-regularity leg is kept as one hypothesis with the exact
existential shape of its successor moment estimate.  The two Markov bounds and
the shell estimate give the shifted per-site tail with logarithmic exponent
`-6` and accuracy floor `sqrt gamma * |log gamma|^(7/2)`.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem measure_gt_le_of_lintegral_rpow_le {Omega : Type*}
    [MeasurableSpace Omega] (P : Measure Omega) {F : Omega → ℝ≥0∞} (hF : Measurable F)
    {A t p : ℝ} (hA : 0 < A) (ht : 0 < t) (hp : 0 < p)
    (hmom : (∫⁻ omega, F omega ^ p ∂P) ≤ ENNReal.ofReal A ^ p) :
    P {omega | ENNReal.ofReal t < F omega} ≤ ENNReal.ofReal ((A / t) ^ p) := by
  have hEp : Measurable fun omega => F omega ^ p := hF.pow_const p
  have htpos : (0 : ℝ≥0∞) < ENNReal.ofReal t := ENNReal.ofReal_pos.2 ht
  have htne : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hposp : (0 : ℝ≥0∞) < ENNReal.ofReal t ^ p := ENNReal.rpow_pos htpos htne
  have htopp : ENNReal.ofReal t ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le htne
  have hsub : {omega | ENNReal.ofReal t < F omega} ⊆
      {omega | ENNReal.ofReal t ^ p ≤ F omega ^ p} := fun omega h =>
    ENNReal.rpow_le_rpow (le_of_lt h) hp.le
  have hmk := mul_meas_ge_le_lintegral₀ (hEp.aemeasurable (μ := P)) (ENNReal.ofReal t ^ p)
  have h1 : ENNReal.ofReal t ^ p * P {omega | ENNReal.ofReal t ^ p ≤ F omega ^ p} ≤
      ENNReal.ofReal A ^ p := le_trans hmk hmom
  have h2 : P {omega | ENNReal.ofReal t ^ p ≤ F omega ^ p} ≤
      ENNReal.ofReal A ^ p / ENNReal.ofReal t ^ p := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hposp.ne') (Or.inl htopp), mul_comm]
    exact h1
  calc P {omega | ENNReal.ofReal t < F omega}
      ≤ P {omega | ENNReal.ofReal t ^ p ≤ F omega ^ p} := measure_mono hsub
    _ ≤ ENNReal.ofReal A ^ p / ENNReal.ofReal t ^ p := h2
    _ = ENNReal.ofReal ((A / t) ^ p) := by
      rw [← ENNReal.div_rpow_of_nonneg _ _ hp.le, ← ENNReal.ofReal_div_of_pos ht,
        ENNReal.ofReal_rpow_of_pos (div_pos hA ht)]

private theorem measureReal_gt_le_exp_of_lintegral_rpow_le {Omega : Type*}
    [MeasurableSpace Omega] (P : Measure Omega) {F : Omega → ℝ≥0∞} (hF : Measurable F)
    {A t p : ℝ} (hA : 0 < A) (ht : 0 < t) (hp : 0 < p)
    (hmom : (∫⁻ omega, F omega ^ p ∂P) ≤ ENNReal.ofReal A ^ p)
    (hcal : A ≤ Real.exp (-1) * t) :
    P.real {omega | ENNReal.ofReal t < F omega} ≤ Real.exp (-p) := by
  have hstep := measure_gt_le_of_lintegral_rpow_le P hF hA ht hp hmom
  have hquot : A / t ≤ Real.exp (-1) := (div_le_iff₀ ht).2 hcal
  have hpow : (A / t) ^ p ≤ Real.exp (-p) := by
    calc (A / t) ^ p ≤ Real.exp (-1) ^ p :=
          Real.rpow_le_rpow (le_of_lt (div_pos hA ht)) hquot hp.le
      _ = Real.exp (-p) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos (-1)), Real.log_exp]
        congr 1
        ring
  refine le_trans (ENNReal.toReal_le_of_le_ofReal ?_ hstep) hpow
  exact Real.rpow_nonneg (div_pos hA ht).le p

private theorem sqrt_successor_rate {c t g l : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hg : 0 < g) (hl : 0 < l) :
    Real.sqrt (c * t ^ 2 * g⁻¹ * l ^ (-6 : ℤ)) =
      Real.sqrt c * t * (Real.sqrt g)⁻¹ * l ^ (-3 : ℤ) := by
  have hq0 : 0 ≤ Real.sqrt c * t * (Real.sqrt g)⁻¹ * l ^ (-3 : ℤ) := by positivity
  have hsq : (Real.sqrt c * t * (Real.sqrt g)⁻¹ * l ^ (-3 : ℤ)) ^ 2 =
      c * t ^ 2 * g⁻¹ * l ^ (-6 : ℤ) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hc, inv_pow, Real.sq_sqrt hg.le,
      ← zpow_natCast (l ^ (-3 : ℤ)) 2, ← zpow_mul]
    norm_num
  rw [← hsq, Real.sqrt_sq hq0]

private theorem first_amplitude_eq {C c t g l : ℝ} (hg : 0 < g) (hl : 0 < l) :
    C * (Real.sqrt c * t * (Real.sqrt g)⁻¹ * l ^ (-3 : ℤ)) *
        Real.sqrt g * l ^ (3 : ℕ) = C * Real.sqrt c * t := by
  have hsg : Real.sqrt g ≠ 0 := (Real.sqrt_pos.2 hg).ne'
  have hlne : l ≠ 0 := hl.ne'
  field_simp

private theorem second_amplitude_eq {C g l : ℝ} (hl : 0 < l) :
    C * Real.sqrt l * Real.sqrt g * l ^ (3 : ℕ) =
      C * Real.sqrt g * Real.rpow l (7 / 2) := by
  have hpow3 : l ^ (3 : ℕ) = Real.rpow l (3 : ℝ) :=
    (Real.rpow_natCast l 3).symm
  rw [Real.sqrt_eq_rpow, hpow3]
  calc
    C * Real.rpow l (1 / 2) * Real.sqrt g * Real.rpow l 3 =
        C * Real.sqrt g * (Real.rpow l (1 / 2) * Real.rpow l 3) := by ring
    _ = C * Real.sqrt g * Real.rpow l (7 / 2) := by
      have hadd : Real.rpow l (1 / 2) * Real.rpow l 3 =
          Real.rpow l ((1 / 2) + 3) := (Real.rpow_add hl (1 / 2) 3).symm
      rw [hadd]
      norm_num

/-- The error Markov leg at the successor exponent. -/
theorem measureReal_localizedError_gt_le_v2 (M : ABKModel d)
    {c C ep : ℝ} (hc : 0 < c) (hC : 0 < C) (hep : 0 < ep) (hep4 : ep ≤ 1 / 4)
    (hcal : c ≤ ((2 * Real.exp 1 * C)⁻¹) ^ 2) (hrange : c ≤ C⁻¹)
    (hfloor : 2 * Real.exp 1 * C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep)
    (hmomE : ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
      p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, localizedError M n y omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p)
    (hp1 : 1 ≤ siteMarkovExponentV2 M c ep) (n : ℤ) (y : Vec d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
        {omega | ENNReal.ofReal ep < localizedError M n y omega} ≤
      Real.exp (-siteMarkovExponentV2 M c ep) := by
  set p := siteMarkovExponentV2 M c ep
  let l := |Real.log M.gamma|
  have hg : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hl : 0 < l := abs_log_gamma_pos M
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hsqrtp : Real.sqrt p =
      Real.sqrt c * ep * (Real.sqrt M.gamma)⁻¹ * l ^ (-3 : ℤ) := by
    rw [show p = c * ep ^ 2 * M.gamma⁻¹ * l ^ (-6 : ℤ) by
      simp only [p, l, siteMarkovExponentV2]]
    exact sqrt_successor_rate hc.le hep.le hg hl
  have hfirst : C * Real.sqrt p * Real.sqrt M.gamma * l ^ (3 : ℕ) =
      C * Real.sqrt c * ep := by
    rw [hsqrtp]
    exact first_amplitude_eq hg hl
  have hsecond : C * Real.sqrt l * Real.sqrt M.gamma * l ^ (3 : ℕ) =
      C * Real.sqrt M.gamma * Real.rpow l (7 / 2) := second_amplitude_eq hl
  have hroot : Real.sqrt c ≤ (2 * Real.exp 1 * C)⁻¹ := by
    have h := Real.sqrt_le_sqrt hcal
    rwa [Real.sqrt_sq (by positivity : 0 ≤ (2 * Real.exp 1 * C)⁻¹)] at h
  have hfirstCal : C * Real.sqrt c * ep ≤ Real.exp (-1) * ep / 2 := by
    have hcanc : C * (2 * Real.exp 1 * C)⁻¹ = Real.exp (-1) / 2 := by
      rw [Real.exp_neg]
      field_simp
    calc C * Real.sqrt c * ep ≤ (Real.exp (-1) / 2) * ep :=
          mul_le_mul_of_nonneg_right
            (by simpa only [hcanc] using mul_le_mul_of_nonneg_left hroot hC.le) hep.le
      _ = Real.exp (-1) * ep / 2 := by ring
  have hsecondCal : C * Real.sqrt M.gamma * Real.rpow l (7 / 2) ≤
      Real.exp (-1) * ep / 2 := by
    have h := mul_le_mul_of_nonneg_left hfloor (by positivity : 0 ≤ Real.exp (-1) / 2)
    have he : Real.exp (-1) / 2 * (2 * Real.exp 1 * C * Real.sqrt M.gamma *
        Real.rpow l (7 / 2)) = C * Real.sqrt M.gamma * Real.rpow l (7 / 2) := by
      rw [Real.exp_neg]
      field_simp
    rw [he] at h
    calc C * Real.sqrt M.gamma * Real.rpow l (7 / 2) ≤
          (Real.exp (-1) / 2) * ep := by simpa only [he] using h
      _ = Real.exp (-1) * ep / 2 := by ring
  have hampEq : C * (Real.sqrt p + Real.sqrt l) * Real.sqrt M.gamma * l ^ (3 : ℕ) =
      C * Real.sqrt p * Real.sqrt M.gamma * l ^ (3 : ℕ) +
        C * Real.sqrt l * Real.sqrt M.gamma * l ^ (3 : ℕ) := by ring
  have htotal : C * (Real.sqrt p + Real.sqrt l) * Real.sqrt M.gamma * l ^ (3 : ℕ) ≤
      Real.exp (-1) * ep := by
    rw [hampEq, hfirst, hsecond]
    linarith only [hfirstCal, hsecondCal]
  have hApos : 0 < C * (Real.sqrt p + Real.sqrt l) * Real.sqrt M.gamma * l ^ (3 : ℕ) := by
    have hsqrtp : 0 < Real.sqrt p := Real.sqrt_pos.2 hppos
    have hsqrtg : 0 < Real.sqrt M.gamma := Real.sqrt_pos.2 hg
    positivity
  exact measureReal_gt_le_exp_of_lintegral_rpow_le _
    (measurable_localizedError M n y) hApos hep hppos
    (hmomE p n y hp1 (siteMarkovExponentV2_le_range M hC hrange hep hep4))
    htotal

/-- The regularity Markov leg at the successor exponent. -/
theorem measureReal_localizedRegularity_gt_le_v2 (M : ABKModel d)
    {c creg Creg ep : ℝ} (hcreg : 0 < creg) (hCreg : 0 < Creg)
    (hc_le : c ≤ creg)
    (hmomX : ∀ (n : ℤ) (y : Vec d),
      (∫⁻ omega, localizedRegularity M n y omega ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal Creg ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)))
    (hep : 0 < ep) (hep4 : ep ≤ 1 / 4) (n : ℤ) (y : Vec d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
        {omega | ENNReal.ofReal (2 * Creg) < localizedRegularity M n y omega} ≤
      Real.exp (-siteMarkovExponentV2 M c ep) := by
  let px := creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)
  have hpx : 0 < px := by
    dsimp only [px]
    exact mul_pos (mul_pos hcreg (inv_pos.2 M.shellPrefix.gamma_pos))
      (zpow_pos (abs_log_gamma_pos M) _)
  have hstep := measure_gt_le_of_lintegral_rpow_le _
    (measurable_localizedRegularity M n y) hCreg
    (by linarith only [hCreg] : 0 < 2 * Creg) hpx (hmomX n y)
  have hhalf : Creg / (2 * Creg) = 1 / 2 := by field_simp
  have hval : ((1 : ℝ) / 2) ^ px = Real.exp (-(px * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (1 : ℝ) / 2), one_div, Real.log_inv]
    congr 1
    ring
  rw [hhalf, hval] at hstep
  have hreal : (Cutoff.cutoffSampleLaw M).toMeasure.real
      {omega | ENNReal.ofReal (2 * Creg) < localizedRegularity M n y omega} ≤
      Real.exp (-(px * Real.log 2)) :=
    ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hstep
  refine hreal.trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact siteMarkovExponentV2_le_regularity M hc_le hcreg.le hep hep4

/-- The constant serving the error calibration, both moment ranges, and the
shell comparison. -/
def siteTailConstV2 (C creg Cinj : ℝ) : ℝ :=
  min (min (min (((2 * Real.exp 1 * C)⁻¹) ^ 2) C⁻¹) creg)
    (siteThresholdConst Cinj ^ 2)

theorem siteTailConstV2_pos {C creg Cinj : ℝ}
    (hC : 0 < C) (hcreg : 0 < creg) (hCinj : 0 < Cinj) :
    0 < siteTailConstV2 C creg Cinj := by
  rw [siteTailConstV2]
  exact lt_min (lt_min (lt_min (sq_pos_of_pos (inv_pos.2 (by positivity)))
    (inv_pos.2 hC)) hcreg) (sq_pos_of_pos (siteThresholdConst_pos hCinj))

theorem siteTailConstV2_le_error (C creg Cinj : ℝ) :
    siteTailConstV2 C creg Cinj ≤ ((2 * Real.exp 1 * C)⁻¹) ^ 2 := by
  rw [siteTailConstV2]
  exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

theorem siteTailConstV2_le_range (C creg Cinj : ℝ) :
    siteTailConstV2 C creg Cinj ≤ C⁻¹ := by
  rw [siteTailConstV2]
  exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))

theorem siteTailConstV2_le_regularity (C creg Cinj : ℝ) :
    siteTailConstV2 C creg Cinj ≤ creg :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem siteTailConstV2_le_shell (C creg Cinj : ℝ) :
    siteTailConstV2 C creg Cinj ≤ siteThresholdConst Cinj ^ 2 := min_le_right _ _

/-- The complement of a good cube has the successor two-leg tail. -/
theorem measureReal_compl_goodCubeEvent_le_v2 (M : ABKModel d)
    {c C creg Creg ep : ℝ} (hc : 0 < c) (hC : 0 < C) (hcreg : 0 < creg)
    (hCreg : 0 < Creg) (hep : 0 < ep) (hep4 : ep ≤ 1 / 4)
    (hcal : c ≤ ((2 * Real.exp 1 * C)⁻¹) ^ 2) (hrange : c ≤ C⁻¹)
    (hc_le : c ≤ creg)
    (hfloor : 2 * Real.exp 1 * C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep)
    (hmomE : ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
      p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, localizedError M n y omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p)
    (hmomX : ∀ (n : ℤ) (y : Vec d),
      (∫⁻ omega, localizedRegularity M n y omega ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal Creg ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)))
    (hp1 : 1 ≤ siteMarkovExponentV2 M c ep) (n : ℤ) (y : Vec d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real (goodCubeEvent M Creg n y ep)ᶜ ≤
      2 * Real.exp (-siteMarkovExponentV2 M c ep) := by
  rw [compl_goodCubeEvent_eq]
  refine (measureReal_union_le _ _).trans ?_
  have hE := measureReal_localizedError_gt_le_v2 M hc hC hep hep4 hcal hrange
    hfloor hmomE hp1 n y
  have hX := measureReal_localizedRegularity_gt_le_v2 M hcreg hCreg hc_le
    hmomX hep hep4 n y
  linarith only [hE, hX]

private theorem three_mul_exp_le_exp {s : ℝ} (hs : Real.log 3 ≤ s) :
    3 * Real.exp (-(2 * s)) ≤ Real.exp (-s) := by
  have h1 : Real.exp (-(2 * s)) = Real.exp (-s) * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hthird : Real.exp (-s) ≤ 1 / 3 := by
    have h := Real.exp_le_exp.2 (neg_le_neg hs)
    have he : Real.exp (-Real.log 3) = 1 / 3 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3), one_div]
    exact h.trans_eq he
  have hpos := (Real.exp_pos (-s)).le
  calc
    3 * Real.exp (-(2 * s)) = 3 * Real.exp (-s) * Real.exp (-s) := by rw [h1]; ring
    _ ≤ 1 * Real.exp (-s) :=
      mul_le_mul_of_nonneg_right (by linarith only [hthird]) hpos
    _ = Real.exp (-s) := one_mul _

/-- The unshifted site family has the successor per-site tail. -/
theorem measureReal_siteBadEventFive_le_v2 (M : ABKModel d)
    {c C creg Creg Cinj ep : ℝ} (hc : 0 < c) (hC : 0 < C) (hcreg : 0 < creg)
    (hCreg : 0 < Creg) (hCinj : 0 < Cinj) (hep : 0 < ep) (hep4 : ep ≤ 1 / 4)
    (hcal : c ≤ ((2 * Real.exp 1 * C)⁻¹) ^ 2) (hrange : c ≤ C⁻¹)
    (hc_reg : c ≤ creg) (hc_shell : c ≤ siteThresholdConst Cinj ^ 2)
    (hfloor : 2 * Real.exp 1 * C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep)
    (hmomE : ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
      p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, localizedError M n y omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p)
    (hmomX : ∀ (n : ℤ) (y : Vec d),
      (∫⁻ omega, localizedRegularity M n y omega ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal Creg ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)))
    (hp1 : 1 ≤ siteMarkovExponentV2 M c ep)
    (hlog3 : Real.log 3 ≤ siteBadRateSqV2 M c ep)
    (hthr : 1 ≤ siteThresholdConst Cinj * ep * (Real.sqrt M.gamma)⁻¹)
    (n : ℤ) (L : ℕ) (z : Percolation.Site d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
        (siteBadEventFive M Creg (siteThresholdConst Cinj) ep n L z) ≤
      Real.exp (-(siteBadRateSqV2 M c ep *
        (3 : ℝ) ^ (sitePathExponent * (L : ℝ)))) := by
  have hkappa := siteThresholdConst_pos hCinj
  have hp := siteMarkovExponentV2_pos M hc hep
  have hshellrate : siteBadRateSqV2 M c ep ≤
      siteThresholdConst Cinj ^ 2 * ep ^ 2 * M.gamma⁻¹ := by
    have h := siteMarkovExponentV2_le_shell M (ep := ep) hc_shell
    rw [siteBadRateSqV2]
    linarith only [h, hp]
  have hshell : ∀ K : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure.real
          (shellExcessEvent M (siteThresholdConst Cinj) ep n K z) ≤
        Real.exp (-(siteBadRateSqV2 M c ep *
          (3 : ℝ) ^ (sitePathExponent * (K : ℝ)))) := by
    intro K
    refine (measureReal_shellExcessEvent_le M hkappa hep hthr n K z).trans
      (Real.exp_le_exp.2 (neg_le_neg ?_))
    exact mul_le_mul_of_nonneg_right hshellrate (Real.rpow_nonneg (by norm_num) _)
  cases L with
  | zero =>
      rw [siteBadEventFive_zero]
      norm_num only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
      have hshell0 :
          (Cutoff.cutoffSampleLaw M).toMeasure.real
              (shellExcessEvent M (siteThresholdConst Cinj) ep n 0 z) ≤
            Real.exp (-siteMarkovExponentV2 M c ep) := by
        refine (measureReal_shellExcessEvent_le M hkappa hep hthr n 0 z).trans
          (Real.exp_le_exp.2 (neg_le_neg ?_))
        norm_num only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
        exact siteMarkovExponentV2_le_shell M (ep := ep) hc_shell
      have hgood := measureReal_compl_goodCubeEvent_le_v2 M hc hC hcreg hCreg hep
        hep4 hcal hrange hc_reg hfloor hmomE hmomX hp1 n (rescaledLatticePoint n z)
      have hp2 : siteMarkovExponentV2 M c ep = 2 * siteBadRateSqV2 M c ep := by
        rw [siteBadRateSqV2]
        ring
      calc
        (Cutoff.cutoffSampleLaw M).toMeasure.real
            ((goodCubeEvent M Creg n (rescaledLatticePoint n z) ep)ᶜ ∪
              shellExcessEvent M (siteThresholdConst Cinj) ep n 0 z) ≤
            (Cutoff.cutoffSampleLaw M).toMeasure.real
                (goodCubeEvent M Creg n (rescaledLatticePoint n z) ep)ᶜ +
              (Cutoff.cutoffSampleLaw M).toMeasure.real
                (shellExcessEvent M (siteThresholdConst Cinj) ep n 0 z) :=
          measureReal_union_le _ _
        _ ≤ 2 * Real.exp (-siteMarkovExponentV2 M c ep) +
              Real.exp (-siteMarkovExponentV2 M c ep) := add_le_add hgood hshell0
        _ = 3 * Real.exp (-(2 * siteBadRateSqV2 M c ep)) := by rw [hp2]; ring
        _ ≤ Real.exp (-siteBadRateSqV2 M c ep) := three_mul_exp_le_exp hlog3
  | succ K =>
      rw [siteBadEventFive_succ]
      exact hshell (K + 1)

/-- The shifted site family has the successor per-site tail. -/
theorem measureReal_shiftedSiteBadEventFive_le_v2 (M : ABKModel d)
    {c C creg Creg Cinj ep : ℝ} (hc : 0 < c) (hC : 0 < C) (hcreg : 0 < creg)
    (hCreg : 0 < Creg) (hCinj : 0 < Cinj) (hep : 0 < ep) (hep4 : ep ≤ 1 / 4)
    (hcal : c ≤ ((2 * Real.exp 1 * C)⁻¹) ^ 2) (hrange : c ≤ C⁻¹)
    (hc_reg : c ≤ creg) (hc_shell : c ≤ siteThresholdConst Cinj ^ 2)
    (hfloor : 2 * Real.exp 1 * C * Real.sqrt M.gamma *
      Real.rpow |Real.log M.gamma| (7 / 2) ≤ ep)
    (hmomE : ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
      p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, localizedError M n y omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p)
    (hmomX : ∀ (n : ℤ) (y : Vec d),
      (∫⁻ omega, localizedRegularity M n y omega ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal Creg ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)))
    (hp1 : 1 ≤ siteMarkovExponentV2 M c ep)
    (hlog3 : Real.log 3 ≤ siteBadRateSqV2 M c ep)
    (hthr : 1 ≤ siteThresholdConst Cinj * ep * (Real.sqrt M.gamma)⁻¹)
    (n : ℤ) (l : ℕ) (z : Percolation.Site d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
        (shiftedSiteBadEventFive M Creg (siteThresholdConst Cinj) ep n l z) ≤
      Real.exp (-(siteTailRateV2 d M c ep ^ 2 *
        (3 : ℝ) ^ (sitePathExponent * (l : ℝ)))) := by
  by_cases hlq : l < Provider.Percolation.sepShift d
  · rw [shiftedSiteBadEventFive_of_lt M Creg (siteThresholdConst Cinj) ep n hlq z,
      measureReal_empty]
    exact (Real.exp_pos _).le
  · push Not at hlq
    rw [shiftedSiteBadEventFive_of_le M Creg (siteThresholdConst Cinj) ep n hlq z]
    refine (measureReal_siteBadEventFive_le_v2 M hc hC hcreg hCreg hCinj hep hep4
      hcal hrange hc_reg hc_shell hfloor hmomE hmomX hp1 hlog3 hthr n
      (l - Provider.Percolation.sepShift d) z).trans
      (Real.exp_le_exp.2 (neg_le_neg (le_of_eq ?_)))
    have hcast : ((l - Provider.Percolation.sepShift d : ℕ) : ℝ) =
        (l : ℝ) - (Provider.Percolation.sepShift d : ℝ) := Nat.cast_sub hlq
    rw [siteTailRateV2]
    have hrate : 0 ≤ siteTailRateSqV2 d M c ep := by
      rw [siteTailRateSqV2, siteBadRateSqV2]
      exact mul_nonneg (div_nonneg (siteMarkovExponentV2_pos M hc hep).le (by norm_num))
        (Real.rpow_nonneg (by norm_num) _)
    rw [Real.sq_sqrt hrate, siteTailRateSqV2, hcast, mul_assoc,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 2
    ring

/-- The shifted site-tail estimate derived from the two successor moment
inputs. -/
theorem measureReal_shiftedSiteBadEventFive_le_of_epsLower_v2 (M : ABKModel d)
    {c C creg Creg Cinj Cpath ep : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hcreg : 0 < creg) (hCreg : 0 < Creg) (hCinj : 0 < Cinj)
    (hcal : c ≤ ((2 * Real.exp 1 * C)⁻¹) ^ 2) (hrange : c ≤ C⁻¹)
    (hc_reg : c ≤ creg) (hc_shell : c ≤ siteThresholdConst Cinj ^ 2)
    (hmomE : ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
      p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
      (∫⁻ omega, localizedError M n y omega ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p)
    (hmomX : ∀ (n : ℤ) (y : Vec d),
      (∫⁻ omega, localizedRegularity M n y omega ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal Creg ^
          (creg * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)))
    (hep : ep ∈ Set.Icc (siteEpsLowerConstV2 d c Cinj Cpath C *
      Real.sqrt M.gamma * Real.rpow |Real.log M.gamma| (7 / 2)) (1 / 4))
    (n : ℤ) (l : ℕ) (z : Percolation.Site d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
        (shiftedSiteBadEventFive M Creg (siteThresholdConst Cinj) ep n l z) ≤
      Real.exp (-(siteTailRateV2 d M c ep ^ 2 *
        (3 : ℝ) ^ (sitePathExponent * (l : ℝ)))) := by
  have hepPos := pos_of_epsLowerV2 M hCinj hC.le hep.1
  exact measureReal_shiftedSiteBadEventFive_le_v2 M hc hC hcreg hCreg hCinj hepPos hep.2
    hcal hrange hc_reg hc_shell
    (two_exp_mul_sqrt_mul_rpow_le_of_epsLowerV2 M hCinj hep.1)
    hmomE hmomX
    (one_le_siteMarkovExponentV2_of_epsLower M hc hCinj hC.le hep.1)
    (log_three_le_siteBadRateSqV2_of_epsLower M hc hCinj hC.le hep.1)
    (one_le_siteThresholdConst_mul_of_epsLowerV2 M hCinj hC.le hep.1) n l z

end

end Algsuperdiff.Section5.Provider
