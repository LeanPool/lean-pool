/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyPointwise
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# High-contrast homogenization: Provider.Response.ProfileMaximumBadLp

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The maximal bad event in `L²`

Only a `Q`-moment of the complete maximum is used.  Hölder at exponents
`Q / 2` and `Q / (Q - 2)` separates its `L²` restriction from the probability
of the bad event; no higher moment or independence assumption enters.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Restricting an extended-real random variable to `{M > 1}` costs its
`L^Q` norm times the probability of that event to the Hölder exponent. -/
theorem eLpNorm_indicator_gt_one_le_mul_measure
    (P : Measure Ω) {Q : ℝ} (hQ : 2 < Q) {M : Ω → ℝ≥0∞}
    (hM : AEMeasurable M P) :
    eLpNorm ({a | (1 : ℝ≥0∞) < M a}.indicator M) 2 P ≤
      eLpNorm M (ENNReal.ofReal Q) P *
        P {a | (1 : ℝ≥0∞) < M a} ^ (1 / 2 - Q⁻¹) := by
  let bad : Set Ω := {a | (1 : ℝ≥0∞) < M a}
  let R : ℝ := 2 * Q / (Q - 2)
  let I : Ω → ℝ≥0∞ := bad.indicator fun _ => 1
  have hQ0 : 0 < Q := lt_trans (by norm_num) hQ
  have hden : 0 < Q - 2 := by linarith only [hQ]
  have hR0 : 0 < R := by
    dsimp only [R]
    positivity
  have hholderExp : 1 / 2 = 1 / Q + 1 / R := by
    dsimp only [R]
    field_simp
    ring
  have hRinv : 1 / R = 1 / 2 - Q⁻¹ := by
    rw [hholderExp]
    ring
  have hbad : NullMeasurableSet bad P := by
    exact nullMeasurableSet_lt aemeasurable_const hM
  have hI : AEMeasurable I P := by
    exact aemeasurable_const.indicator₀ hbad
  have hmul : M * I = bad.indicator M := by
    funext a
    by_cases ha : a ∈ bad <;> simp [I, ha]
  have hholder := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
    (p := 2) (q := Q) (r := R) (by norm_num) hQ hholderExp P hM hI
  have hnorm2 :
      eLpNorm (bad.indicator M) 2 P =
        (∫⁻ a, (M * I) a ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (hM.indicator₀ hbad).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, enorm_eq_self, hmul]
  have hnormQ :
      eLpNorm M (ENNReal.ofReal Q) P =
        (∫⁻ a, M a ^ Q ∂P) ^ (1 / Q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hQ0) ENNReal.ofReal_ne_top hM.aestronglyMeasurable,
      ENNReal.toReal_ofReal hQ0.le]
    simp only [enorm_eq_self]
  have hnormI :
      (∫⁻ a, I a ^ R ∂P) ^ (1 / R) = P bad ^ (1 / R) := by
    have hRp : ENNReal.ofReal R ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hR0
    have hdef : eLpNorm I (ENNReal.ofReal R) P =
        (∫⁻ a, I a ^ R ∂P) ^ (1 / R) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hRp ENNReal.ofReal_ne_top
        hI.aestronglyMeasurable, ENNReal.toReal_ofReal hR0.le]
      simp only [enorm_eq_self]
    rw [← hdef, show I = bad.indicator (fun _ : Ω => (1 : ℝ≥0∞)) by rfl,
      eLpNorm_indicator_const₀ hbad hRp ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hR0.le]
    simp
  rw [hnorm2, hnormQ]
  rw [hnormI, hRinv] at hholder
  simpa only [bad] using hholder

/-- The pathwise comparison `M ≤ W + beta` and the `Q`-moment of `W` give the
small-drift probability bound for the event `{M > 1}`. -/
theorem measure_gt_one_le_of_complete_maximum
    (P : Measure Ω) {Q h beta : ℝ} (hQ : 2 < Q)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    {M W : Ω → ℝ≥0∞} (hW : AEMeasurable W P)
    (hpoint : ∀ a, M a ≤ W a + ENNReal.ofReal beta)
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h) :
    P {a | (1 : ℝ≥0∞) < M a} ≤
      ENNReal.ofReal (h / (1 - beta) ^ Q) := by
  let c : ℝ := 1 - beta
  let ce : ℝ≥0∞ := ENNReal.ofReal c
  have hQ0 : 0 < Q := lt_trans (by norm_num) hQ
  have hc0 : 0 < c := by
    dsimp only [c]
    linarith only [hbeta1]
  have hsum : ce + ENNReal.ofReal beta = 1 := by
    rw [show ce = ENNReal.ofReal c by rfl, ← ENNReal.ofReal_add hc0.le hbeta0]
    have : c + beta = 1 := by dsimp only [c]; ring
    rw [this]
    norm_num
  have hsubset : {a | (1 : ℝ≥0∞) < M a} ⊆ {a | ce ≤ W a} := by
    intro a ha
    by_contra hnot
    have hlt : W a < ce := lt_of_not_ge hnot
    have hadd : W a + ENNReal.ofReal beta <
        ce + ENNReal.ofReal beta :=
      ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hlt
    rw [hsum] at hadd
    have hMlt : M a < 1 := (hpoint a).trans_lt hadd
    exact (not_lt_of_ge (le_of_lt ha)) hMlt
  have hpowSubset : {a | ce ≤ W a} ⊆ {a | ce ^ Q ≤ W a ^ Q} := by
    intro a ha
    exact ENNReal.rpow_le_rpow ha hQ0.le
  have hmarkov : P {a | ce ^ Q ≤ W a ^ Q} ≤
      (∫⁻ a, W a ^ Q ∂P) / ce ^ Q := by
    exact meas_ge_le_lintegral_div (hW.pow_const Q)
      (ne_of_gt (ENNReal.rpow_pos_of_nonneg (by
        change 0 < ENNReal.ofReal c
        exact ENNReal.ofReal_pos.mpr hc0) hQ0.le))
      (ENNReal.rpow_ne_top_of_nonneg hQ0.le (by
        change ENNReal.ofReal c ≠ ⊤
        exact ENNReal.ofReal_ne_top))
  calc
    P {a | (1 : ℝ≥0∞) < M a} ≤ P {a | ce ≤ W a} := measure_mono hsubset
    _ ≤ P {a | ce ^ Q ≤ W a ^ Q} := measure_mono hpowSubset
    _ ≤ (∫⁻ a, W a ^ Q ∂P) / ce ^ Q := hmarkov
    _ ≤ ENNReal.ofReal h / ce ^ Q := ENNReal.div_le_div_right hmoment _
    _ = ENNReal.ofReal (h / (1 - beta) ^ Q) := by
      rw [show ce = ENNReal.ofReal c by rfl,
        ENNReal.ofReal_rpow_of_nonneg hc0.le hQ0.le,
        ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hc0 Q)]

/-- The complete-maximum comparison gives exactly the correlated bad-event
majorant used by the profile response estimate. -/
theorem eLpNorm_indicator_gt_one_le_profileBadMajorant
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Q h beta : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    {M W : Ω → ℝ≥0∞} (hM : AEMeasurable M P) (hW : AEMeasurable W P)
    (hpoint : ∀ a, M a ≤ W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm M (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h) :
    eLpNorm ({a | (1 : ℝ≥0∞) < M a}.indicator M) 2 P ≤
      ENNReal.ofReal (profileBadMajorant Q h beta) := by
  let alpha : ℝ := 1 / 2 - Q⁻¹
  let bad : Set Ω := {a | (1 : ℝ≥0∞) < M a}
  have hQ0 : 0 < Q := lt_trans (by norm_num) hQ
  have hinvHalf : Q⁻¹ < 1 / 2 := by
    have hraw : Q⁻¹ < (2 : ℝ)⁻¹ :=
      (inv_lt_inv₀ hQ0 (by norm_num)).2 hQ
    simpa only [one_div] using hraw
  have halpha0 : 0 < alpha := by
    dsimp only [alpha]
    linarith only [hinvHalf]
  have hholder : eLpNorm (bad.indicator M) 2 P ≤
      eLpNorm M (ENNReal.ofReal Q) P * P bad ^ alpha := by
    simpa only [bad, alpha] using
      eLpNorm_indicator_gt_one_le_mul_measure P hQ hM
  by_cases hbeta1 : beta < 1
  · let c : ℝ := 1 - beta
    have hc0 : 0 < c := by
      dsimp only [c]
      linarith only [hbeta1]
    have hprob : P bad ≤ ENNReal.ofReal (h / c ^ Q) := by
      simpa only [bad, c] using
        measure_gt_one_le_of_complete_maximum P hQ hbeta hbeta1 hW hpoint hmoment
    have hprobPow : P bad ^ alpha ≤
        ENNReal.ofReal ((h / c ^ Q) ^ alpha) := by
      calc
        P bad ^ alpha ≤ (ENNReal.ofReal (h / c ^ Q)) ^ alpha :=
          ENNReal.rpow_le_rpow hprob halpha0.le
        _ = ENNReal.ofReal ((h / c ^ Q) ^ alpha) := by
          rw [ENNReal.ofReal_rpow_of_nonneg
            (div_nonneg hh (Real.rpow_nonneg hc0.le _)) halpha0.le]
    have hscalar : (h / c ^ Q) ^ alpha =
        c ^ (1 - Q / 2) * h ^ alpha := by
      rw [Real.div_rpow hh (Real.rpow_nonneg hc0.le Q),
        ← Real.rpow_mul hc0.le]
      have hexp : Q * alpha = Q / 2 - 1 := by
        dsimp only [alpha]
        field_simp
      rw [hexp, div_eq_mul_inv, ← Real.rpow_neg hc0.le]
      rw [show -(Q / 2 - 1) = 1 - Q / 2 by ring]
      ring
    have hleft0 : 0 ≤ h ^ Q⁻¹ + beta :=
      add_nonneg (Real.rpow_nonneg hh _) hbeta
    have hright0 : 0 ≤ c ^ (1 - Q / 2) * h ^ alpha :=
      mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg hh _)
    calc
      eLpNorm (bad.indicator M) 2 P ≤
          eLpNorm M (ENNReal.ofReal Q) P * P bad ^ alpha := hholder
      _ ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta) *
          ENNReal.ofReal ((h / c ^ Q) ^ alpha) :=
        mul_le_mul hnorm hprobPow (by simp) (by simp)
      _ = ENNReal.ofReal ((h ^ Q⁻¹ + beta) *
          (c ^ (1 - Q / 2) * h ^ alpha)) := by
        rw [hscalar, ← ENNReal.ofReal_mul hleft0]
      _ = ENNReal.ofReal (profileBadMajorant Q h beta) := by
        rw [profileBadMajorant_of_lt_one hbeta1]
        dsimp only [c, alpha]
        congr 1
        ring
  · have hbetaOne : 1 ≤ beta := not_lt.mp hbeta1
    have hprob : P bad ≤ 1 := by
      calc P bad ≤ P Set.univ := measure_mono (Set.subset_univ bad)
        _ = 1 := measure_univ
    have hprobPow : P bad ^ alpha ≤ 1 := by
      simpa only [ENNReal.one_rpow] using
        ENNReal.rpow_le_rpow hprob halpha0.le
    calc
      eLpNorm (bad.indicator M) 2 P ≤
          eLpNorm M (ENNReal.ofReal Q) P * P bad ^ alpha := hholder
      _ ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta) * 1 :=
        mul_le_mul hnorm hprobPow (by simp) (by simp)
      _ = ENNReal.ofReal (profileBadMajorant Q h beta) := by
        rw [profileBadMajorant_of_one_le hbetaOne, mul_one]

/-- **Companion of `eLpNorm_indicator_gt_one_le_mul_measure`.**  Restricting to
`{lam < M}` costs the `L^Q` norm times the probability to the Hölder exponent —
at every level, the fixed level playing no role in the argument. -/
theorem eLpNorm_indicator_gt_level_le_mul_measure
    (P : Measure Ω) {Q : ℝ} (hQ : 2 < Q) (lam : ℝ≥0∞) {M : Ω → ℝ≥0∞}
    (hM : AEMeasurable M P) :
    eLpNorm ({a | lam < M a}.indicator M) 2 P ≤
      eLpNorm M (ENNReal.ofReal Q) P *
        P {a | lam < M a} ^ (1 / 2 - Q⁻¹) := by
  let bad : Set Ω := {a | lam < M a}
  let R : ℝ := 2 * Q / (Q - 2)
  let I : Ω → ℝ≥0∞ := bad.indicator fun _ => 1
  have hQ0 : 0 < Q := lt_trans (by norm_num) hQ
  have hden : 0 < Q - 2 := by linarith only [hQ]
  have hR0 : 0 < R := by
    dsimp only [R]
    positivity
  have hholderExp : 1 / 2 = 1 / Q + 1 / R := by
    dsimp only [R]
    field_simp
    ring
  have hRinv : 1 / R = 1 / 2 - Q⁻¹ := by
    rw [hholderExp]
    ring
  have hbad : NullMeasurableSet bad P := nullMeasurableSet_lt aemeasurable_const hM
  have hI : AEMeasurable I P := aemeasurable_const.indicator₀ hbad
  have hmul : M * I = bad.indicator M := by
    funext a
    by_cases ha : a ∈ bad <;> simp [I, ha]
  have hholder := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
    (p := 2) (q := Q) (r := R) (by norm_num) hQ hholderExp P hM hI
  have hnorm2 :
      eLpNorm (bad.indicator M) 2 P =
        (∫⁻ a, (M * I) a ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (hM.indicator₀ hbad).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, enorm_eq_self, hmul]
  have hnormQ :
      eLpNorm M (ENNReal.ofReal Q) P =
        (∫⁻ a, M a ^ Q ∂P) ^ (1 / Q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hQ0) ENNReal.ofReal_ne_top hM.aestronglyMeasurable,
      ENNReal.toReal_ofReal hQ0.le]
    simp only [enorm_eq_self]
  have hnormI :
      (∫⁻ a, I a ^ R ∂P) ^ (1 / R) = P bad ^ (1 / R) := by
    have hRp : ENNReal.ofReal R ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hR0
    have hdef : eLpNorm I (ENNReal.ofReal R) P =
        (∫⁻ a, I a ^ R ∂P) ^ (1 / R) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hRp ENNReal.ofReal_ne_top
        hI.aestronglyMeasurable, ENNReal.toReal_ofReal hR0.le]
      simp only [enorm_eq_self]
    rw [← hdef, show I = bad.indicator (fun _ : Ω => (1 : ℝ≥0∞)) by rfl,
      eLpNorm_indicator_const₀ hbad hRp ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hR0.le]
    simp
  rw [hnorm2, hnormQ]
  rw [hnormI, hRinv] at hholder
  simpa only [bad] using hholder

/-! ## Companion 2: the small-drift probability bound, at a released level -/

/-- **Companion of `measure_gt_one_le_of_complete_maximum`.**  The deterministic
part `beta` need only sit below the **split level**, not below `1`. -/
theorem measure_gt_level_le_of_complete_maximum
    (P : Measure Ω) {Q h beta lev : ℝ} (hQ : 2 < Q)
    (hbeta0 : 0 ≤ beta) (hbetalev : beta < lev)
    {M W : Ω → ℝ≥0∞} (hW : AEMeasurable W P)
    (hpoint : ∀ a, M a ≤ W a + ENNReal.ofReal beta)
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h) :
    P {a | ENNReal.ofReal lev < M a} ≤
      ENNReal.ofReal (h / (lev - beta) ^ Q) := by
  let c : ℝ := lev - beta
  let ce : ℝ≥0∞ := ENNReal.ofReal c
  have hQ0 : 0 < Q := lt_trans (by norm_num) hQ
  have hc0 : 0 < c := by
    dsimp only [c]
    linarith only [hbetalev]
  have hsum : ce + ENNReal.ofReal beta = ENNReal.ofReal lev := by
    rw [show ce = ENNReal.ofReal c by rfl, ← ENNReal.ofReal_add hc0.le hbeta0]
    have : c + beta = lev := by dsimp only [c]; ring
    rw [this]
  have hsubset : {a | ENNReal.ofReal lev < M a} ⊆ {a | ce ≤ W a} := by
    intro a ha
    by_contra hnot
    have hlt : W a < ce := lt_of_not_ge hnot
    have hadd : W a + ENNReal.ofReal beta < ce + ENNReal.ofReal beta :=
      ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hlt
    rw [hsum] at hadd
    have hMlt : M a < ENNReal.ofReal lev := (hpoint a).trans_lt hadd
    exact (not_lt_of_ge (le_of_lt ha)) hMlt
  have hpowSubset : {a | ce ≤ W a} ⊆ {a | ce ^ Q ≤ W a ^ Q} := by
    intro a ha
    exact ENNReal.rpow_le_rpow ha hQ0.le
  have hmarkov : P {a | ce ^ Q ≤ W a ^ Q} ≤ (∫⁻ a, W a ^ Q ∂P) / ce ^ Q := by
    exact meas_ge_le_lintegral_div (hW.pow_const Q)
      (ne_of_gt (ENNReal.rpow_pos_of_nonneg (by
        change 0 < ENNReal.ofReal c
        exact ENNReal.ofReal_pos.mpr hc0) hQ0.le))
      (ENNReal.rpow_ne_top_of_nonneg hQ0.le (by
        change ENNReal.ofReal c ≠ ⊤
        exact ENNReal.ofReal_ne_top))
  calc
    P {a | ENNReal.ofReal lev < M a} ≤ P {a | ce ≤ W a} := measure_mono hsubset
    _ ≤ P {a | ce ^ Q ≤ W a ^ Q} := measure_mono hpowSubset
    _ ≤ (∫⁻ a, W a ^ Q ∂P) / ce ^ Q := hmarkov
    _ ≤ ENNReal.ofReal h / ce ^ Q := ENNReal.div_le_div_right hmoment _
    _ = ENNReal.ofReal (h / (lev - beta) ^ Q) := by
      rw [show ce = ENNReal.ofReal c by rfl,
        ENNReal.ofReal_rpow_of_nonneg hc0.le hQ0.le,
        ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hc0 Q)]

/-! ## Companion 3: the bad-event majorant, at a released level -/

/-- **Companion of `eLpNorm_indicator_gt_one_le_profileBadMajorant`.**  The
complete-maximum comparison at a released split level. -/
theorem eLpNorm_indicator_gt_level_le_profileBadMajorantAt
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Q h beta lev : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    {M W : Ω → ℝ≥0∞} (hM : AEMeasurable M P) (hW : AEMeasurable W P)
    (hpoint : ∀ a, M a ≤ W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm M (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h) :
    eLpNorm ({a | ENNReal.ofReal lev < M a}.indicator M) 2 P ≤
      ENNReal.ofReal (profileBadMajorantAt Q h beta lev) := by
  let alpha : ℝ := 1 / 2 - Q⁻¹
  let bad : Set Ω := {a | ENNReal.ofReal lev < M a}
  have hQ0 : 0 < Q := lt_trans (by norm_num) hQ
  have hinvHalf : Q⁻¹ < 1 / 2 := by
    have hraw : Q⁻¹ < (2 : ℝ)⁻¹ := (inv_lt_inv₀ hQ0 (by norm_num)).2 hQ
    simpa only [one_div] using hraw
  have halpha0 : 0 < alpha := by
    dsimp only [alpha]
    linarith only [hinvHalf]
  have hholder : eLpNorm (bad.indicator M) 2 P ≤
      eLpNorm M (ENNReal.ofReal Q) P * P bad ^ alpha := by
    simpa only [bad, alpha] using
      eLpNorm_indicator_gt_level_le_mul_measure P hQ (ENNReal.ofReal lev) hM
  by_cases hbetalev : beta < lev
  · let c : ℝ := lev - beta
    have hc0 : 0 < c := by
      dsimp only [c]
      linarith only [hbetalev]
    have hprob : P bad ≤ ENNReal.ofReal (h / c ^ Q) := by
      simpa only [bad, c] using
        measure_gt_level_le_of_complete_maximum P hQ hbeta hbetalev hW hpoint
          hmoment
    have hprobPow : P bad ^ alpha ≤ ENNReal.ofReal ((h / c ^ Q) ^ alpha) := by
      calc
        P bad ^ alpha ≤ (ENNReal.ofReal (h / c ^ Q)) ^ alpha :=
          ENNReal.rpow_le_rpow hprob halpha0.le
        _ = ENNReal.ofReal ((h / c ^ Q) ^ alpha) := by
          rw [ENNReal.ofReal_rpow_of_nonneg
            (div_nonneg hh (Real.rpow_nonneg hc0.le _)) halpha0.le]
    have hscalar : (h / c ^ Q) ^ alpha = c ^ (1 - Q / 2) * h ^ alpha := by
      rw [Real.div_rpow hh (Real.rpow_nonneg hc0.le Q),
        ← Real.rpow_mul hc0.le]
      have hexp : Q * alpha = Q / 2 - 1 := by
        dsimp only [alpha]
        field_simp
      rw [hexp, div_eq_mul_inv, ← Real.rpow_neg hc0.le]
      rw [show -(Q / 2 - 1) = 1 - Q / 2 by ring]
      ring
    have hleft0 : 0 ≤ h ^ Q⁻¹ + beta :=
      add_nonneg (Real.rpow_nonneg hh _) hbeta
    calc
      eLpNorm (bad.indicator M) 2 P ≤
          eLpNorm M (ENNReal.ofReal Q) P * P bad ^ alpha := hholder
      _ ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta) *
          ENNReal.ofReal ((h / c ^ Q) ^ alpha) :=
        mul_le_mul hnorm hprobPow (by simp) (by simp)
      _ = ENNReal.ofReal ((h ^ Q⁻¹ + beta) * (c ^ (1 - Q / 2) * h ^ alpha)) := by
        rw [hscalar, ← ENNReal.ofReal_mul hleft0]
      _ = ENNReal.ofReal (profileBadMajorantAt Q h beta lev) := by
        rw [profileBadMajorantAt_of_lt hbetalev]
        dsimp only [c, alpha]
        congr 1
        ring
  · have hprob : P bad ≤ 1 := by
      calc P bad ≤ P Set.univ := measure_mono (Set.subset_univ bad)
        _ = 1 := measure_univ
    have hprobPow : P bad ^ alpha ≤ 1 := by
      simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hprob halpha0.le
    calc
      eLpNorm (bad.indicator M) 2 P ≤
          eLpNorm M (ENNReal.ofReal Q) P * P bad ^ alpha := hholder
      _ ≤ ENNReal.ofReal (h ^ Q⁻¹ + beta) * 1 :=
        mul_le_mul hnorm hprobPow (by simp) (by simp)
      _ = ENNReal.ofReal (profileBadMajorantAt Q h beta lev) := by
        rw [profileBadMajorantAt_of_ge (not_lt.mp hbetalev), mul_one]

end

end HCPolySupport.HighContrast.Response
