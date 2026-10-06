/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDelayExponentUniform

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRawPrefactorCap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

/-- The raw corrected-cadence prefactor follows from the polynomial cap on
the initial level-schedule index, the floor bound, and the quarter-rate bound. -/
theorem corrected_cadence_raw_prefactor_cap
    {d : ℕ} {P : Measure (CoeffSpace d)} {lAl : ℤ} {E : BlockMat d}
    {N₀ ns cA : ℕ} {A alpha b0 bA b2 S0 S1 S2 d0 : ℝ}
    {base Cns C7 cns ct2 : ℝ}
    (hbase : (3 : ℝ) ≤ base)
    (hfloor0 : 0 ≤ hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0)
    (hfloor : hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0 ≤ 1 / 9)
    (hrate0 : 0 ≤ linRate A alpha b0 bA b2 cA S0)
    (hrate4 : linRate A alpha b0 bA b2 cA S0 ≤ 1 / 4)
    (hCns : 1 ≤ Cns) (hC7 : 1 ≤ C7)
    (hcns : 0 ≤ cns) (hct2 : 0 ≤ ct2)
    (hstart :
      (3 : ℝ) ^ ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ) ≤
        Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2)) :
    9 / 2 *
        ((1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
          (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
            ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) *
        (Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1) ≤
      (36 * Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹) *
        Real.rpow base (cns / 2 + ct2 / 4) := by
  have hbase0 : (0 : ℝ) < base := by
    linarith only [hbase]
  have hCns0 : (0 : ℝ) ≤ Cns := by
    linarith only [hCns]
  have hC70 : (0 : ℝ) ≤ C7 := by
    linarith only [hC7]
  have hexp0 : (0 : ℝ) ≤ 2 * cns + ct2 := by
    linarith only [hcns, hct2]
  have hbasepow1 : (1 : ℝ) ≤ Real.rpow base (2 * cns + ct2) :=
    Real.one_le_rpow (by linarith only [hbase]) hexp0
  have hCnsSq1 : (1 : ℝ) ≤ Cns ^ (2 : ℕ) :=
    one_le_pow₀ hCns
  have hstartBase : (1 : ℝ) ≤
      Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2) := by
    have hprod : (1 : ℝ) ≤ Cns ^ (2 : ℕ) * C7 := by
      nlinarith only [hCnsSq1, hC7]
    nlinarith only [hprod, hbasepow1]
  have hstartRate :
      (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
          ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) ≤
        (Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2)) ^
          (1 / 4 : ℝ) := by
    have hpowStart := Real.rpow_le_rpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      hstart hrate0
    have hrateStep :
        (Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2)) ^
            linRate A alpha b0 bA b2 cA S0 ≤
          (Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2)) ^
            (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hstartBase hrate4
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)] at hpowStart
    have hpowStart' :
        (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
            ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) ≤
          (Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2)) ^
            linRate A alpha b0 bA b2 cA S0 := by
      simpa only [mul_comm] using hpowStart
    exact le_trans hpowStart' hrateStep
  have hquarter :
      (Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2)) ^
          (1 / 4 : ℝ) =
        Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹ *
          Real.rpow base (cns / 2 + ct2 / 4) := by
    have hsplit :
        (Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2)) ^
            (1 / 4 : ℝ) =
          (Cns ^ (2 : ℕ) * C7) ^ (1 / 4 : ℝ) *
            (Real.rpow base (2 * cns + ct2)) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (mul_nonneg (pow_nonneg hCns0 2) hC70)
        (Real.rpow_nonneg hbase0.le (2 * cns + ct2))
    have hsplitLeft :
        (Cns ^ (2 : ℕ) * C7) ^ (1 / 4 : ℝ) =
          (Cns ^ (2 : ℕ)) ^ (1 / 4 : ℝ) * C7 ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (pow_nonneg hCns0 2) hC70
    have hCnsQuarter :
        (Cns ^ (2 : ℕ)) ^ (1 / 4 : ℝ) = Cns ^ (2 : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast Cns 2, ← Real.rpow_mul hCns0]
      norm_num
    have hbaseQuarter :
        (Real.rpow base (2 * cns + ct2)) ^ (1 / 4 : ℝ) =
          Real.rpow base (cns / 2 + ct2 / 4) := by
      calc
        (Real.rpow base (2 * cns + ct2)) ^ (1 / 4 : ℝ) =
            Real.rpow base ((2 * cns + ct2) * (1 / 4)) :=
          (Real.rpow_mul hbase0.le (2 * cns + ct2) (1 / 4)).symm
        _ = Real.rpow base (cns / 2 + ct2 / 4) := by
          congr 1
          ring
    rw [hsplit, hsplitLeft, hCnsQuarter, hbaseQuarter]
    norm_num
  have hprefPow :
      (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
          ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) ≤
        Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹ *
          Real.rpow base (cns / 2 + ct2 / 4) := by
    rw [← hquarter]
    exact hstartRate
  have hfloorOne :
      1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0 ≤ 2 := by
    linarith only [hfloor]
  have hfloorOne0 :
      0 ≤ 1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0 := by
    linarith only [hfloor0]
  have htail :
      Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1 ≤ 4 := by
    have hexp : linRate A alpha b0 bA b2 cA S0 / 2 ≤ 1 := by
      linarith only [hrate4]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp
    rw [Real.rpow_one] at hpow
    calc
      Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1 ≤
          3 + 1 := add_le_add hpow le_rfl
      _ = 4 := by norm_num
  have htail0 : 0 ≤
      Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1 := by
    exact add_nonneg
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (linRate A alpha b0 bA b2 cA S0 / 2)) zero_le_one
  have hprefPow0 : 0 ≤
      (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
        ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmiddle :
      (1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
          (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
            ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) ≤
        2 * (Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹ *
          Real.rpow base (cns / 2 + ct2 / 4)) := by
    calc
      (1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
          (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
            ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) ≤
        2 * (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
          ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hfloorOne hprefPow0
      _ ≤ 2 * (Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹ *
          Real.rpow base (cns / 2 + ct2 / 4)) :=
            mul_le_mul_of_nonneg_left hprefPow (by norm_num)
  have hmiddle0 : 0 ≤
      (1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
        (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
          ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ)) :=
    mul_nonneg hfloorOne0 hprefPow0
  have hmiddleRight0 : 0 ≤
      2 * (Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹ *
        Real.rpow base (cns / 2 + ct2 / 4)) :=
    le_trans hmiddle0 hmiddle
  calc
    9 / 2 *
          ((1 + hatExcess P (roundedGrid lAl (canonicalMetric E)) N₀ 0) *
            (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
              ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) *
          (Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1) ≤
        9 / 2 *
          (2 * (Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹ *
            Real.rpow base (cns / 2 + ct2 / 4))) * 4 := by
      have hprod := mul_le_mul hmiddle htail htail0 hmiddleRight0
      nlinarith only [hprod]
    _ = (36 * Cns ^ (2 : ℝ)⁻¹ * C7 ^ (4 : ℝ)⁻¹) *
        Real.rpow base (cns / 2 + ct2 / 4) := by ring

end

end HCPolySupport.HighContrast.Quenched
