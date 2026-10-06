/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastInitialLedgerCap

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedConstantBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Lower bounds for the corrected cadence constants

These elementary bounds expose the normalization facts used by the corrected
cadence level schedule.  Their statements are written at the defining expressions of
the four constants, so the endpoint only rewrites its local `set` equations.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-- The coefficient multiplying the generation cap is at least one. -/
theorem one_le_corrected_generation_coefficient
    {H : ℕ} {C5 CF rate : ℝ}
    (hC5 : 1 ≤ C5) (hCF : 1 ≤ CF) (hrate : 0 < rate) :
    (1 : ℝ) ≤
      (3 : ℝ) ^ (H + 1) * 624 *
        (8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ)) *
        (3 * Real.rpow CF rate⁻¹) * 3 := by
  have hH : (1 : ℝ) ≤ (3 : ℝ) ^ (H + 1) :=
    one_le_pow₀ (by norm_num)
  have h3H : (1 : ℝ) ≤ (3 : ℝ) ^ (3 * H) :=
    one_le_pow₀ (by norm_num)
  have hC5pow : (1 : ℝ) ≤ C5 ^ (4 : ℕ) :=
    one_le_pow₀ hC5
  have hCE0 : (0 : ℝ) ≤ 8100 * (3 : ℝ) ^ (3 * H) := by
    positivity
  have hCE : (1 : ℝ) ≤
      8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ) := by
    have hleft : (1 : ℝ) ≤ 8100 * (3 : ℝ) ^ (3 * H) := by
      nlinarith only [h3H]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (8100 * (3 : ℝ) ^ (3 * H)) * C5 ^ (4 : ℕ) :=
        mul_le_mul hleft hC5pow zero_le_one hCE0
  have hCFinv : (0 : ℝ) ≤ rate⁻¹ := inv_nonneg.mpr hrate.le
  have hCFpow : (1 : ℝ) ≤ Real.rpow CF rate⁻¹ :=
    Real.one_le_rpow hCF hCFinv
  have hCFterm : (1 : ℝ) ≤ 3 * Real.rpow CF rate⁻¹ := by
    nlinarith only [hCFpow]
  have hfirst : (1 : ℝ) ≤ (3 : ℝ) ^ (H + 1) * 624 := by
    nlinarith only [hH]
  have hsecond : (1 : ℝ) ≤
      ((3 : ℝ) ^ (H + 1) * 624) *
        (8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ)) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((3 : ℝ) ^ (H + 1) * 624) *
          (8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ)) :=
        mul_le_mul hfirst hCE zero_le_one (by linarith only [hfirst])
  have hthird : (1 : ℝ) ≤
      (((3 : ℝ) ^ (H + 1) * 624) *
          (8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ))) *
        (3 * Real.rpow CF rate⁻¹) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (((3 : ℝ) ^ (H + 1) * 624) *
          (8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ))) *
          (3 * Real.rpow CF rate⁻¹) :=
        mul_le_mul hsecond hCFterm zero_le_one (by linarith only [hsecond])
  nlinarith only [hthird]

/-- The bad-source coefficient is one plus a nonnegative square term. -/
theorem one_le_corrected_bad_source_coefficient
    {d : ℕ} {Cpre X : ℝ} (hCpre : 1 ≤ Cpre) :
    (1 : ℝ) ≤
      1 + (6 * weakCoefficient d Cpre * X ^ (2 : ℕ)) * 65536 := by
  have hw : (0 : ℝ) ≤ weakCoefficient d Cpre :=
    weakCoefficient_nonneg d (by linarith only [hCpre])
  have hterm : (0 : ℝ) ≤
      (6 * weakCoefficient d Cpre * X ^ (2 : ℕ)) * 65536 := by
    positivity
  linarith only [hterm]

/-- The fixed source coefficient is one plus a nonnegative source payment. -/
theorem one_le_corrected_source_coefficient
    {d : ℕ} {Cpre X t : ℝ} (hCpre : 1 ≤ Cpre) :
    (1 : ℝ) ≤
      1 + 6 * weakCoefficient d Cpre * X ^ (2 : ℕ) *
        Real.rpow (3 : ℝ) t := by
  have hw : (0 : ℝ) ≤ weakCoefficient d Cpre :=
    weakCoefficient_nonneg d (by linarith only [hCpre])
  have hterm : (0 : ℝ) ≤
      6 * weakCoefficient d Cpre * X ^ (2 : ℕ) *
        Real.rpow (3 : ℝ) t := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hw) (sq_nonneg X))
      (Real.rpow_nonneg (by norm_num) t)
  linarith only [hterm]

/-- The coefficient paying the two source ceilings is at least one. -/
theorem one_le_corrected_ledger_coefficient
    {delta CX beta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hCX : 1 ≤ CX) (hbeta : 0 < beta) :
    (1 : ℝ) ≤
      (3 / delta ^ (2 : ℕ)) * 3 *
        Real.rpow (CX / delta ^ (2 : ℕ)) beta⁻¹ := by
  have hd2 : (0 : ℝ) < delta ^ (2 : ℕ) := sq_pos_of_pos hdelta
  have hd2one : delta ^ (2 : ℕ) ≤ 1 := by
    nlinarith only [hdelta, hdelta1]
  have hdiv : (1 : ℝ) ≤ CX / delta ^ (2 : ℕ) := by
    rw [le_div_iff₀ hd2]
    nlinarith only [hCX, hd2one]
  have hroot : (1 : ℝ) ≤
      Real.rpow (CX / delta ^ (2 : ℕ)) beta⁻¹ :=
    Real.one_le_rpow hdiv (inv_nonneg.mpr hbeta.le)
  have hfirst : (1 : ℝ) ≤ 3 / delta ^ (2 : ℕ) := by
    rw [le_div_iff₀ hd2]
    nlinarith only [hd2one]
  have hleft : (1 : ℝ) ≤ (3 / delta ^ (2 : ℕ)) * 3 := by
    nlinarith only [hfirst]
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ ((3 / delta ^ (2 : ℕ)) * 3) *
        Real.rpow (CX / delta ^ (2 : ℕ)) beta⁻¹ :=
      mul_le_mul hleft hroot zero_le_one (by linarith only [hleft])

end

end HCPolySupport.HighContrast.Quenched
