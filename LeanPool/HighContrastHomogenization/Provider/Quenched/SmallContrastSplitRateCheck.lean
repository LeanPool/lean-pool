/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLinearDecay
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotBoundsSplit
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSplitRateCheck

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrected rate at the split supply

The level schedule's conclusion rate `linRate` is antitone
in the recursion constant and in the lag-channel coefficient, and the
burn-split supply value is capped by a pre-law constant once
`κ_𝐄 ≤ 1 + 6σ`.  Together these certify that fixing the rate at the
pre-law caps only weakens the conclusion.  Dependence on `Π` and the aspect
ratio occurs only in scale thresholds, not in the rate.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-- The spacing constant is monotone in the recursion constant and the
lag coefficient. -/
theorem linCs_mono {A A' alpha b0 bA b2 : ℝ} {cA : ℕ} {S0 S0' : ℝ}
    (hA : 1 ≤ A) (hAA' : A ≤ A')
    (hb0 : 0 < b0) (hS0 : 1 ≤ S0) (hSS' : S0 ≤ S0') :
    linCs A alpha b0 bA b2 cA S0 ≤ linCs A' alpha b0 bA b2 cA S0' := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hA'0 : (0 : ℝ) < A' := lt_of_lt_of_le hA0 hAA'
  have hlogS : Real.logb 3 S0 ≤ Real.logb 3 S0' :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
      (lt_of_lt_of_le one_pos hS0) hSS'
  have hterm1 : Real.logb 3 S0 / b0 ≤ Real.logb 3 S0' / b0 := by
    have hb0' : (0 : ℝ) ≤ b0⁻¹ := inv_nonneg.mpr hb0.le
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hlogS hb0'
  have hratio' : (1 : ℝ) < (2 * A' + 1) / (2 * A') := by
    rw [lt_div_iff₀ (by positivity)]
    linarith only []
  have hlog'pos : 0 < Real.logb 3 ((2 * A' + 1) / (2 * A')) :=
    Real.logb_pos (by norm_num) hratio'
  have hratio_le : (2 * A' + 1) / (2 * A') ≤ (2 * A + 1) / (2 * A) := by
    have hsplitA : (2 * A + 1) / (2 * A) = 1 + 1 / (2 * A) := by
      field_simp
    have hsplitA' : (2 * A' + 1) / (2 * A') = 1 + 1 / (2 * A') := by
      field_simp
    rw [hsplitA, hsplitA']
    have hinv2 := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < 2 * A)
      (by linarith only [hAA'] : 2 * A ≤ 2 * A')
    linarith only [hinv2]
  have hlogle : Real.logb 3 ((2 * A' + 1) / (2 * A')) ≤
      Real.logb 3 ((2 * A + 1) / (2 * A)) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 3)
      (by positivity) hratio_le
  have hinv : 1 / Real.logb 3 ((2 * A + 1) / (2 * A)) ≤
      1 / Real.logb 3 ((2 * A' + 1) / (2 * A')) :=
    one_div_le_one_div_of_le hlog'pos hlogle
  have hterm3 : (1 / Real.logb 3 ((2 * A + 1) / (2 * A)) + 1) *
      ((cA : ℝ) + 1) ≤
      (1 / Real.logb 3 ((2 * A' + 1) / (2 * A')) + 1) * ((cA : ℝ) + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith only [hinv]
  rw [linCs, linCs]
  linarith only [hterm1, hterm3]

/-- The conclusion rate is antitone in the recursion constant and the
lag coefficient. -/
theorem linRate_anti {A A' alpha b0 bA b2 : ℝ} {cA : ℕ} {S0 S0' : ℝ}
    (hA : 1 ≤ A) (hAA' : A ≤ A') (halpha : 0 < alpha)
    (hb0 : 0 < b0) (hbA : 0 < bA) (hb2 : 0 < b2)
    (hS0 : 1 ≤ S0) (hSS' : S0 ≤ S0') :
    linRate A' alpha b0 bA b2 cA S0' ≤ linRate A alpha b0 bA b2 cA S0 := by
  have hCs1 : 1 ≤ linCs A alpha b0 bA b2 cA S0 :=
    linCs_one_le hA halpha hb0 hbA hb2 hS0
  have hCsmono : linCs A alpha b0 bA b2 cA S0 ≤
      linCs A' alpha b0 bA b2 cA S0' :=
    linCs_mono hA hAA' hb0 hS0 hSS'
  rw [linRate, linRate]
  refine one_div_le_one_div_of_le (by linarith only [hCs1]) ?_
  linarith only [hCsmono]

/-- The conclusion rate is positive. -/
theorem linRate_pos {A alpha b0 bA b2 : ℝ} {cA : ℕ} {S0 : ℝ}
    (hA : 1 ≤ A) (halpha : 0 < alpha)
    (hb0 : 0 < b0) (hbA : 0 < bA) (hb2 : 0 < b2) (hS0 : 1 ≤ S0) :
    0 < linRate A alpha b0 bA b2 cA S0 := by
  have hCs1 : 1 ≤ linCs A alpha b0 bA b2 cA S0 :=
    linCs_one_le hA halpha hb0 hbA hb2 hS0
  rw [linRate]
  positivity

/-- The split supply value is capped by the pre-law reference bound. -/
theorem supplyMscSplit_le {d : ℕ} {E : BlockMat d} {kapBar : ℝ}
    (hkap : kappaRef E ≤ kapBar) :
    supplyMscSplit d E ≤
      (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * (kapBar * 4) * (2 * (4 : ℝ)) *
        Real.sqrt 2 := by
  have hkap0 : 0 ≤ kappaRef E := Transport.zero_le_kappaRef E
  have h2d : (0 : ℝ) ≤ (2 * d : ℝ) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  rw [supplyMscSplit]
  have hstep : (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * (kappaRef E * 4) ≤
      (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * (kapBar * 4) := by
    refine mul_le_mul_of_nonneg_left ?_ h2d
    linarith only [hkap]
  have hstep2 := mul_le_mul_of_nonneg_right hstep
    (by norm_num : (0 : ℝ) ≤ 2 * (4 : ℝ))
  exact mul_le_mul_of_nonneg_right hstep2 hs2

/-- The variance-leg constant is monotone in the supply value. -/
theorem vsumSourceConstant_mono {d : ℕ} {Csub delta : ℝ}
    (hCsub : 0 ≤ Csub)
    {Msc Msc' : ℝ} (hMM' : Msc ≤ Msc') :
    vsumSourceConstant d Csub Msc delta ≤
      vsumSourceConstant d Csub Msc' delta := by
  have hgeom0 : (0 : ℝ) ≤ halfGeom :=
    le_trans zero_le_one halfGeom_one_le
  have hs : (0 : ℝ) ≤ Real.sqrt (2 * (d : ℝ)) := Real.sqrt_nonneg _
  have hsv : slotSourceValue d Csub Msc 0 ≤
      slotSourceValue d Csub Msc' 0 := by
    rw [slotSourceValue, slotSourceValue]
    refine mul_le_mul_of_nonneg_left ?_ hs
    have h1 : 18 * (Csub * ((3 ^ (d * 0) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc) ≤
        18 * (Csub * ((3 ^ (d * 0) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) * Msc') := by
      have hc : (0 : ℝ) ≤ Csub *
          ((3 ^ (d * 0) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) := by
        have : (0 : ℝ) ≤ ((3 ^ (d * 0) : ℕ) : ℝ) ^ (-(2 : ℝ)⁻¹) :=
          Real.rpow_nonneg (by positivity) _
        positivity
      nlinarith only [hMM', hc]
    linarith only [h1]
  have hdeep : deepSlotConstant d Csub Msc delta ≤
      deepSlotConstant d Csub Msc' delta := by
    rw [deepSlotConstant, deepSlotConstant]
    linarith only [hsv]
  rw [vsumSourceConstant, vsumSourceConstant]
  refine mul_le_mul_of_nonneg_left ?_ hgeom0
  have h2 : 2 * (Real.sqrt (2 * d) * 18 * Csub * Msc) ≤
      2 * (Real.sqrt (2 * d) * 18 * Csub * Msc') := by
    have hc : (0 : ℝ) ≤ Real.sqrt (2 * (d : ℝ)) * 18 * Csub := by
      positivity
    nlinarith only [hMM', hc]
  linarith only [h2, hdeep]

end

end HCPolySupport.HighContrast.Quenched
