/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRawPrefactorCap

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastInitialLedgerCap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-- The two one-time source payments in the corrected cadence level schedule are
absorbed by two copies of the generation cap and the fixed source cap. -/
theorem corrected_cadence_initial_ledger_power_cap
    {ns cA : ℕ} {A alpha S0 S2 d0 beta : ℝ}
    {base Cns cns CX Ct1 Ct2u C7 ct2 : ℝ}
    (hbase : (3 : ℝ) ≤ base)
    (hA : 1 ≤ A) (hd0 : 0 < d0) (hd01 : d0 ≤ 1)
    (hbeta : 0 < beta) (hCns : 1 ≤ Cns)
    (hct2 : 0 ≤ ct2) (hCX : 1 ≤ CX) (hS2 : 1 ≤ S2)
    (hns : (3 : ℝ) ^ ns ≤ Cns * Real.rpow base cns)
    (hsource :
      S2 / (A * d0 ^ 2) ≤
        CX / d0 ^ 2 *
          (Real.rpow ((3 : ℝ) ^ ns) beta * Real.rpow base (beta * ct2)))
    (hCt1 : Ct1 = 3 / d0 ^ 2)
    (hCt2u : Ct2u = Real.rpow (CX / d0 ^ 2) beta⁻¹)
    (hC7 : C7 = Ct1 * 3 * Ct2u) :
    (3 : ℝ) ^
        ((linR ns cA A alpha 1 1 beta S0 1 S2 d0 0 : ℕ) : ℝ) ≤
      Cns ^ (2 : ℕ) * C7 * Real.rpow base (2 * cns + ct2) := by
  have hbase0 : (0 : ℝ) < base := by
    linarith only [hbase]
  have hbeta0 : (0 : ℝ) ≤ beta⁻¹ := inv_nonneg.mpr hbeta.le
  have hd0sq0 : (0 : ℝ) < d0 ^ 2 := sq_pos_of_pos hd0
  have hAd0sq0 : (0 : ℝ) < A * d0 ^ 2 :=
    mul_pos (by linarith only [hA]) hd0sq0
  have hCXdiv1 : (1 : ℝ) ≤ CX / d0 ^ 2 := by
    rw [le_div_iff₀ hd0sq0]
    have hd0sq1 : d0 ^ 2 ≤ 1 := by
      nlinarith only [hd0, hd01]
    nlinarith only [hCX, hd0sq1]
  have hCt2u1 : (1 : ℝ) ≤ Ct2u := by
    rw [hCt2u]
    exact Real.one_le_rpow hCXdiv1 hbeta0
  have hthreeNs1 : (1 : ℝ) ≤ (3 : ℝ) ^ ns :=
    one_le_pow₀ (by norm_num)
  have hbaseCt1 : (1 : ℝ) ≤ Real.rpow base ct2 :=
    Real.one_le_rpow (by linarith only [hbase]) hct2
  have hgenRoot1 : (1 : ℝ) ≤
      Ct2u * (3 : ℝ) ^ ns * Real.rpow base ct2 := by
    have hmul : (1 : ℝ) ≤ Ct2u * (3 : ℝ) ^ ns := by
      nlinarith only [hCt2u1, hthreeNs1]
    nlinarith only [hmul, hbaseCt1]
  set x1 : ℝ := 1 / (A * d0 ^ 2) with hx1
  have hx10 : (0 : ℝ) < x1 := by
    rw [hx1]
    positivity
  have hx1le : x1 ≤ 1 / d0 ^ 2 := by
    rw [hx1]
    have hden : d0 ^ 2 ≤ A * d0 ^ 2 := by
      nlinarith only [hA, hd0sq0]
    exact one_div_le_one_div_of_le hd0sq0 hden
  have hd0inv1 : (1 : ℝ) ≤ 1 / d0 ^ 2 := by
    rw [le_div_iff₀ hd0sq0]
    nlinarith only [hd0, hd01]
  have hceil1 := three_pow_ceil_logb_le hx10
  have hpay1 : (3 : ℝ) ^ ⌈Real.logb 3 x1⌉₊ ≤ Ct1 := by
    refine hceil1.trans ?_
    rw [hCt1]
    have hmax : max 1 x1 ≤ 1 / d0 ^ 2 := max_le hd0inv1 hx1le
    calc
      3 * max 1 x1 ≤ 3 * (1 / d0 ^ 2) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = 3 / d0 ^ 2 := by ring
  set x2 : ℝ := S2 / (A * d0 ^ 2) with hx2
  have hx20 : (0 : ℝ) < x2 := by
    rw [hx2]
    exact div_pos (by linarith only [hS2]) hAd0sq0
  set z : ℝ := x2 ^ beta⁻¹ with hz
  have hz0 : (0 : ℝ) < z := by
    rw [hz]
    exact Real.rpow_pos_of_pos hx20 _
  have hlogz : Real.logb 3 x2 / beta = Real.logb 3 z := by
    rw [hz]
    have hlog := Real.logb_rpow_eq_mul_logb_of_pos
      (b := (3 : ℝ)) (x := x2) (y := beta⁻¹) hx20
    calc
      Real.logb 3 x2 / beta = beta⁻¹ * Real.logb 3 x2 := by
        field_simp
      _ = Real.logb 3 (x2 ^ beta⁻¹) := hlog.symm
  have hx2nonneg : (0 : ℝ) ≤ x2 := hx20.le
  have hsource' : x2 ≤
      CX / d0 ^ 2 *
        (Real.rpow ((3 : ℝ) ^ ns) beta * Real.rpow base (beta * ct2)) := by
    rwa [hx2] at hsource
  have hsourceRpow := Real.rpow_le_rpow hx2nonneg hsource' hbeta0
  have hright0 : (0 : ℝ) ≤ CX / d0 ^ 2 := by
    linarith only [hCXdiv1]
  have hthreeNs0 : (0 : ℝ) ≤ (3 : ℝ) ^ ns := by positivity
  have hsourceRoot : z ≤
      Ct2u * (3 : ℝ) ^ ns * Real.rpow base ct2 := by
    rw [hz]
    refine hsourceRpow.trans (le_of_eq ?_)
    have hsplitOuter :
        (CX / d0 ^ 2 *
          (Real.rpow ((3 : ℝ) ^ ns) beta * Real.rpow base (beta * ct2))) ^
            beta⁻¹ =
        (CX / d0 ^ 2) ^ beta⁻¹ *
          (Real.rpow ((3 : ℝ) ^ ns) beta *
            Real.rpow base (beta * ct2)) ^ beta⁻¹ :=
      Real.mul_rpow hright0
        (mul_nonneg (Real.rpow_nonneg hthreeNs0 beta)
          (Real.rpow_nonneg hbase0.le (beta * ct2)))
    have hsplitInner :
        (Real.rpow ((3 : ℝ) ^ ns) beta * Real.rpow base (beta * ct2)) ^
            beta⁻¹ =
        (Real.rpow ((3 : ℝ) ^ ns) beta) ^ beta⁻¹ *
          (Real.rpow base (beta * ct2)) ^ beta⁻¹ :=
      Real.mul_rpow (Real.rpow_nonneg hthreeNs0 beta)
        (Real.rpow_nonneg hbase0.le (beta * ct2))
    have hthreeRoot : (Real.rpow ((3 : ℝ) ^ ns) beta) ^ beta⁻¹ =
        (3 : ℝ) ^ ns := by
      change (((3 : ℝ) ^ ns) ^ beta) ^ beta⁻¹ = (3 : ℝ) ^ ns
      exact Real.rpow_rpow_inv hthreeNs0 hbeta.ne'
    have hCXRoot : (CX / d0 ^ 2) ^ beta⁻¹ = Ct2u := by
      change Real.rpow (CX / d0 ^ 2) beta⁻¹ = Ct2u
      exact hCt2u.symm
    rw [hsplitOuter, hsplitInner, hthreeRoot, hCXRoot]
    have hbaseRoot : (Real.rpow base (beta * ct2)) ^ beta⁻¹ =
        Real.rpow base ct2 := by
      change (base ^ (beta * ct2)) ^ beta⁻¹ = base ^ ct2
      rw [← Real.rpow_mul hbase0.le]
      congr 1
      field_simp
    rw [hbaseRoot]
    ring
  have hceil2 := three_pow_ceil_logb_le hz0
  have hpay2 : (3 : ℝ) ^ ⌈Real.logb 3 x2 / beta⌉₊ ≤
      3 * Ct2u * (3 : ℝ) ^ ns * Real.rpow base ct2 := by
    rw [hlogz]
    refine hceil2.trans ?_
    have hmax : max 1 z ≤
        Ct2u * (3 : ℝ) ^ ns * Real.rpow base ct2 :=
      max_le hgenRoot1 hsourceRoot
    nlinarith only [hmax]
  have hCt10 : (0 : ℝ) ≤ Ct1 := le_trans (by norm_num) hpay1
  have hpay20 : (0 : ℝ) ≤
      3 * Ct2u * (3 : ℝ) ^ ns * Real.rpow base ct2 := by
    positivity
  have hstart : (3 : ℝ) ^
      ((linR ns cA A alpha 1 1 beta S0 1 S2 d0 0 : ℕ) : ℝ) ≤
      ((Cns * Real.rpow base cns) * Ct1) *
        (3 * Ct2u * (Cns * Real.rpow base cns) * Real.rpow base ct2) := by
    rw [linR_zero, Real.rpow_natCast, pow_add, pow_add]
    have hns0 : (0 : ℝ) ≤ (3 : ℝ) ^ ns := by positivity
    have hgen0 : (0 : ℝ) ≤ Cns * Real.rpow base cns :=
      mul_nonneg (by linarith only [hCns]) (Real.rpow_nonneg hbase0.le cns)
    have hleft := mul_le_mul hns hpay1 (by positivity) hgen0
    have hleft0 : (0 : ℝ) ≤ (3 : ℝ) ^ ns *
        (3 : ℝ) ^ ⌈Real.logb 3 (1 / (A * d0 ^ 2)) / 1⌉₊ := by
      positivity
    have hright0' : (0 : ℝ) ≤
        (Cns * Real.rpow base cns) * Ct1 := by
      exact le_trans hleft0 (by
        simpa only [div_one, hx1] using hleft)
    have hpay2' : (3 : ℝ) ^
        ⌈Real.logb 3 (S2 / (A * d0 ^ 2)) / beta⌉₊ ≤
          3 * Ct2u * (Cns * Real.rpow base cns) * Real.rpow base ct2 := by
      have hmul := mul_le_mul_of_nonneg_left hns
        (by positivity : (0 : ℝ) ≤ 3 * Ct2u)
      have hmul' := mul_le_mul_of_nonneg_right hmul
        (Real.rpow_nonneg hbase0.le ct2)
      have hpay2x : (3 : ℝ) ^
          ⌈Real.logb 3 (S2 / (A * d0 ^ 2)) / beta⌉₊ ≤
            3 * Ct2u * (3 : ℝ) ^ ns * Real.rpow base ct2 := by
        simpa only [hx2] using hpay2
      exact hpay2x.trans hmul'
    exact mul_le_mul (by simpa only [div_one, hx1] using hleft)
      hpay2' (by positivity) hright0'
  refine hstart.trans (le_of_eq ?_)
  rw [hC7, pow_two]
  calc
    Cns * Real.rpow base cns * Ct1 *
          (3 * Ct2u * (Cns * Real.rpow base cns) * Real.rpow base ct2) =
        Cns * Cns * (Ct1 * 3 * Ct2u) *
          (Real.rpow base cns * Real.rpow base cns * Real.rpow base ct2) := by
            ring
    _ = Cns * Cns * (Ct1 * 3 * Ct2u) *
        Real.rpow base (2 * cns + ct2) := by
      have hcc : Real.rpow base (cns + cns) =
          Real.rpow base cns * Real.rpow base cns :=
        Real.rpow_add hbase0 cns cns
      have hcct : Real.rpow base (cns + cns + ct2) =
          Real.rpow base (cns + cns) * Real.rpow base ct2 :=
        Real.rpow_add hbase0 (cns + cns) ct2
      rw [← hcc, ← hcct]
      congr 2
      ring

end

end HCPolySupport.HighContrast.Quenched
