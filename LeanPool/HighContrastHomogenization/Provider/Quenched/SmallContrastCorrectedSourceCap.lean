/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedGenerationCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceGroupNonneg

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedSourceCap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The normalized corrected source cap

The released bad-source constant has polynomial degree eight in the growth
bar.  Squaring it gives the degree-sixteen payment recorded in `ct2`; this
file packages that calculation in the exact normalized form consumed by the
initial cadence level schedule.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-- The released bad-source scalar grows at most like the eighth power of the
source growth bar. -/
theorem badSourceConstant_le_three_mul_growthBar_pow_eight (K : ℝ) :
    badSourceConstant K ≤ 3 * growthBar K ^ (8 : ℕ) := by
  have hbar2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hbar0 : (0 : ℝ) ≤ growthBar K := by linarith only [hbar2]
  have hbar1 : (1 : ℝ) ≤ growthBar K := by linarith only [hbar2]
  have hT6 : IndependentSums.natTriangular 6 + 1 = 16 := by decide
  have hS0 : (0 : ℝ) ≤ sourceMomentSix K := sourceMomentSix_nonneg K
  have hS := sourceMomentSix_le K
  rw [hT6] at hS
  set y : ℝ := sourceMomentSix K / 16 with hy
  have hy0 : (0 : ℝ) ≤ y := by rw [hy]; positivity
  have hyBar : y ≤ growthBar K ^ (16 : ℕ) := by
    rw [hy]
    have hdiv : sourceMomentSix K / 16 ≤
        (13 / 16 : ℝ) * growthBar K ^ (16 : ℕ) := by
      nlinarith only [hS]
    have hpow0 : (0 : ℝ) ≤ growthBar K ^ (16 : ℕ) := by positivity
    nlinarith only [hdiv, hpow0]
  set z : ℝ := Real.rpow y (4 : ℝ)⁻¹ with hz
  have hz0 : (0 : ℝ) ≤ z := by
    rw [hz]
    exact Real.rpow_nonneg hy0 _
  have hzBar : z ≤ growthBar K ^ (4 : ℕ) := by
    rw [hz]
    have hmono := Real.rpow_le_rpow hy0 hyBar (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
    refine hmono.trans (le_of_eq ?_)
    calc
      Real.rpow (growthBar K ^ (16 : ℕ)) (4 : ℝ)⁻¹ =
          Real.rpow (Real.rpow (growthBar K) (16 : ℝ)) (4 : ℝ)⁻¹ := by
        exact congrArg (fun x : ℝ => Real.rpow x (4 : ℝ)⁻¹)
          (Real.rpow_natCast (growthBar K) 16).symm
      _ = Real.rpow (growthBar K) ((16 : ℝ) * (4 : ℝ)⁻¹) := by
        exact (Real.rpow_mul hbar0 (16 : ℝ) (4 : ℝ)⁻¹).symm
      _ = Real.rpow (growthBar K) (4 : ℝ) := by norm_num
      _ = growthBar K ^ (4 : ℕ) := Real.rpow_natCast _ 4
  have hzSq : z ^ (2 : ℕ) ≤ growthBar K ^ (8 : ℕ) := by
    have hpow := pow_le_pow_left₀ hz0 hzBar 2
    calc
      z ^ (2 : ℕ) ≤ (growthBar K ^ (4 : ℕ)) ^ (2 : ℕ) := hpow
      _ = growthBar K ^ (8 : ℕ) := by rw [← pow_mul]
  have hbar4le8 : growthBar K ^ (4 : ℕ) ≤ growthBar K ^ (8 : ℕ) :=
    pow_le_pow_right₀ hbar1 (by norm_num)
  rw [badSourceConstant]
  change 2 * z ^ (2 : ℕ) + z ≤ 3 * growthBar K ^ (8 : ℕ)
  nlinarith only [hzSq, hzBar, hbar4le8]

/-- The released bad-source constant at the endpoint is absorbed by a fixed
coefficient, that module, and `base^(8*cW)`. -/
theorem badSourceLegConstantAtLevel_le_corrected_source_scale
    {L K R base cW : ℝ} (hR : 1 ≤ R) (hbase : 3 ≤ base)
    (hcW : 0 ≤ cW)
    (hgrowth : growthBar K ≤ 2 * Real.rpow base cW) :
    badSourceLegConstantAtLevel L K R ≤
      (Real.sqrt 2 * Real.sqrt (L + 1) * R * 6) * 256 *
        Real.rpow base (8 * cW) := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hp0 : (0 : ℝ) ≤ Real.rpow base cW :=
    Real.rpow_nonneg hbase0.le cW
  have hp1 : (1 : ℝ) ≤ Real.rpow base cW :=
    Real.one_le_rpow (by linarith only [hbase]) hcW
  have hbar0 : (0 : ℝ) ≤ growthBar K := by
    linarith only [show (2 : ℝ) ≤ growthBar K from le_max_left _ _]
  have hpow := pow_le_pow_left₀ hbar0 hgrowth 8
  have hp8 : Real.rpow base cW ^ (8 : ℕ) =
      Real.rpow base (8 * cW) := by
    calc
      Real.rpow base cW ^ (8 : ℕ) =
          Real.rpow (Real.rpow base cW) (8 : ℝ) :=
        (Real.rpow_natCast (Real.rpow base cW) 8).symm
      _ = Real.rpow base (cW * 8) := by
        change (base ^ cW) ^ (8 : ℝ) = base ^ (cW * 8)
        rw [← Real.rpow_mul hbase0.le]
      _ = Real.rpow base (8 * cW) := by congr 1; ring
  have hbad : badSourceConstant K ≤
      768 * Real.rpow base (8 * cW) := by
    have hraw := badSourceConstant_le_three_mul_growthBar_pow_eight K
    rw [← hp8]
    nlinarith only [hraw, hpow]
  have hbad0 : (0 : ℝ) ≤ badSourceConstant K := badSourceConstant_nonneg K
  have hp80 : (0 : ℝ) ≤ Real.rpow base (8 * cW) :=
    Real.rpow_nonneg hbase0.le _
  have hp81 : (1 : ℝ) ≤ Real.rpow base (8 * cW) :=
    Real.one_le_rpow (by linarith only [hbase]) (by linarith only [hcW])
  have hR0 : (0 : ℝ) ≤ R := by linarith only [hR]
  have hinside : R * badSourceConstant K + 1 ≤
      R * (6 * 256 * Real.rpow base (8 * cW)) := by
    calc
      R * badSourceConstant K + 1 ≤ R * badSourceConstant K + R :=
        by linarith only [hR]
      _ = R * (badSourceConstant K + 1) := by ring
      _ ≤ R * (768 * Real.rpow base (8 * cW) + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hbad le_rfl) hR0
      _ ≤ R * (6 * 256 * Real.rpow base (8 * cW)) := by
        refine mul_le_mul_of_nonneg_left ?_ hR0
        nlinarith only [hp81]
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (L + 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [badSourceLegConstantAtLevel]
  calc
    Real.sqrt 2 * Real.sqrt (L + 1) * (R * badSourceConstant K) +
        Real.sqrt 2 * Real.sqrt (L + 1) =
        (Real.sqrt 2 * Real.sqrt (L + 1)) *
          (R * badSourceConstant K + 1) := by ring
    _ ≤ (Real.sqrt 2 * Real.sqrt (L + 1)) *
        (R * (6 * 256 * Real.rpow base (8 * cW))) :=
      mul_le_mul_of_nonneg_left hinside hsqrt0
    _ = (Real.sqrt 2 * Real.sqrt (L + 1) * R * 6) * 256 *
        Real.rpow base (8 * cW) := by ring

/-- The fixed source coefficient has the normalized cap required by the
initial corrected cadence level schedule. -/
theorem corrected_normalized_source_cap
    {d ns : ℕ} {A delta beta base cW Cpre M L rho K R CX S2 ct2 : ℝ}
    (hA : 1 ≤ A) (hdelta : 0 < delta) (hbeta : 0 < beta)
    (hbase : 3 ≤ base) (hcW : 0 ≤ cW) (hCpre : 1 ≤ Cpre)
    (hM : 0 ≤ M) (hrho : rho < 1) (hR : 1 ≤ R)
    (hgrowth : growthBar K ≤ 2 * Real.rpow base cW)
    (hCX : CX = 1 +
      (6 * weakCoefficient d Cpre *
        ((16 * M / (1 - rho)) *
          (Real.sqrt 2 * Real.sqrt (L + 1) * R * 6)) ^ (2 : ℕ)) * 65536)
    (hS2 : S2 = 1 + 6 * weakCoefficient d Cpre *
      weakSourceGroupSummed M L rho 0 0 (badSourceLegConstantAtLevel L K R) ^ (2 : ℕ) *
        Real.rpow (3 : ℝ) (beta * (ns : ℝ)))
    (hct2 : ct2 = 16 * cW / beta) :
    S2 / (A * delta ^ (2 : ℕ)) ≤
      CX / delta ^ (2 : ℕ) *
        (Real.rpow ((3 : ℝ) ^ ns) beta *
          Real.rpow base (beta * ct2)) := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hden : (0 : ℝ) < 1 - rho := by linarith only [hrho]
  have hw : (0 : ℝ) ≤ weakCoefficient d Cpre :=
    weakCoefficient_nonneg d (by linarith only [hCpre])
  have hcoef0 : (0 : ℝ) ≤ 16 * M / (1 - rho) := by positivity
  have hbsrc0 : (0 : ℝ) ≤ badSourceLegConstantAtLevel L K R := by
    rw [badSourceLegConstantAtLevel]
    have hbad0 : (0 : ℝ) ≤ badSourceConstant K := badSourceConstant_nonneg K
    positivity
  have hgroup0 : (0 : ℝ) ≤
      weakSourceGroupSummed M L rho 0 0 (badSourceLegConstantAtLevel L K R) := by
    exact weakSourceGroupSummed_nonneg hM hrho (by norm_num) (by norm_num) hbsrc0
  have hbsrc := badSourceLegConstantAtLevel_le_corrected_source_scale
    (L := L) (K := K) (R := R) (base := base) (cW := cW)
    hR hbase hcW hgrowth
  set X : ℝ := (16 * M / (1 - rho)) *
    (Real.sqrt 2 * Real.sqrt (L + 1) * R * 6) with hX
  have hX0 : (0 : ℝ) ≤ X := by
    rw [hX]
    positivity
  have hgroup : weakSourceGroupSummed M L rho 0 0
      (badSourceLegConstantAtLevel L K R) ≤
      X * 256 * Real.rpow base (8 * cW) := by
    rw [weakSourceGroupSummed]
    have hden' : 2 * ((1 - rho) / 2) = 1 - rho := by ring
    rw [hden']
    simp only [mul_zero, add_zero]
    rw [hX]
    have hstep := mul_le_mul_of_nonneg_left hbsrc hcoef0
    nlinarith only [hstep]
  have hgroupSq := pow_le_pow_left₀ hgroup0 hgroup 2
  have hp16 : Real.rpow base (8 * cW) ^ (2 : ℕ) =
      Real.rpow base (16 * cW) := by
    calc
      Real.rpow base (8 * cW) ^ (2 : ℕ) =
          Real.rpow (Real.rpow base (8 * cW)) (2 : ℝ) :=
        (Real.rpow_natCast (Real.rpow base (8 * cW)) 2).symm
      _ = Real.rpow base ((8 * cW) * 2) := by
        change (base ^ (8 * cW)) ^ (2 : ℝ) = base ^ ((8 * cW) * 2)
        rw [← Real.rpow_mul hbase0.le]
      _ = Real.rpow base (16 * cW) := by congr 1; ring
  have hgroupSqCap :
      weakSourceGroupSummed M L rho 0 0 (badSourceLegConstantAtLevel L K R) ^ (2 : ℕ) ≤
        X ^ (2 : ℕ) * 65536 * Real.rpow base (16 * cW) := by
    calc
      weakSourceGroupSummed M L rho 0 0
          (badSourceLegConstantAtLevel L K R) ^ (2 : ℕ) ≤
          (X * 256 * Real.rpow base (8 * cW)) ^ (2 : ℕ) := hgroupSq
      _ = X ^ (2 : ℕ) * 65536 *
          Real.rpow base (8 * cW) ^ (2 : ℕ) := by ring
      _ = X ^ (2 : ℕ) * 65536 * Real.rpow base (16 * cW) := by
        rw [hp16]
  have hthree0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (beta * (ns : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hthree1 : (1 : ℝ) ≤ Real.rpow (3 : ℝ) (beta * (ns : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hbeta.le (Nat.cast_nonneg _))
  have hbase16zero : (0 : ℝ) ≤ Real.rpow base (16 * cW) :=
    Real.rpow_nonneg hbase0.le _
  have hbase16one : (1 : ℝ) ≤ Real.rpow base (16 * cW) :=
    Real.one_le_rpow (by linarith only [hbase]) (by linarith only [hcW])
  have hsixw0 : (0 : ℝ) ≤ 6 * weakCoefficient d Cpre :=
    mul_nonneg (by norm_num) hw
  have hpay :
      (6 * weakCoefficient d Cpre) *
          weakSourceGroupSummed M L rho 0 0
            (badSourceLegConstantAtLevel L K R) ^ (2 : ℕ) ≤
        (6 * weakCoefficient d Cpre) *
          (X ^ (2 : ℕ) * 65536 * Real.rpow base (16 * cW)) :=
    mul_le_mul_of_nonneg_left hgroupSqCap hsixw0
  have hpay' := mul_le_mul_of_nonneg_right hpay hthree0
  have hprod1 : (1 : ℝ) ≤
      Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
        Real.rpow base (16 * cW) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
          Real.rpow base (16 * cW) :=
        mul_le_mul hthree1 hbase16one zero_le_one (by linarith only [hthree1])
  have hS2cap : S2 ≤ CX * Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
      Real.rpow base (16 * cW) := by
    rw [hS2, hCX]
    calc
      1 + 6 * weakCoefficient d Cpre *
          weakSourceGroupSummed M L rho 0 0
            (badSourceLegConstantAtLevel L K R) ^ (2 : ℕ) *
            Real.rpow (3 : ℝ) (beta * (ns : ℝ)) ≤
          1 + (6 * weakCoefficient d Cpre *
            (X ^ (2 : ℕ) * 65536 * Real.rpow base (16 * cW))) *
              Real.rpow (3 : ℝ) (beta * (ns : ℝ)) :=
        add_le_add le_rfl hpay'
      _ ≤ Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
          Real.rpow base (16 * cW) +
          (6 * weakCoefficient d Cpre * X ^ (2 : ℕ) * 65536) *
            Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
              Real.rpow base (16 * cW) := by
        nlinarith only [hprod1]
      _ = (1 + (6 * weakCoefficient d Cpre * X ^ (2 : ℕ)) * 65536) *
          Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
            Real.rpow base (16 * cW) := by ring
  have hS20 : (0 : ℝ) ≤ S2 := by
    rw [hS2]
    exact le_trans zero_le_one
      (one_le_corrected_source_coefficient (d := d) (Cpre := Cpre)
        (X := weakSourceGroupSummed M L rho 0 0 (badSourceLegConstantAtLevel L K R))
        (t := beta * (ns : ℝ)) hCpre)
  have hd2 : (0 : ℝ) < delta ^ (2 : ℕ) := sq_pos_of_pos hdelta
  have hA0 : (0 : ℝ) < A := by linarith only [hA]
  have hdenA : delta ^ (2 : ℕ) ≤ A * delta ^ (2 : ℕ) := by
    nlinarith only [hA, hd2]
  have hinv : (A * delta ^ (2 : ℕ))⁻¹ ≤ (delta ^ (2 : ℕ))⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le hd2 hdenA
  have hfirst : S2 / (A * delta ^ (2 : ℕ)) ≤ S2 / delta ^ (2 : ℕ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hS20
  have hsecond : S2 / delta ^ (2 : ℕ) ≤
      (CX * Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
        Real.rpow base (16 * cW)) / delta ^ (2 : ℕ) := by
    exact div_le_div_of_nonneg_right hS2cap hd2.le
  have hthree : Real.rpow ((3 : ℝ) ^ ns) beta =
      Real.rpow (3 : ℝ) (beta * (ns : ℝ)) := by
    calc
      Real.rpow ((3 : ℝ) ^ ns) beta =
          Real.rpow (Real.rpow (3 : ℝ) (ns : ℝ)) beta := by
        exact congrArg (fun x : ℝ => Real.rpow x beta)
          (Real.rpow_natCast (3 : ℝ) ns).symm
      _ = Real.rpow (3 : ℝ) ((ns : ℝ) * beta) := by
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
          (ns : ℝ) beta).symm
      _ = Real.rpow (3 : ℝ) (beta * (ns : ℝ)) := by congr 1; ring
  have hbasePay : Real.rpow base (beta * ct2) =
      Real.rpow base (16 * cW) := by
    rw [hct2]
    congr 1
    field_simp
  calc
    S2 / (A * delta ^ (2 : ℕ)) ≤ S2 / delta ^ (2 : ℕ) := hfirst
    _ ≤ (CX * Real.rpow (3 : ℝ) (beta * (ns : ℝ)) *
          Real.rpow base (16 * cW)) / delta ^ (2 : ℕ) := hsecond
    _ = CX / delta ^ (2 : ℕ) *
        (Real.rpow ((3 : ℝ) ^ ns) beta * Real.rpow base (beta * ct2)) := by
      rw [hthree, hbasePay]
      field_simp

end

end HCPolySupport.HighContrast.Quenched
