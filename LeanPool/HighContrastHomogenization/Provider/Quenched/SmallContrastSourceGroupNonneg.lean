/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotAlgebra

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSourceGroupNonneg

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The source group is nonnegative at nonnegative legs

Two sign facts the entry-slot clause consumes and that no earlier module needed:
the sharp summed source constant is nonnegative, and so is the summed source
group at nonnegative legs.  Both are immediate from the shapes of their own
definitions; they are recorded here so the entry-slot clause discharges them
rather than carrying them.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-- The sharp summed source constant is nonnegative. -/
theorem slotVsumSharp_nonneg (d : ℕ) {Csub Msc delta : ℝ} (hCsub : 0 ≤ Csub)
    (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta) (J : ℕ) :
    0 ≤ slotVsumSharp d Csub Msc delta J := by
  have hg : 0 < halfGeom := halfGeom_pos
  have hr : (0 : ℝ) ≤ halfRatio ^ J := pow_nonneg halfRatio_pos.le J
  have hdeep : 0 ≤ deepSlotConstant d Csub Msc delta := by
    rw [deepSlotConstant]
    exact add_nonneg (slotSourceValue_nonneg d hCsub hMsc 0)
      (mul_nonneg (slotBaseCoefficient_nonneg d) hdelta)
  have hs : 0 ≤ slotSourceSeq d Csub Msc delta J 0 :=
    slotSourceSeq_nonneg d hCsub hMsc hdelta J 0
  have h1 : (0 : ℝ) ≤ Real.sqrt (2 * (d : ℝ)) * 18 * Csub * Msc := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  have h2 : (0 : ℝ) ≤ Real.sqrt (2 * (d : ℝ)) * 288 := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  have hin : (0 : ℝ) ≤
      Real.sqrt (2 * (d : ℝ)) * 18 * Csub * Msc + Real.sqrt (2 * (d : ℝ)) * 288 +
        deepSlotConstant d Csub Msc delta := by
    linarith only [h1, h2, hdeep]
  rw [slotVsumSharp]
  exact add_nonneg (mul_nonneg (mul_nonneg hg.le hin) hr) (mul_nonneg hg.le hs)

/-- The summed source group is nonnegative at nonnegative legs. -/
theorem weakSourceGroupSummed_nonneg {M L rho vsum vmsrc bsrc : ℝ}
    (hM : 0 ≤ M) (hrho1 : rho < 1) (hvsum : 0 ≤ vsum) (hvmsrc : 0 ≤ vmsrc)
    (hbsrc : 0 ≤ bsrc) :
    0 ≤ weakSourceGroupSummed M L rho vsum vmsrc bsrc := by
  have hsem : (0 : ℝ) ≤ Response.constantSeminormCoefficient := by
    rw [Response.constantSeminormCoefficient_eq]
    have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 2) := by linarith only [hlt]
    positivity
  have hden : (0 : ℝ) < 2 * ((1 - rho) / 2) := by linarith only [hrho1]
  have h1 : (0 : ℝ) ≤ 16 * M * Real.sqrt L * vsum :=
    mul_nonneg (mul_nonneg (by linarith only [hM]) (Real.sqrt_nonneg _)) hvsum
  have h2 : (0 : ℝ) ≤ Response.constantSeminormCoefficient * M * Real.sqrt 7 * vmsrc :=
    mul_nonneg (mul_nonneg (mul_nonneg hsem hM) (Real.sqrt_nonneg _)) hvmsrc
  have h3 : (0 : ℝ) ≤ 16 * M / (2 * ((1 - rho) / 2)) * bsrc :=
    mul_nonneg (div_nonneg (by linarith only [hM]) hden.le) hbsrc
  rw [weakSourceGroupSummed]
  linarith only [h1, h2, h3]

end

end HCPolySupport.HighContrast.Quenched
