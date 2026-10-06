/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryRate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The entry estimate at a common rate

The three legs of `SmallContrastEntryRateParts` are put on one decay rate and
assembled into the `hentry` hypothesis of
`hrec_line_of_slots_isotropy_sharp_at_jb_at_level_src`, consumed through the
rate-form entry exponent.

**The constant.**  `weakSourceGroupSummed` is linear with nonnegative
coefficients in its three source slots, so the source group evaluated at the
three legs' constants *is* the entry constant:

  `C_src = entrySourceConstant M L g C_v C_m C_b`,

and the entry estimate runs at `C_src ^ 2` because the rate-form entry exponent
consumes the square.

**The rate bookkeeping.**  Each leg decays at rate `beta` in a common decay
index `N`, so the square decays at `2·beta`.  The rate-form entry exponent asks for
`3^{-(N₁ + 2·beta·n)}`, so the caller must supply
`N₁ + 2·beta·n ≤ 2·beta·N`.  With `N = n_s + n` this is
`N₁ ≤ 2·beta·n_s`: the delayed start must exceed the entry delay *inflated by*
`1/(2·beta)`, not the entry delay itself.  The delayed-start shift is that step.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-! ## The source group scales -/

/-- **The source group scales with its three slots.**  It is linear with
nonnegative coefficients in `vsum`, `vmsrc`, `bsrc`. -/
theorem weakSourceGroupSummed_le_scaled {M L rho vsum vmsrc bsrc Cv Cm Cb w : ℝ}
    (hM0 : 0 ≤ M) (hrho1 : rho < 1) (hv : vsum ≤ Cv * w)
    (hm : vmsrc ≤ Cm * w) (hb : bsrc ≤ Cb * w) :
    weakSourceGroupSummed M L rho vsum vmsrc bsrc ≤
      weakSourceGroupSummed M L rho Cv Cm Cb * w := by
  have ha1 : (0 : ℝ) ≤ 16 * M * Real.sqrt L :=
    mul_nonneg (by linarith only [hM0]) (Real.sqrt_nonneg _)
  have ha2 : (0 : ℝ) ≤ Response.constantSeminormCoefficient * M * Real.sqrt 7 :=
    mul_nonneg (mul_nonneg constantSeminormCoefficient_nonneg hM0)
      (Real.sqrt_nonneg _)
  have ha3 : (0 : ℝ) ≤ 16 * M / (2 * ((1 - rho) / 2)) := by
    have hden : (0 : ℝ) < 2 * ((1 - rho) / 2) := by linarith only [hrho1]
    exact div_nonneg (by linarith only [hM0]) hden.le
  have h1 := mul_le_mul_of_nonneg_left hv ha1
  have h2 := mul_le_mul_of_nonneg_left hm ha2
  have h3 := mul_le_mul_of_nonneg_left hb ha3
  rw [weakSourceGroupSummed, weakSourceGroupSummed]
  nlinarith only [h1, h2, h3]

/-! ## The entry constant and the squared estimate -/

/-! ## The `hentry` producer -/

/-! ## The two established legs at the common rate -/

theorem vsumSourceConstant_nonneg {d : ℕ} {Csub Msc delta : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta) :
    0 ≤ vsumSourceConstant d Csub Msc delta := by
  have hs := Real.sqrt_nonneg (2 * (d : ℝ))
  have hgeom0 : (0 : ℝ) ≤ halfGeom := le_trans zero_le_one halfGeom_one_le
  have hc3 : (0 : ℝ) ≤ deepSlotConstant d Csub Msc delta := by
    rw [deepSlotConstant]
    exact add_nonneg (slotSourceValue_nonneg d hCsub hMsc 0)
      (mul_nonneg (slotBaseCoefficient_nonneg d) hdelta)
  have hc1 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 18 * Csub * Msc := by positivity
  have hc2 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 288 := by positivity
  rw [vsumSourceConstant]
  nlinarith only [hgeom0, hc1, hc2, hc3, hs]

/-- **The variance leg at the common rate.**  `beta·N ≤ J/2` is the rate
condition: at `J ≈ n/4` and `beta = recursionAlpha g ≤ 1/8` it is `N ≤ n`. -/
theorem vsum_leg_le {d : ℕ} (hd : 2 ≤ d) {Csub Msc delta : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta)
    {beta : ℝ} {J N : ℕ} (hrate : beta * (N : ℝ) ≤ (1 / 2 : ℝ) * (J : ℝ)) :
    slotVsumSharp d Csub Msc delta J ≤
      vsumSourceConstant d Csub Msc delta * (3 : ℝ) ^ (-beta * (N : ℝ)) := by
  have h1 : slotVsumSharp d Csub Msc delta J ≤
      vsumSourceConstant d Csub Msc delta * halfRatio ^ J :=
    slotVsumSharp_le hd hCsub hMsc J
  have h2 : halfRatio ^ J ≤ (3 : ℝ) ^ (-beta * (N : ℝ)) := by
    have h := halfRatio_pow_le (r := beta * (N : ℝ)) (J := J) hrate
    rwa [neg_mul]
  have h0 : (0 : ℝ) ≤ vsumSourceConstant d Csub Msc delta :=
    vsumSourceConstant_nonneg hCsub hMsc hdelta
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 h0)

end

end HCPolySupport.HighContrast.Quenched
