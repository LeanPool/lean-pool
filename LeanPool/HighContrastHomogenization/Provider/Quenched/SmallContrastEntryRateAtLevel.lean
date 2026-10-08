/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBadLevelResidue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRate

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryRateAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bad-event leg at the matched threshold

The source group's bad leg with the residue-free majorant in place of the
pinned one.  The rate is unchanged — the printed half rate in the
absolute-generation gap — and the only cost of the matched threshold is the
single factor `R` in front of a constant the source slot already permits to
carry the grid's aspect ratio.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

/-- The bad-event leg's assembled constant at the matched threshold. -/
@[expose]
def badSourceLegConstantAtLevel (L K R : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sqrt (L + 1) * (R * badSourceConstant K) +
    Real.sqrt 2 * Real.sqrt (L + 1)

/-- **The bad-event leg at the common rate, at the matched threshold.** -/
theorem bad_source_leg_at_level_le {L K R : ℝ} (hR : 1 ≤ R) {Delta : ℤ}
    (hD : 0 ≤ Delta) {g : ℝ} {Hw : ℕ}
    {beta : ℝ} {N : ℕ}
    (hDrate : beta * (N : ℝ) ≤ (1 / 2 : ℝ) * (Delta : ℝ))
    (hHrate : beta * (N : ℝ) ≤ contrastAlpha g * (Hw : ℝ)) :
    Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 * (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) *
          Real.sqrt (L + 1) ≤
      badSourceLegConstantAtLevel L K R * (3 : ℝ) ^ (-beta * (N : ℝ)) := by
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsL : (0 : ℝ) ≤ Real.sqrt (L + 1) := Real.sqrt_nonneg _
  have hfac : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (L + 1) := mul_nonneg hs2 hsL
  have hbad := profileBadMajorantAt_badMoment_le K hR hD
  have hb0 : (0 : ℝ) ≤ R * badSourceConstant K :=
    mul_nonneg (by linarith only [hR]) (badSourceConstant_nonneg K)
  have hpow : (3 : ℝ) ^ (-(1 / 2 : ℝ) * (Delta : ℝ)) ≤
      (3 : ℝ) ^ (-beta * (N : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith only [hDrate]
  have htail : (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) ≤
      (3 : ℝ) ^ (-beta * (N : ℝ)) := by
    rw [one_sub_contrastRho_half_eq]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith only [hHrate]
  have hone : Real.sqrt 2 * Real.sqrt (L + 1) *
      Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R ≤
      Real.sqrt 2 * Real.sqrt (L + 1) *
        (R * badSourceConstant K * (3 : ℝ) ^ (-beta * (N : ℝ))) := by
    refine mul_le_mul_of_nonneg_left (le_trans hbad ?_) hfac
    exact mul_le_mul_of_nonneg_left hpow hb0
  have htwo : Real.sqrt 2 * (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) *
      Real.sqrt (L + 1) ≤
      Real.sqrt 2 * Real.sqrt (L + 1) * (3 : ℝ) ^ (-beta * (N : ℝ)) := by
    have := mul_le_mul_of_nonneg_left htail hfac
    calc
      Real.sqrt 2 * (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) *
          Real.sqrt (L + 1) =
          (Real.sqrt 2 * Real.sqrt (L + 1)) *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) := by ring
      _ ≤ (Real.sqrt 2 * Real.sqrt (L + 1)) *
          (3 : ℝ) ^ (-beta * (N : ℝ)) := this
  rw [badSourceLegConstantAtLevel]
  calc
    _ ≤ Real.sqrt 2 * Real.sqrt (L + 1) *
          (R * badSourceConstant K * (3 : ℝ) ^ (-beta * (N : ℝ))) +
        Real.sqrt 2 * Real.sqrt (L + 1) *
          (3 : ℝ) ^ (-beta * (N : ℝ)) := add_le_add hone htwo
    _ = _ := by ring

end

end HCPolySupport.HighContrast.Quenched
