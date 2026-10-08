/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotSum
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDropCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Tilt.AdaptedHatIntrinsic

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSmallnessPack

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The per-generation smallness pack and the drop slot

Two of the four analytic families of hypotheses of
`exists_account_one_step_entry_of_block_at_level` come from the bootstrap's single scalar
smallness `d(Θ̂_r − 1) ≤ δ` alone.  This file discharges them.

* **The contrast smallness** `6(Θ(E_t) − 1) ≤ 1`.  The
  hatted-to-intrinsic comparison
  (the hatted-polynomial contrast bound) gives
  `Θ − 1 ≤ (5/4)F + (1/4)F²` at `F = d(Θ̂ − 1)`, so `δ ≤ 1/9` suffices:
  `6((5/4)(1/9) + (1/4)(1/81)) = 46/54 < 1`.
* **The drop smallness** `d(Θ̂_j − Θ̂_p) ≤ 1` at every depth: the hatted
  contrast is `≥ 1`, so every drop is below the excess at its upper scale.

It also records the **drop slot** in recursion shape: `meanDrop2ValueIsotropy` — the
carrier `exists_account_one_step_entry_of_block_at_level` consumes in its `Dr` slot — is
literally `4·(F_{t-j} - F_t)·c_T`, i.e. the `c_D·(F(n-j) - F n)` shape of
`hrec_final_sharp_at_jb_src`, with `c_D = 4 c_T` and

  `c_T = 2·boundaryConst Cd g mAl·3^{g G}·blockSize 𝐄 (inflatedReference …)`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The hatted excess at an absolute scale. -/
@[expose]
def hatExcessAt (P : Measure (CoeffSpace d)) (q : Mat d) (r : ℤ) : ℝ :=
  (d : ℝ) * (adaptedHattedContrast P q r - 1)

theorem hatExcessAt_nonneg [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {r : ℤ}
    (hfin : HasFiniteAdaptedMean P q r) : 0 ≤ hatExcessAt P q r := by
  have h := one_le_adaptedHattedContrast_of_rounded hgrid hfin
  exact mul_nonneg (Nat.cast_nonneg d) (by linarith only [h])

/-- **The contrast smallness clause.**  `δ ≤ 1/9` on the hatted excess forces
`6(Θ(E_t) − 1) ≤ 1`. -/
theorem contrast_smallness_of_hatExcess [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {t : ℤ}
    (hfin : HasFiniteAdaptedMean P q t)
    {delta : ℝ} (hdelta : hatExcessAt P q t ≤ delta) (hdelta9 : delta ≤ 1 / 9) :
    6 * (blockContrast (adaptedMean P q t) - 1) ≤ 1 := by
  have hF0 : 0 ≤ hatExcessAt P q t := hatExcessAt_nonneg hgrid hfin
  have hpoly := adaptedContrast_sub_one_le_hatted_polynomial hgrid hfin
  have hFle : hatExcessAt P q t ≤ 1 / 9 := le_trans hdelta hdelta9
  have hrw : (5 / 4 : ℝ) * (d : ℝ) * (adaptedHattedContrast P q t - 1) +
      (1 / 4 : ℝ) * ((d : ℝ) * (adaptedHattedContrast P q t - 1)) ^ 2 =
      (5 / 4 : ℝ) * hatExcessAt P q t + (1 / 4 : ℝ) * hatExcessAt P q t ^ 2 := by
    rw [hatExcessAt]
    ring
  rw [hrw] at hpoly
  nlinarith only [hpoly, hF0, hFle]

/-- **The drop smallness clause.**  Every hatted drop is below the excess at
its upper scale. -/
theorem hat_drop_le_hatExcess [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {j p : ℤ}
    (hfinp : HasFiniteAdaptedMean P q p) :
    (d : ℝ) * (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤
      hatExcessAt P q j := by
  have h := one_le_adaptedHattedContrast_of_rounded hgrid hfinp
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [hatExcessAt]
  have hle : adaptedHattedContrast P q j - adaptedHattedContrast P q p ≤
      adaptedHattedContrast P q j - 1 := by linarith only [h]
  exact mul_le_mul_of_nonneg_left hle hd

end

end HCPolySupport.HighContrast.Quenched
