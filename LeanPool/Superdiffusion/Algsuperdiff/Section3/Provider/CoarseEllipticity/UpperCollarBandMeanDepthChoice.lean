/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants

/-!
# UpperCollarBandMeanDepthChoice

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The source-compatible depth coefficient for the collar band-mean lane

The source chooses `k₀ = ceil (c E⁻² gamma⁻¹)` with a sufficiently small
positive dimension-dependent `c`.  The coefficient `1` used by earlier upper
profiles is too large for the first collar-density exponential after the
square-root/fourth-root interpolation.  This file records that scalar mismatch
and selects a smaller coefficient from the proved percolation rate.

Nothing here changes a source-facing declaration or makes a source-node or
development-status claim.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-- A positive source-compatible coefficient for
`k₀ = ceil (c E⁻² gamma⁻¹)`. -/
def collarBandMeanDepthCoeff (d : ℕ) : ℝ :=
  siteRateBase d / 64

/-- The internally selected integer depth. -/
def collarBandMeanDepth (M : ABKModel d) (E : ℝ) : ℕ :=
  waveBandDepth (collarBandMeanDepthCoeff d) E M.gamma

/-- The room left below the Step-3 mass-density ceiling
`(siteRateBase d / 2) E⁻² gamma⁻¹`. -/
def collarBandMeanDepthSlack (d : ℕ) : ℝ :=
  siteRateBase d / 2 - collarBandMeanDepthCoeff d

/-- A dimension-only lower bound on `E⁻² gamma⁻¹` that pays both the
three-layer floor and the one-unit ceiling error. -/
def collarBandMeanDepthThreshold (d : ℕ) : ℝ :=
  max (3 * (collarBandMeanDepthCoeff d)⁻¹)
    (collarBandMeanDepthSlack d)⁻¹

private theorem siteRateBase_le_badRateConst_div_two (d : ℕ) :
    siteRateBase d ≤ badRateConst d / 2 := by
  have hrpow :
      (3 : ℝ) ^ (-(3 / 2 : ℝ) * (sepShift d : ℝ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hshift : (0 : ℝ) ≤ (sepShift d : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [siteRateBase]
  exact mul_le_of_le_one_right
    (div_nonneg (badRateConst_pos d).le (by norm_num)) hrpow

theorem collarBandMeanDepthCoeff_pos (d : ℕ) :
    0 < collarBandMeanDepthCoeff d := by
  rw [collarBandMeanDepthCoeff]
  exact div_pos (siteRateBase_pos d) (by norm_num)

theorem collarBandMeanDepthCoeff_le_one (d : ℕ) :
    collarBandMeanDepthCoeff d ≤ 1 := by
  have hbad : badRateConst d ≤ (1 / 512 : ℝ) := by
    rw [badRateConst]
    exact min_le_right _ _
  have hsite := siteRateBase_le_badRateConst_div_two d
  rw [collarBandMeanDepthCoeff]
  nlinarith

@[simp] theorem collarBandMeanDepthSlack_eq (d : ℕ) :
    collarBandMeanDepthSlack d = 31 * siteRateBase d / 64 := by
  rw [collarBandMeanDepthSlack, collarBandMeanDepthCoeff]
  ring

theorem collarBandMeanDepthSlack_pos (d : ℕ) :
    0 < collarBandMeanDepthSlack d := by
  rw [collarBandMeanDepthSlack_eq]
  exact div_pos (mul_pos (by norm_num) (siteRateBase_pos d)) (by norm_num)

theorem collarBandMeanDepthThreshold_pos (d : ℕ) :
    0 < collarBandMeanDepthThreshold d := by
  rw [collarBandMeanDepthThreshold]
  exact lt_of_lt_of_le
    (mul_pos (by norm_num) (inv_pos.mpr (collarBandMeanDepthCoeff_pos d)))
    (le_max_left _ _)


theorem three_le_waveBandDepth_collarBandMeanDepthCoeff
    {E gamma X : ℝ} (hE : 0 < E) (hgamma : 0 < gamma)
    (hX : X = E⁻¹ ^ 2 * gamma⁻¹)
    (hlarge : collarBandMeanDepthThreshold d ≤ X) :
    3 ≤ waveBandDepth (collarBandMeanDepthCoeff d) E gamma := by
  have hc := collarBandMeanDepthCoeff_pos d
  have hX0 : 0 ≤ X := by
    rw [hX]
    positivity
  have hfloor : 3 * (collarBandMeanDepthCoeff d)⁻¹ ≤ X :=
    (le_max_left _ _).trans hlarge
  have hcX : (3 : ℝ) ≤ collarBandMeanDepthCoeff d * X := by
    have := mul_le_mul_of_nonneg_left hfloor hc.le
    calc
      (3 : ℝ) = collarBandMeanDepthCoeff d *
          (3 * (collarBandMeanDepthCoeff d)⁻¹) := by
        field_simp [hc.ne']
      _ ≤ collarBandMeanDepthCoeff d * X := this
  have harg : collarBandMeanDepthCoeff d * X =
      collarBandMeanDepthCoeff d * (E ^ 2)⁻¹ * gamma⁻¹ := by
    rw [hX, inv_pow]
    ring
  have hceil := Nat.le_ceil
    (collarBandMeanDepthCoeff d * (E ^ 2)⁻¹ * gamma⁻¹)
  have hceil' : collarBandMeanDepthCoeff d * X ≤
      (⌈collarBandMeanDepthCoeff d * (E ^ 2)⁻¹ * gamma⁻¹⌉₊ : ℝ) := by
    rw [harg]
    exact hceil
  have hcast : (3 : ℝ) ≤
      (⌈collarBandMeanDepthCoeff d * (E ^ 2)⁻¹ * gamma⁻¹⌉₊ : ℝ) := by
    exact hcX.trans hceil'
  rw [waveBandDepth]
  exact_mod_cast hcast

/-- The selected ceiling satisfies the exact `Step3Seams.hk0` density window
once the dimension-only threshold pays its one-unit rounding error. -/
theorem waveBandDepth_collarBandMeanDepthCoeff_le_siteRate
    {E gamma X : ℝ} (hE : 0 < E) (hgamma : 0 < gamma)
    (hX : X = E⁻¹ ^ 2 * gamma⁻¹)
    (hlarge : collarBandMeanDepthThreshold d ≤ X) :
    (waveBandDepth (collarBandMeanDepthCoeff d) E gamma : ℝ) ≤
      siteRateBase d / 2 * X := by
  let c := collarBandMeanDepthCoeff d
  let delta := collarBandMeanDepthSlack d
  have hc : 0 < c := collarBandMeanDepthCoeff_pos d
  have hdelta : 0 < delta := collarBandMeanDepthSlack_pos d
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hround : delta⁻¹ ≤ X := (le_max_right _ _).trans hlarge
  have hone : 1 ≤ delta * X := by
    have := mul_le_mul_of_nonneg_left hround hdelta.le
    rw [mul_inv_cancel₀ hdelta.ne'] at this
    exact this
  have harg0 : 0 ≤ c * (E ^ 2)⁻¹ * gamma⁻¹ := by positivity
  have hceil := Nat.ceil_lt_add_one harg0
  have harg : c * (E ^ 2)⁻¹ * gamma⁻¹ = c * X := by
    rw [hX, inv_pow]
    ring
  have hsum : c + delta = siteRateBase d / 2 := by
    dsimp only [c, delta]
    rw [collarBandMeanDepthSlack]
    ring
  change (⌈c * (E ^ 2)⁻¹ * gamma⁻¹⌉₊ : ℝ) ≤
    siteRateBase d / 2 * X
  calc
    (⌈c * (E ^ 2)⁻¹ * gamma⁻¹⌉₊ : ℝ) ≤
        c * (E ^ 2)⁻¹ * gamma⁻¹ + 1 := hceil.le
    _ = c * X + 1 := by rw [harg]
    _ ≤ c * X + delta * X := by
      simpa only [add_comm] using add_le_add_left hone (c * X)
    _ = siteRateBase d / 2 * X := by rw [← add_mul, hsum]

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
