/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileClose
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerSeries
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareProfile

/-!
# UpperAfterBandRareAbsorption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Frozen-scale absorption for the rare after-band lane

This module proves the terminal numerical absorption for `foldedBlockPole`
at the exact rare after-band coordinate base scale.  The output threshold is
explicit and depends only on the dimension.

The theorem here does not perform the actual weighted depth sum or root fold,
nor does it connect the resulting numerical envelope to the complete random
variable.  It also does not assemble the other upper lanes, the complete
observable, the all-exponent result, or the frozen theorem, and it carries no
source-node or closure status.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- A uniform triangle constant for the frozen upper exponent
`(1 - sigma) / 3`, whose inverse is at most six. -/
def upperAfterBandRareTriangleConst : ℝ :=
  4 * (117649 : ℝ) ^ (12 : ℝ)

/-- A uniform grid-net constant for the frozen upper exponent. -/
def upperAfterBandRareGridNetConst (d : ℕ) : ℝ :=
  (3 * (d : ℝ) * Real.log 3) ^ (6 : ℝ)

/-- The dimension-only part of `probeMeanGoodWaveConst`. -/
def probeMeanGoodWaveDimensionConst (d : ℕ) : ℝ :=
  1920 * simplexCrudeConst d (1 / 4) *
    probeSimplexMeanSensitivityConst d


theorem upperProfileTargetSigma_one_six_le {sigma : ℝ}
    (hsigma : sigma ≤ 1 / 2) :
    (1 : ℝ) / 6 ≤ upperProfileTargetSigma sigma := by
  rw [upperProfileTargetSigma]
  linarith

theorem gammaTriangleConst_upperProfileTarget_le
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    gammaTriangleConst (upperProfileTargetSigma sigma) ≤
      upperAfterBandRareTriangleConst := by
  let tau : ℝ := upperProfileTargetSigma sigma
  have htau : (1 : ℝ) / 6 ≤ tau :=
    upperProfileTargetSigma_one_six_le hsigma
  have htau0 : 0 < tau := lt_of_lt_of_le (by norm_num) htau
  have hinv : tau⁻¹ ≤ (6 : ℝ) :=
    (inv_le_iff_one_le_mul₀ htau0).2 (by nlinarith)
  have hinv0 : 0 ≤ tau⁻¹ := (inv_pos.mpr htau0).le
  have hbase : 1 + tau⁻¹ ≤ (7 : ℝ) := by linarith
  have hp1 : (1 + tau⁻¹) ^ tau⁻¹ ≤ (7 : ℝ) ^ tau⁻¹ :=
    Real.rpow_le_rpow (by linarith) hbase hinv0
  have hp2 : (7 : ℝ) ^ tau⁻¹ ≤ (7 : ℝ) ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
  have hgrowth : gammaGrowthConst tau ≤ (117649 : ℝ) := by
    unfold gammaGrowthConst
    refine max_le (by norm_num) ?_
    calc
      (1 + tau⁻¹) ^ tau⁻¹ ≤ (7 : ℝ) ^ tau⁻¹ := hp1
      _ ≤ (7 : ℝ) ^ (6 : ℝ) := hp2
      _ = 117649 := by norm_num
  unfold gammaTriangleConst upperAfterBandRareTriangleConst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow
      (le_trans zero_le_two (two_le_gammaGrowthConst tau)) hgrowth
      (by norm_num))
    (by norm_num)

theorem gridNetConst_upperProfileTarget_le (hd : 2 ≤ d)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    gridNetConst d (upperProfileTargetSigma sigma) ≤
      upperAfterBandRareGridNetConst d := by
  let tau : ℝ := upperProfileTargetSigma sigma
  have htau : (1 : ℝ) / 6 ≤ tau :=
    upperProfileTargetSigma_one_six_le hsigma
  have htau0 : 0 < tau := lt_of_lt_of_le (by norm_num) htau
  have hinv : tau⁻¹ ≤ (6 : ℝ) :=
    (inv_le_iff_one_le_mul₀ htau0).2 (by nlinarith)
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hbase : 1 ≤ 3 * (d : ℝ) * Real.log 3 := by
    have hlog : 1 < Real.log 3 := one_lt_log_three
    nlinarith
  unfold gridNetConst upperAfterBandRareGridNetConst
  exact Real.rpow_le_rpow_of_exponent_le hbase hinv

theorem probeMeanGoodWaveConst_eq_dimension_mul_cstarInv
    (M : ABKModel d) :
    probeMeanGoodWaveConst M =
      probeMeanGoodWaveDimensionConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ := by
  rw [probeMeanGoodWaveConst, probeMeanGoodWaveDimensionConst]


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
