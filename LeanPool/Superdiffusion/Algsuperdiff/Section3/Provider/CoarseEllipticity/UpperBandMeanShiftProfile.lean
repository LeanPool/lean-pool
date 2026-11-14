/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandOrdinaryProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.WaveBandMean

/-!
# UpperBandMeanShiftProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic shift profile for the tuned deep-band mean

After the framed hsep factor is split, the literal deterministic `2` branch of
the tuned deep-band mean has a layer coefficient
`10 * d^2 * sqrt(layerMass) * 3^(-gamma D) * waveBandMean^2`, where
`D = k + n + ceil_n + k₀`.  This file sums that numerical carrier and restores
the outer coefficient `probeMeanGoodWaveConst M`.

The frozen maximum gate supplies `cstar M⁻¹ ≤ E`; together with the fifth-root
gate this lets `cstarInv_mul_waveBandMean_sq_le` remove every model parameter.
The result is an explicit dimension-only deterministic-shift budget.

No theorem here proves the preceding random hsep split or identifies this
carrier with the actual framed layer term.  The hsep residual, centered
deep-band tail, other wave terms, collar contribution, depth/grid aggregation,
and cutoff observable are absent.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- The dimension-only part of `probeMeanGoodWaveConst`, before its single
`cstar⁻¹` factor. -/
def probeSharpBandMeanDimensionConst (d : ℕ) : ℝ :=
  1920 * simplexCrudeConst d (1 / 4) *
    probeSimplexMeanSensitivityConst d


/-- The dimension-only one-coordinate budget after summing the deterministic
band-mean branch over Whitney layers and restoring the outer coefficient. -/
def probeSharpBandMeanCoordinateShiftConst (d : ℕ) : ℝ :=
  probeSharpBandMeanDimensionConst d *
    (10 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
      (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
    waveBandConst (probeDeepBandMeanAmplitude d)

/-- The dimension-only budget after the finite coordinate trace. -/
def probeSharpBandMeanTraceShiftConst (d : ℕ) : ℝ :=
  (d : ℝ) * probeSharpBandMeanCoordinateShiftConst d

theorem probeSharpBandMeanDimensionConst_nonneg (hd : 2 ≤ d) :
    0 ≤ probeSharpBandMeanDimensionConst d := by
  rw [probeSharpBandMeanDimensionConst]
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
    (probeSimplexMeanSensitivityConst_nonneg hd)


private theorem three_rpow_neg_half_lt_one :
    (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)


theorem probeSharpBandMeanCoordinateShiftConst_nonneg (hd : 2 ≤ d) :
    0 ≤ probeSharpBandMeanCoordinateShiftConst d := by
  rw [probeSharpBandMeanCoordinateShiftConst]
  have hden : 0 < 1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    linarith [three_rpow_neg_half_lt_one]
  exact mul_nonneg
    (mul_nonneg (probeSharpBandMeanDimensionConst_nonneg hd) (by positivity))
    (waveBandConst_nonneg _)

theorem probeSharpBandMeanTraceShiftConst_nonneg (hd : 2 ≤ d) :
    0 ≤ probeSharpBandMeanTraceShiftConst d := by
  rw [probeSharpBandMeanTraceShiftConst]
  exact mul_nonneg (Nat.cast_nonneg d)
    (probeSharpBandMeanCoordinateShiftConst_nonneg hd)


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
