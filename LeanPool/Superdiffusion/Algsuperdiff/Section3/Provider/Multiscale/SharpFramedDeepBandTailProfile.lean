/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandLayerProfile

/-!
# SharpFramedDeepBandTailProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Ordinary profile of the centered tuned deep-band tail

This file computes the exact deterministic scale of the squared centered
deep-band tail after removing the framed hsep factor at a strict descendant.
The corresponding deterministic `2` branch is summed over Whitney layers and
shown to be bounded by a dimension-only constant times `gamma`.

The actual random hsep split is not performed here, and no random variable is
identified with this numerical carrier.  The outer `probeMeanGoodWaveConst M *
vecNormSq p`, the complementary residual branch, all other good/collar terms,
depth/grid aggregation, and the cutoff observable are absent.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-- The dimension-only coefficient in the closed form of the wave-gauged
centered deep-band scale. -/
def probeSharpDeepBandTailAmplitude (d : ℕ) : ℝ :=
  HCPolySupport.IndependentSums.gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)


/-- Dimension-only coefficient for the pointwise geometric layer profile. -/
def probeSharpDeepBandTailOrdinaryLayerConst (d : ℕ) : ℝ :=
  10 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
    probeSharpDeepBandTailAmplitude d ^ 2 * 81


/-- Exact cancellation of the layer anchor in the wave-gauged centered-tail
scale. -/
theorem probeDeepBandGaugedFluct_eq_closed
    (M : ABKModel d) (ell : ℤ) (k₀ g₀ : ℕ) :
    probeDeepBandGaugedFluct M ell k₀ g₀ =
      probeSharpDeepBandTailAmplitude d * Real.sqrt M.gamma *
        probeBandUnitGain d ^ g₀ *
        (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) := by
  have hpow :
      (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (((ell + (k₀ : ℤ)) : ℤ) : ℝ)) =
        (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [probeDeepBandGaugedFluct, probeDeepBandRawFluct,
    probeSharpDeepBandTailAmplitude]
  rw [← hpow]
  ring

/-- Squared closed form of the centered deep-band scale. -/
theorem probeDeepBandGaugedFluct_sq_eq_closed
    (M : ABKModel d) (ell : ℤ) (k₀ g₀ : ℕ) :
    probeDeepBandGaugedFluct M ell k₀ g₀ ^ 2 =
      probeSharpDeepBandTailAmplitude d ^ 2 * M.gamma *
        (probeBandUnitGain d ^ g₀) ^ 2 *
        (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) := by
  have hsqrt : Real.sqrt M.gamma ^ 2 = M.gamma :=
    Real.sq_sqrt M.shellPrefix.gamma_pos.le
  have hpow : ((3 : ℝ) ^ (M.gamma * (k₀ : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) := by
    rw [← Real.rpow_natCast
      ((3 : ℝ) ^ (M.gamma * (k₀ : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [probeDeepBandGaugedFluct_eq_closed, mul_pow, mul_pow, mul_pow,
    hsqrt, hpow]


theorem probeSharpDeepBandTailOrdinaryLayerConst_nonneg (d : ℕ) :
    0 ≤ probeSharpDeepBandTailOrdinaryLayerConst d := by
  rw [probeSharpDeepBandTailOrdinaryLayerConst]
  positivity


end

end Algsuperdiff.Section3.Provider.Multiscale
