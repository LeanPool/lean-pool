/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedWaveTailOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveTailProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle

/-!
# UpperWaveTailBoundedProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Bounded good-mass wave-tail profile

This file prices the literal bounded witness from the framed random-depth
wave-tail split at one strict descendant.  It compares the actual Whitney
layer anchor with the tuned band gap, retains the squared wave-tail scale, and
sums the resulting geometric layer profile.

The outer mean/vector coefficient, the rare witness, root row, collar lanes,
grid/depth aggregation, other named lanes, and cutoff observable are not
treated here.  The declarations below are conditional internal A for this
single normalized lane.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-- Dimension-only coefficient for the unframed bounded wave-tail layer. -/
def probeSharpWaveTailBaseLayerConst (d : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
    (4 * waveTailProfileConst d) ^ 2

/-- Dimension-only coefficient after inserting the exact bounded witness
factor `2`. -/
def probeSharpWaveTailBoundedLayerConst (d : ℕ) : ℝ :=
  2 * probeSharpWaveTailBaseLayerConst d

/-- Dimension-only coefficient after the Whitney-layer sum. -/
def probeSharpWaveTailBoundedSumConst (d : ℕ) : ℝ :=
  probeSharpWaveTailBoundedLayerConst d *
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹


private theorem waveTailProfileConst_pos_local (hd : 2 ≤ d) :
    0 < waveTailProfileConst d := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hd)
  have hgain : 0 <
      streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (streamIncrementLpGainConst_pos d _) _
  have hhead : 0 < waveL4HeadConst d := by
    rw [waveL4HeadConst]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            (gammaMomentConst_pos (by norm_num)))
          gammaTriangleConst_pos)
        (sq_pos_of_pos hd0))
      geometricConcentrationConst_pos
  have hamp : 0 < hsepAmplitude (1 / 2) bfaProfileB :=
    hsepAmplitude_pos _ _
  have hbInv : 0 < bfaProfileB⁻¹ := inv_pos.mpr bfaProfileB_pos
  rw [waveTailProfileConst]
  exact mul_pos (by norm_num)
    (mul_pos (by norm_num)
      (mul_pos (mul_pos hgain hhead)
        (mul_pos hamp (mul_pos (by norm_num) hbInv))))

theorem probeSharpWaveTailBaseLayerConst_pos (hd : 2 ≤ d) :
    0 < probeSharpWaveTailBaseLayerConst d := by
  rw [probeSharpWaveTailBaseLayerConst]
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hd)
  have hC := waveTailProfileConst_pos_local hd
  positivity

theorem probeSharpWaveTailBoundedLayerConst_pos (hd : 2 ≤ d) :
    0 < probeSharpWaveTailBoundedLayerConst d := by
  rw [probeSharpWaveTailBoundedLayerConst]
  exact mul_pos (by norm_num) (probeSharpWaveTailBaseLayerConst_pos hd)

theorem probeSharpWaveTailBoundedSumConst_pos (hd : 2 ≤ d) :
    0 < probeSharpWaveTailBoundedSumConst d := by
  rw [probeSharpWaveTailBoundedSumConst]
  have hr : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact mul_pos (probeSharpWaveTailBoundedLayerConst_pos hd)
    (inv_pos.mpr (sub_pos.mpr hr))


/-! ## The actual anchor and tuned-depth decay -/


/-! ## Layer pricing and summation -/


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
