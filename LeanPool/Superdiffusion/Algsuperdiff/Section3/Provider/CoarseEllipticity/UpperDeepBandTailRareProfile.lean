/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedDeepBandTailOrlicz

/-!
# UpperDeepBandTailRareProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Rare centered deep-band-tail Whitney-layer profile

This file prices and sums the explicit rare witness of the framed centered
deep-band-tail good-mass lane.  It retains the literal exceptional exponent
`Gamma_((1 - sigma) / 3)`, bounds the complete hsep product scale, and applies
the countable Orlicz triangle inequality over Whitney layers.

The output still precedes multiplication by `probeMeanGoodWaveConst M *
vecNormSq p`, coordinate tracing, grid/depth aggregation, and the cutoff
observable.  The root row, every other good lane, and every collar lane are
absent.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- A dimension-only coefficient for one rare centered-tail layer.  The
leading `1` makes strict positivity unconditional. -/
def probeSharpDeepBandTailRareLayerConst (d : ℕ) : ℝ :=
  1 + 32 * upperHsepResidualConst *
    probeSharpDeepBandTailOrdinaryLayerConst d

/-- The dimension-only coefficient after summing the rare centered-tail
layer majorant. -/
def probeSharpDeepBandTailRareSumConst (d : ℕ) : ℝ :=
  probeSharpDeepBandTailRareLayerConst d *
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

/-- A summable deterministic majorant for one exact rare centered-tail scale. -/
def probeSharpDeepBandTailRareGoodMassLayerBound
    (M : ABKModel d) (E : ℝ) (n : ℕ) : ℝ :=
  probeSharpDeepBandTailRareLayerConst d *
    ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * M.gamma *
    Real.exp (-(upperHsepResidualRate * (E⁻¹ ^ 2 * M.gamma⁻¹)))

theorem probeSharpDeepBandTailRareLayerConst_pos (d : ℕ) :
    0 < probeSharpDeepBandTailRareLayerConst d := by
  rw [probeSharpDeepBandTailRareLayerConst]
  have hresidual : 0 ≤ upperHsepResidualConst :=
    upperHsepResidualConst_pos.le
  have hlayer : 0 ≤ probeSharpDeepBandTailOrdinaryLayerConst d :=
    probeSharpDeepBandTailOrdinaryLayerConst_nonneg d
  positivity

theorem probeSharpDeepBandTailRareSumConst_pos (d : ℕ) :
    0 < probeSharpDeepBandTailRareSumConst d := by
  rw [probeSharpDeepBandTailRareSumConst]
  have hratio : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact mul_pos (probeSharpDeepBandTailRareLayerConst_pos d)
    (inv_pos.mpr (sub_pos.mpr hratio))

theorem probeSharpDeepBandTailRareGoodMassLayerBound_pos
    (M : ABKModel d) (E : ℝ) (n : ℕ) :
    0 < probeSharpDeepBandTailRareGoodMassLayerBound M E n := by
  rw [probeSharpDeepBandTailRareGoodMassLayerBound]
  exact mul_pos
    (mul_pos
      (mul_pos (probeSharpDeepBandTailRareLayerConst_pos d)
        (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) n))
      M.shellPrefix.gamma_pos)
    (Real.exp_pos _)


theorem summable_probeSharpDeepBandTailRareGoodMassLayerBound
    (M : ABKModel d) (E : ℝ) :
    Summable (fun n : ℕ =>
      probeSharpDeepBandTailRareGoodMassLayerBound M E n) := by
  have hratio0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hratiolt : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  simpa only [probeSharpDeepBandTailRareGoodMassLayerBound] using
    (((summable_geometric_of_lt_one hratio0 hratiolt).mul_left
      (probeSharpDeepBandTailRareLayerConst d)).mul_right M.gamma).mul_right
      (Real.exp (-(upperHsepResidualRate * (E⁻¹ ^ 2 * M.gamma⁻¹))))

/-- Exact evaluation of the summed deterministic rare-layer majorant. -/
theorem tsum_probeSharpDeepBandTailRareGoodMassLayerBound_eq
    (M : ABKModel d) (E : ℝ) :
    ∑' n : ℕ, probeSharpDeepBandTailRareGoodMassLayerBound M E n =
      probeSharpDeepBandTailRareSumConst d * M.gamma *
        Real.exp (-(upperHsepResidualRate *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  have hratio0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hratiolt : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  simp only [probeSharpDeepBandTailRareGoodMassLayerBound]
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_left,
    tsum_geometric_of_lt_one hratio0 hratiolt,
    probeSharpDeepBandTailRareSumConst]


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
