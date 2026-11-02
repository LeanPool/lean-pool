/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailBoundedProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle

/-!
# UpperWaveTailRareProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Rare good-mass wave-tail profile

This file prices the rare witness in the exact split of the framed random-depth
wave-tail term at one strict descendant.  It retains the target exceptional
exponent, the complete hsep-product constant, the squared `sigma` pole, and the
tuned exponential factor.  The two exponential factors in the product scale are
weakened internally to one factor.

The outer mean/vector coefficient, translation to the descendant sample,
grid/depth aggregation, root row, other named lanes, and cutoff observable are
not treated here.  These declarations are conditional internal Provider A for
the normalized rare wave-tail lane only.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- The product constant for the hsep residual and profile-tail exponents is
uniformly bounded by `64` on the terminal profile window. -/
theorem gammaProductConst_upperProfileHsepTau_tailSigma_le_sixty_four
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileHsepTau sigma) (upperProfileTailSigma sigma) ≤ 64 := by
  have htarget : 0 < upperProfileTargetSigma sigma :=
    upperProfileTargetSigma_pos hsigma0 hsigma
  have hinv : (upperProfileTargetSigma sigma)⁻¹ ≤ (6 : ℝ) :=
    (inv_le_iff_one_le_mul₀ htarget).2 (by
      rw [upperProfileTargetSigma]
      nlinarith)
  change (2 : ℝ) ^
      ((upperProfileHsepTau sigma * upperProfileTailSigma sigma /
        (upperProfileHsepTau sigma + upperProfileTailSigma sigma))⁻¹) ≤ 64
  rw [upperProfile_hsep_mul_tailSigma_eq hsigma0 hsigma]
  calc
    (2 : ℝ) ^ (upperProfileTargetSigma sigma)⁻¹ ≤
        (2 : ℝ) ^ (6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
    _ = 64 := by norm_num

/-- A dimension-only coefficient for one rare wave-tail layer.  The leading
`1` makes strict positivity unconditional. -/
def probeSharpWaveTailRareLayerConst (d : ℕ) : ℝ :=
  1 + 64 * upperHsepResidualConst *
    probeSharpWaveTailBaseLayerConst d

/-- The dimension-only coefficient after summing the rare wave-tail layer
majorant. -/
def probeSharpWaveTailRareSumConst (d : ℕ) : ℝ :=
  probeSharpWaveTailRareLayerConst d *
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹


theorem probeSharpWaveTailRareLayerConst_pos (d : ℕ) :
    0 < probeSharpWaveTailRareLayerConst d := by
  rw [probeSharpWaveTailRareLayerConst]
  have hresidual : 0 ≤ upperHsepResidualConst :=
    upperHsepResidualConst_pos.le
  have hlayer : 0 ≤ probeSharpWaveTailBaseLayerConst d := by
    rw [probeSharpWaveTailBaseLayerConst]
    positivity
  positivity

theorem probeSharpWaveTailRareSumConst_pos (d : ℕ) :
    0 < probeSharpWaveTailRareSumConst d := by
  rw [probeSharpWaveTailRareSumConst]
  have hratio : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact mul_pos (probeSharpWaveTailRareLayerConst_pos d)
    (inv_pos.mpr (sub_pos.mpr hratio))


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
