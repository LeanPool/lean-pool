/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# UpperCollarBandMeanConsumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Literal consumption of the collar copy of the tuned band mean

This file sums the literal ninth named summand over Whitney layers at one
translated strict descendant.  The pointwise layer estimate is the
cap/mass-interpolated estimate from `UpperCollarBandMeanProfile`; the only
random factor left after summation is the actual collar power
`3 ^ ((gamma + 2 b) hsep)` read at the translated sample.

The frozen profile gates are used internally to price that power.  No
summability, domination, or probabilistic proposition is supplied by a caller.
The finite coordinate trace is also formed here, before any cube maximum.
These declarations are internal Provider results and make no source-node or
development-status claim.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

private theorem inductionState_mono_collarBandMean
    (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}) {m₁ m₂ : ℤ}
    (hm : m₁ ≤ m₂)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₂ E) :
    Algsuperdiff.Frozen.Section3.inductionState M m₁ E := by
  rw [Algsuperdiff.Frozen.Section3.inductionState] at hS ⊢
  exact ⟨fun i hi => hS.1 i (hi.trans hm),
    fun i hi => hS.2 i (hi.trans hm)⟩


/-- The exact hsep-power scale furnished by `e.hsep.tails`. -/
def probeSharpCollarBandMeanPowerScale
    (M : ABKModel d) (sigma : ℝ) : ℝ :=
  hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB


theorem probeSharpCollarBandMeanPowerScale_nonneg
    (M : ABKModel d) (sigma : ℝ) :
    0 ≤ probeSharpCollarBandMeanPowerScale M sigma := by
  rw [probeSharpCollarBandMeanPowerScale]
  exact Real.rpow_nonneg (hsepAmplitude_pos _ _).le _


/-- The frozen gates price the exact collar hsep power at the target upper
profile exponent. -/
theorem isBigOWith_upperProfileTarget_slstarPowerTerm
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma)
      (probeSharpCollarBandMeanPowerScale M sigma) := by
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by
    rw [hscale]
    omega
  have hSroot : Algsuperdiff.Frozen.Section3.inductionState
      M (R.scale - 1) E :=
    inductionState_mono_collarBandMean M E hroot hS
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmax
  have hsigmaProfile0 : 0 < upperProfileSigma sigma := by
    rw [upperProfileSigma]
    positivity
  have hsigmaProfileHalf : upperProfileSigma sigma ≤ 1 / 2 := by
    rw [upperProfileSigma]
    linarith
  have hEexp : Real.exp
      (badClustersConst d / upperProfileSigma sigma) ≤ (E : ℝ) := by
    simpa only [upperProfileSigma, bfaProfileSigma] using
      exp_badClustersConst_div_bfaProfileSigma_le_of_profileAuxiliaryGate
        hsigma0 hexp
  have hEb : badClustersConst d / bfaProfileB ≤ (E : ℝ) :=
    badClustersConst_div_bfaProfileB_le_of_profileAuxiliaryGate
      hsigma0 hsigma hexp
  obtain ⟨hE4, hunit, hgamma20, hinvSq, hgammaZ⟩ :=
    badEventGates_of_profileAuxiliaryMaxGate M E.property hsigma0 hsigma
      hmax hEgamma
  have hgammaProfile :
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma := by
    exact hgammaZ.trans
      (zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
        hsigma0 hexp)
  have hgammaHalf : M.gamma / 2 ≤ bfaProfileB * sigma := by
    have hbs : 0 ≤ bfaProfileB * sigma :=
      mul_nonneg bfaProfileB_pos.le hsigma0.le
    nlinarith
  have hraw := isBigOWith_gammaSigma_slstarPowerTerm_of_gates
    (m := R.scale) (E := (E : ℝ))
    (sigma := upperProfileSigma sigma) (b := bfaProfileB) (gam := M.gamma)
    M M.shellPrefix.dimension E.property hSroot
    hsigmaProfile0 hsigmaProfileHalf bfaProfileB_pos
    bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20 hinvSq hEb
    hgammaZ M.shellPrefix.gamma_pos
  have htau0 : 0 < upperProfileHsepTau sigma :=
    upperProfileHsepTau_pos hsigma0 hsigma
  have htargetHsep : upperProfileTargetSigma sigma ≤
      upperProfileHsepTau sigma := by
    refine (upperProfileTargetSigma_le_hsep_mul_one hsigma0 hsigma).trans ?_
    rw [div_le_iff₀ (add_pos htau0 one_pos)]
    nlinarith [sq_nonneg (upperProfileHsepTau sigma)]
  have hcollar : upperProfileHsepTau sigma ≤
      upperProfileBaseSigma sigma /
        ((M.gamma + 2 * bfaProfileB) / bfaProfileB) := by
    convert upperProfileHsepTau_le_collarPowerSigma
      hsigma0 hsigma (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num))
      bfaProfileB_pos hgammaHalf using 1
    ring
  have hbfa :
      bfaTau (upperProfileSigma sigma) M.gamma bfaProfileB =
        upperProfileBaseSigma sigma /
          ((M.gamma + 2 * bfaProfileB) / bfaProfileB) := by
    rw [bfaTau, bfaPower, upperProfileBaseSigma]
  have htarget : upperProfileTargetSigma sigma ≤
      bfaTau (upperProfileSigma sigma) M.gamma bfaProfileB := by
    rw [hbfa]
    exact htargetHsep.trans hcollar
  have hweakened :=
    HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
      htarget hraw
  simpa only [probeSharpCollarBandMeanPowerScale] using hweakened


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
