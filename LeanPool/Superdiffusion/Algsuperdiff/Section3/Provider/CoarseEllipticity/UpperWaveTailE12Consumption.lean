/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailBoundedGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailRareProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerSeries
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability

/-!
# UpperWaveTailE12Consumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact consumption for the translated framed wave-tail lane

This file connects the bounded and rare witnesses to the literal named
good-cell wave-tail summand in the framed descendant envelope.  The comparison
uses the exact descendant scale and translated cutoff sample.
Almost-everywhere summability is derived from the existing layerwise `Gamma`
estimates, so no summability assertion is added as a caller obligation when the
real layer sums are identified with the literal envelope.

Only one named good-cell wave-tail lane and one basis coordinate are consumed.
The root row, collar wave-tail lane, eleven other named lanes, complete framed
envelope, cutoff observable, and upper-leg export are not treated here.
-/
namespace Algsuperdiff.Section3.Provider.CoarseEllipticity
open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section
variable {d : ℕ}
/-! ## The literal lane at the common Section 3 depth -/
/-- The positive rate left by the squared wave-tail gain when its anchor uses
the common collar/band-mean depth. -/
def probeSharpWaveTailTunedRate (d : ℕ) : ℝ :=
  (d : ℝ) / 4 * Real.log 3 * collarBandMeanDepthCoeff d
/-- The deterministic descendant offset removed before applying the hsep
split at the common depth. -/
def probeSharpWaveTailTunedOffset
    (M : ABKModel d) (E : ℝ) (k n : ℕ) : ℝ :=
  (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
    (collarBandMeanDepth M E : ℝ)
/-- The unframed squared wave-tail carrier at the common depth. -/
def probeSharpWaveTailTunedBaseTerm
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) : ℝ :=
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  probeSharpWaveTailGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        probeSharpWaveTailTunedOffset M E k n)) *
    waveTailTerm M root E bfaProfileB root ell omega ^ 2
/-- The exact profile-tail scale of the common-depth unframed carrier. -/
def probeSharpWaveTailTunedBaseScale
    (M : ABKModel d) (root : ℤ) (E sigma : ℝ) (k n : ℕ) : ℝ :=
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  probeSharpWaveTailGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        probeSharpWaveTailTunedOffset M E k n)) *
    waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
      (2 / upperProfileSigma sigma) root ell ^ 2
/-- The bounded-hsep witness at the common depth. -/
def probeSharpWaveTailTunedBoundedLayer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) : ℝ :=
  2 * probeSharpWaveTailTunedBaseTerm M root E k n omega
/-- The residual-hsep witness at the common depth. -/
def probeSharpWaveTailTunedRareLayer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) : ℝ :=
  probeSharpAfterBandHsepResidual M root E omega *
    probeSharpWaveTailTunedBaseTerm M root E k n omega
def probeSharpWaveTailTunedBoundedLayerScale
    (M : ABKModel d) (root : ℤ) (E sigma : ℝ) (k n : ℕ) : ℝ :=
  2 * probeSharpWaveTailTunedBaseScale M root E sigma k n
def probeSharpWaveTailTunedRareLayerScale
    (M : ABKModel d) (root : ℤ) (E sigma : ℝ) (k n : ℕ) : ℝ :=
  HCPolySupport.Book.Ch04.gammaProductConst
      (upperProfileHsepTau sigma) (upperProfileTailSigma sigma) *
    upperHsepResidualScale sigma M.gamma *
    probeSharpWaveTailTunedBaseScale M root E sigma k n
def probeSharpWaveTailTunedBoundedLayerBound
    (M : ABKModel d) (E sigma : ℝ) (n : ℕ) : ℝ :=
  probeSharpWaveTailBoundedLayerConst d *
    ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * sigma⁻¹ ^ 2 *
    Real.exp (-(probeSharpWaveTailTunedRate d *
      (E⁻¹ ^ 2 * M.gamma⁻¹)))
def probeSharpWaveTailTunedRareLayerBound
    (M : ABKModel d) (E sigma : ℝ) (n : ℕ) : ℝ :=
  probeSharpWaveTailRareLayerConst d *
    ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * sigma⁻¹ ^ 2 *
    Real.exp (-(probeSharpWaveTailTunedRate d *
      (E⁻¹ ^ 2 * M.gamma⁻¹)))
private theorem probeSharpWaveTailTunedRate_pos (hd : 2 ≤ d) :
    0 < probeSharpWaveTailTunedRate d := by
  rw [probeSharpWaveTailTunedRate]
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hd)
  exact mul_pos
    (mul_pos (div_pos hd0 (by norm_num))
      (lt_trans zero_lt_one one_lt_log_three))
    (collarBandMeanDepthCoeff_pos d)
private theorem probeSharpWaveTailTunedBaseTerm_nonneg
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) :
    0 ≤ probeSharpWaveTailTunedBaseTerm M root E k n omega := by
  rw [probeSharpWaveTailTunedBaseTerm]
  exact mul_nonneg
    (mul_nonneg (probeSharpWaveTailGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
private theorem measurable_probeSharpWaveTailTunedBaseTerm
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ) :
    Measurable (probeSharpWaveTailTunedBaseTerm M root E k n) := by
  have htail := measurable_waveTailTerm M root E bfaProfileB root
    (probeSharpLayerAnchor root bfaProfileB
      (collarBandMeanDepth M E) n)
  exact measurable_const.mul (htail.pow_const (2 : ℕ))
private theorem probeSharpWaveTailTunedBaseScale_nonneg
    (M : ABKModel d) (root : ℤ) (E sigma : ℝ) (k n : ℕ) :
    0 ≤ probeSharpWaveTailTunedBaseScale M root E sigma k n := by
  rw [probeSharpWaveTailTunedBaseScale]
  exact mul_nonneg
    (mul_nonneg (probeSharpWaveTailGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
private theorem probeSharpWaveTailTunedBoundedLayer_nonneg
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) :
    0 ≤ probeSharpWaveTailTunedBoundedLayer M root E k n omega := by
  rw [probeSharpWaveTailTunedBoundedLayer]
  exact mul_nonneg (by norm_num)
    (probeSharpWaveTailTunedBaseTerm_nonneg M root E k n omega)
private theorem measurable_probeSharpWaveTailTunedBoundedLayer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ) :
    Measurable (probeSharpWaveTailTunedBoundedLayer M root E k n) :=
  (measurable_probeSharpWaveTailTunedBaseTerm M root E k n).const_mul 2
private theorem probeSharpWaveTailTunedRareLayer_nonneg
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) :
    0 ≤ probeSharpWaveTailTunedRareLayer M root E k n omega := by
  rw [probeSharpWaveTailTunedRareLayer]
  exact mul_nonneg (probeSharpAfterBandHsepResidual_nonneg M root E omega)
    (probeSharpWaveTailTunedBaseTerm_nonneg M root E k n omega)
private theorem measurable_probeSharpWaveTailTunedRareLayer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k n : ℕ) :
    Measurable (probeSharpWaveTailTunedRareLayer M root E k n) :=
  (measurable_probeSharpAfterBandHsepResidual M root E).mul
    (measurable_probeSharpWaveTailTunedBaseTerm M root E k n)
private theorem probeSharpWaveTailTuned_profileTailExponent_eq
    {sigma : ℝ} (hsigma0 : 0 < sigma) :
    (2 / upperProfileSigma sigma) /
        (2 + 2 / upperProfileSigma sigma) =
      upperProfileTailSigma sigma := by
  unfold upperProfileTailSigma upperProfileSigma
  have hsigma : sigma ≠ 0 := ne_of_gt hsigma0
  have hden : 1 + sigma / 4 ≠ 0 := by positivity
  field_simp [hsigma, hden]
  ring
/-- The common-depth unframed wave-tail layer has the same exact profile-tail
exponent as the coefficient-1 construction; only its deterministic anchor has
changed. -/
private theorem isBigOWith_upperProfileTail_probeSharpWaveTailTunedBaseTerm
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTailSigma sigma))
      (probeSharpWaveTailTunedBaseTerm M R.scale (E : ℝ) k n)
      (probeSharpWaveTailTunedBaseScale
        M R.scale (E : ℝ) sigma k n) := by
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by rw [hscale]; omega
  have hSroot : Algsuperdiff.Frozen.Section3.inductionState
      M (R.scale - 1) E := inductionState_restrict hroot hS
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
  have hsigma2 : 0 < 2 / upperProfileSigma sigma :=
    div_pos (by norm_num) hsigmaProfile0
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  have htail := isBigOWith_gammaSigma_probeWaveTailTerm_sq_of_gates
    (m := R.scale) M M.shellPrefix.dimension E.property hSroot
    hsigmaProfile0 hsigmaProfileHalf hsigma2
    bfaProfileB_pos bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20
    hinvSq hEb hgammaZ R.scale ell
  rw [probeSharpWaveTailTuned_profileTailExponent_eq hsigma0] at htail
  have hc : 0 ≤ probeSharpWaveTailGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        probeSharpWaveTailTunedOffset M (E : ℝ) k n)) :=
    mul_nonneg (probeSharpWaveTailGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _)
  exact htail.const_mul hc
private theorem isBigOWith_upperProfileTail_probeSharpWaveTailTunedBoundedLayer
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTailSigma sigma))
      (probeSharpWaveTailTunedBoundedLayer M R.scale (E : ℝ) k n)
      (probeSharpWaveTailTunedBoundedLayerScale
        M R.scale (E : ℝ) sigma k n) := by
  exact (isBigOWith_upperProfileTail_probeSharpWaveTailTunedBaseTerm
        M hR hS hsigma0 hsigma hmax hEgamma n).const_mul
          (by norm_num : (0 : ℝ) ≤ 2)
private theorem isBigOWith_upperProfileTarget_probeSharpWaveTailTunedRareLayer
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpWaveTailTunedRareLayer M R.scale (E : ℝ) k n)
      (probeSharpWaveTailTunedRareLayerScale
        M R.scale (E : ℝ) sigma k n) := by
  obtain ⟨_hpoint, hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hS hsigma0 hsigma hmax hEgamma
  have hbase :=
    isBigOWith_upperProfileTail_probeSharpWaveTailTunedBaseTerm
      M hR hS hsigma0 hsigma hmax hEgamma n
  have hproduct := isBigOWith_upperProfileTarget_hsep_mul_tail
    hsigma0 hsigma (upperHsepResidualScale_pos sigma M.gamma).le
    (probeSharpWaveTailTunedBaseScale_nonneg
      M R.scale (E : ℝ) sigma k n)
    (probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ))
    (probeSharpWaveTailTunedBaseTerm_nonneg
      M R.scale (E : ℝ) k n) hresidual hbase
  exact hproduct
/-- Pointwise, the literal common-depth framed wave-tail layer is dominated by its
two explicit witnesses. -/
private theorem probeSharpFramedGoodWavePart_waveTail_tuned_le
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2) omega ≤
      probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          probeSharpWaveTailTunedBoundedLayer
            M R.scale (E : ℝ) k n omega +
        probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          probeSharpWaveTailTunedRareLayer
            M R.scale (E : ℝ) k n omega := by
  obtain ⟨hfactor, _hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hS hsigma0 hsigma hmax hEgamma
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let D := probeSharpWaveTailTunedOffset M (E : ℝ) k n
  let C := probeSharpWaveTailGoodMassCoeff d n
  let T := waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
    (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) omega ^ 2
  have hframe := probeSharpFramedAfterBandMultiplier_descendant_eq
    M hR (E : ℝ) bfaProfileB k₀ n omega
  have hpow :
      (3 : ℝ) ^
          (M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB omega : ℝ)) *
          (3 : ℝ) ^ (-(M.gamma * D)) =
        (3 : ℝ) ^ (M.gamma *
          ((hsep M R.scale (E : ℝ) bfaProfileB omega : ℝ) - D)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hnormalized :
      probeSharpAfterBandHsepFactor M R.scale (E : ℝ) omega *
          probeSharpWaveTailTunedBaseTerm M R.scale (E : ℝ) k n omega =
        C * probeSharpFramedAfterBandMultiplier M R.scale (E : ℝ)
          bfaProfileB k₀ n (m - 1) omega * T := by
    change
      (3 : ℝ) ^
          (M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB omega : ℝ)) *
        (C * (3 : ℝ) ^ (-(M.gamma * D)) * T) = _
    rw [hframe]
    change _ = C * (3 : ℝ) ^ (M.gamma *
      ((hsep M R.scale (E : ℝ) bfaProfileB omega : ℝ) - D)) * T
    rw [← hpow]
    ring
  have houter : 0 ≤ probeMeanGoodWaveConst M * vecNormSq (basisVec j) :=
    mul_nonneg (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
      (vecNormSq_nonneg (basisVec j))
  have hbase0 := probeSharpWaveTailTunedBaseTerm_nonneg
    M R.scale (E : ℝ) k n omega
  calc
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2) omega =
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j)) *
        (probeSharpAfterBandHsepFactor M R.scale (E : ℝ) omega *
          probeSharpWaveTailTunedBaseTerm
            M R.scale (E : ℝ) k n omega) := by
      rw [hnormalized]
      dsimp only [C, T, k₀, probeSharpWaveTailGoodMassCoeff]
      unfold probeSharpFramedGoodWavePart
      ring
    _ ≤ (probeMeanGoodWaveConst M * vecNormSq (basisVec j)) *
        ((2 + probeSharpAfterBandHsepResidual M R.scale (E : ℝ) omega) *
          probeSharpWaveTailTunedBaseTerm
            M R.scale (E : ℝ) k n omega) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hfactor omega) hbase0) houter
    _ = _ := by
      rw [probeSharpWaveTailTunedBoundedLayer,
        probeSharpWaveTailTunedRareLayer]
      ring
private theorem waveTailGainScale_tuned_anchor_le
    (M : ABKModel d) (root : ℤ) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (k₀ n : ℕ) :
    waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
        (2 / upperProfileSigma sigma) root
        (probeSharpLayerAnchor root bfaProfileB k₀ n) ≤
      (4 * waveTailProfileConst d) * sigma⁻¹ *
        (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
  have hsigmaProfile0 : 0 < upperProfileSigma sigma := by
    rw [upperProfileSigma]
    positivity
  have hsigmaProfileHalf : upperProfileSigma sigma ≤ 1 / 2 := by
    rw [upperProfileSigma]
    linarith
  have hgap : root - probeSharpLayerAnchor root bfaProfileB k₀ n =
      (whitneyScaleSeq bfaProfileB 0 (k₀ + n) n : ℕ) := by
    rw [probeSharpLayerAnchor, whitneyScaleSeq]
    push_cast
    ring
  have hprofile := waveTailGainScale_profile_le
    (M := M) hsigmaProfile0 hsigmaProfileHalf hgap
  have hkn : (k₀ : ℝ) ≤ ((k₀ + n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right k₀ n
  have hdecay :
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((k₀ + n : ℕ) : ℝ)) ≤
        (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hd0 : 0 ≤ (d : ℝ) / 8 := by positivity
    nlinarith
  have hC0 : 0 ≤ waveTailProfileConst d := by
    rw [waveTailProfileConst]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by norm_num)
        (mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (streamIncrementLpGainConst_pos d _).le _)
            (waveL4HeadConst_nonneg d))
          (mul_nonneg (hsepAmplitude_pos _ _).le
            (mul_nonneg (by norm_num) (inv_nonneg.mpr bfaProfileB_pos.le)))))
  have hinv : (upperProfileSigma sigma)⁻¹ = 4 * sigma⁻¹ := by
    rw [upperProfileSigma]
    field_simp [ne_of_gt hsigma0]
  calc
    waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
          (2 / upperProfileSigma sigma) root
          (probeSharpLayerAnchor root bfaProfileB k₀ n) ≤
        waveTailProfileConst d * (upperProfileSigma sigma)⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * ((k₀ + n : ℕ) : ℝ)) := hprofile
    _ ≤ waveTailProfileConst d * (upperProfileSigma sigma)⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg hC0 (inv_nonneg.mpr hsigmaProfile0.le))
    _ = (4 * waveTailProfileConst d) * sigma⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
      rw [hinv]
      ring
private theorem collarBandMeanDepth_waveTail_decay
    (M : ABKModel d) (E : ℝ) :
    (3 : ℝ) ^ (-((d : ℝ) / 4) *
        (collarBandMeanDepth M E : ℝ)) ≤
      Real.exp (-(probeSharpWaveTailTunedRate d *
        (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let X : ℝ := E⁻¹ ^ 2 * M.gamma⁻¹
  let A : ℝ := (d : ℝ) / 4 * Real.log 3
  let c : ℝ := collarBandMeanDepthCoeff d
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (by positivity)
      (lt_trans zero_lt_one one_lt_log_three).le
  have hceil : c * X ≤ (collarBandMeanDepth M E : ℝ) := by
    have h := Nat.le_ceil (c * (E ^ 2)⁻¹ * M.gamma⁻¹)
    dsimp only [c] at h
    dsimp only [c, X]
    rw [collarBandMeanDepth, waveBandDepth]
    simpa only [inv_pow, mul_assoc] using h
  have hproduct : probeSharpWaveTailTunedRate d * X ≤
      A * (collarBandMeanDepth M E : ℝ) := by
    calc
      probeSharpWaveTailTunedRate d * X = A * (c * X) := by
        dsimp only [A, c]
        rw [probeSharpWaveTailTunedRate]
        ring
      _ ≤ A * (collarBandMeanDepth M E : ℝ) :=
        mul_le_mul_of_nonneg_left hceil hA0
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  calc
    Real.log 3 *
          (-((d : ℝ) / 4) * (collarBandMeanDepth M E : ℝ)) =
        -(A * (collarBandMeanDepth M E : ℝ)) := by
      dsimp only [A]
      ring
    _ ≤ -(probeSharpWaveTailTunedRate d * X) := neg_le_neg hproduct
private theorem waveTailTunedDepthEighth_sq_eq_quarter
    (k₀ : ℕ) :
    ((3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ))) ^ 2 =
      (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
  rw [← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring
private theorem three_rpow_neg_nat_half_eq_tuned (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℝ) / 2) =
      ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  rw [show -(n : ℝ) / 2 = (-(1 / 2 : ℝ)) * (n : ℝ) by ring,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
private theorem probeSharpWaveTailTunedBaseScale_le_profile
    (M : ABKModel d) (root : ℤ) {E sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (k n : ℕ) :
    probeSharpWaveTailTunedBaseScale M root E sigma k n ≤
      probeSharpWaveTailBaseLayerConst d *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * sigma⁻¹ ^ 2 *
        Real.exp (-(probeSharpWaveTailTunedRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let k₀ : ℕ := collarBandMeanDepth M E
  let ell : ℤ := probeSharpLayerAnchor root bfaProfileB k₀ n
  let D : ℝ := probeSharpWaveTailTunedOffset M E k n
  let B : ℝ := 4 * waveTailProfileConst d
  let G : ℝ := waveTailGainScale d bfaProfileB
    (upperProfileSigma sigma) (2 / upperProfileSigma sigma) root ell
  let r : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  let Z : ℝ := Real.exp (-(probeSharpWaveTailTunedRate d *
    (E⁻¹ ^ 2 * M.gamma⁻¹)))
  have hG : G ≤ B * sigma⁻¹ *
      (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
    dsimp only [G, B, ell, k₀]
    exact waveTailGainScale_tuned_anchor_le M root hsigma0 hsigma _ n
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact waveTailGainScale_nonneg _ _ _ _ _ _
  have hGSq := pow_le_pow_left₀ hG0 hG 2
  have hdepthSq := waveTailTunedDepthEighth_sq_eq_quarter (d := d) k₀
  have hGSq' : G ^ 2 ≤ B ^ 2 * sigma⁻¹ ^ 2 *
      (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
    calc
      G ^ 2 ≤ (B * sigma⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ))) ^ 2 := hGSq
      _ = B ^ 2 * sigma⁻¹ ^ 2 *
          (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
        rw [mul_pow, mul_pow, hdepthSq]
  have hD0 : 0 ≤ D := by
    dsimp only [D, probeSharpWaveTailTunedOffset]
    positivity
  have hframe : (3 : ℝ) ^ (-(M.gamma * D)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg M.shellPrefix.gamma_pos.le hD0))
  have hframeGain : (3 : ℝ) ^ (-(M.gamma * D)) * G ^ 2 ≤
      B ^ 2 * sigma⁻¹ ^ 2 *
        (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
    calc
      (3 : ℝ) ^ (-(M.gamma * D)) * G ^ 2 ≤ 1 *
          (B ^ 2 * sigma⁻¹ ^ 2 *
            (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ))) :=
        mul_le_mul hframe hGSq' (sq_nonneg G) zero_le_one
      _ = _ := one_mul _
  have hcoeff0 : 0 ≤ probeSharpWaveTailGoodMassCoeff d n :=
    probeSharpWaveTailGoodMassCoeff_nonneg d n
  have hpre : probeSharpWaveTailTunedBaseScale M root E sigma k n ≤
      probeSharpWaveTailBaseLayerConst d * r ^ n * sigma⁻¹ ^ 2 *
        (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
    rw [probeSharpWaveTailTunedBaseScale]
    change probeSharpWaveTailGoodMassCoeff d n *
        (3 : ℝ) ^ (-(M.gamma * D)) * G ^ 2 ≤ _
    calc
      probeSharpWaveTailGoodMassCoeff d n *
          (3 : ℝ) ^ (-(M.gamma * D)) * G ^ 2 =
        probeSharpWaveTailGoodMassCoeff d n *
          ((3 : ℝ) ^ (-(M.gamma * D)) * G ^ 2) := by ring
      _ ≤ probeSharpWaveTailGoodMassCoeff d n *
          (B ^ 2 * sigma⁻¹ ^ 2 *
            (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ))) :=
        mul_le_mul_of_nonneg_left hframeGain hcoeff0
      _ = probeSharpWaveTailBaseLayerConst d * r ^ n * sigma⁻¹ ^ 2 *
          (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
        rw [probeSharpWaveTailGoodMassCoeff,
          sqrt_probeSharpLayerMassEnvelope_eq,
          three_rpow_neg_nat_half_eq_tuned,
          probeSharpWaveTailBaseLayerConst]
        dsimp only [B, r]
        ring
  have hdecay :
      (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) ≤ Z := by
    dsimp only [k₀, Z]
    exact collarBandMeanDepth_waveTail_decay M E
  have hfactor0 : 0 ≤ probeSharpWaveTailBaseLayerConst d *
      r ^ n * sigma⁻¹ ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (probeSharpWaveTailBaseLayerConst_pos
        M.shellPrefix.dimension).le
        (pow_nonneg (Real.rpow_nonneg (by norm_num) _) n))
      (sq_nonneg sigma⁻¹)
  change probeSharpWaveTailTunedBaseScale M root E sigma k n ≤
    probeSharpWaveTailBaseLayerConst d * r ^ n * sigma⁻¹ ^ 2 * Z
  exact hpre.trans (mul_le_mul_of_nonneg_left hdecay hfactor0)
private theorem probeSharpWaveTailTunedBoundedLayerScale_le
    (M : ABKModel d) (root : ℤ) {E sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) (k n : ℕ) :
    probeSharpWaveTailTunedBoundedLayerScale M root E sigma k n ≤
      probeSharpWaveTailTunedBoundedLayerBound M E sigma n := by
  have hbase := probeSharpWaveTailTunedBaseScale_le_profile
    M root (E := E) hsigma0 hsigma k n
  have h := mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 2)
  rw [probeSharpWaveTailTunedBoundedLayerScale,
    probeSharpWaveTailTunedBoundedLayerBound,
    probeSharpWaveTailBoundedLayerConst]
  exact h.trans_eq (by ring)
private theorem probeSharpWaveTailTunedRareLayerScale_le
    (M : ABKModel d) (root : ℤ) {E sigma : ℝ}
    (hE : 1 ≤ E) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (k n : ℕ) :
    probeSharpWaveTailTunedRareLayerScale M root E sigma k n ≤
      probeSharpWaveTailTunedRareLayerBound M E sigma n := by
  let G : ℝ := HCPolySupport.Book.Ch04.gammaProductConst
    (upperProfileHsepTau sigma) (upperProfileTailSigma sigma)
  let AR : ℝ := upperHsepResidualScale sigma M.gamma
  let AX : ℝ := probeSharpWaveTailTunedBaseScale M root E sigma k n
  let C : ℝ := probeSharpWaveTailBaseLayerConst d
  let r : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  let Z : ℝ := Real.exp (-(probeSharpWaveTailTunedRate d *
    (E⁻¹ ^ 2 * M.gamma⁻¹)))
  have hG : G ≤ 64 :=
    gammaProductConst_upperProfileHsepTau_tailSigma_le_sixty_four
      hsigma0 hsigma
  have hARexp := upperHsepResidualScale_le_exp hsigma0 hsigma hE
    M.shellPrefix.gamma_pos
  have hX0 : 0 ≤ upperHsepResidualRate * (E⁻¹ ^ 2 * M.gamma⁻¹) :=
    mul_nonneg upperHsepResidualRate_pos.le
      (mul_nonneg (sq_nonneg E⁻¹)
        (inv_nonneg.mpr M.shellPrefix.gamma_pos.le))
  have hExpOne : Real.exp (-(upperHsepResidualRate *
      (E⁻¹ ^ 2 * M.gamma⁻¹))) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hX0)
  have hAR : AR ≤ upperHsepResidualConst := by
    exact hARexp.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hExpOne
        upperHsepResidualConst_pos.le)
  have hAX : AX ≤ C * r ^ n * sigma⁻¹ ^ 2 * Z :=
    probeSharpWaveTailTunedBaseScale_le_profile
      M root hsigma0 hsigma k n
  have hAR0 : 0 ≤ AR := (upperHsepResidualScale_pos sigma M.gamma).le
  have hAX0 : 0 ≤ AX :=
    probeSharpWaveTailTunedBaseScale_nonneg M root E sigma k n
  have hprofile0 : 0 ≤ C * r ^ n * sigma⁻¹ ^ 2 * Z := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (probeSharpWaveTailBaseLayerConst_pos
          M.shellPrefix.dimension).le
          (pow_nonneg (Real.rpow_nonneg (by norm_num) _) n))
        (sq_nonneg sigma⁻¹)) (Real.exp_pos _).le
  have hproduct : G * AR * AX ≤
      (64 * upperHsepResidualConst) * (C * r ^ n * sigma⁻¹ ^ 2 * Z) := by
    exact mul_le_mul
      (mul_le_mul hG hAR hAR0 (by norm_num)) hAX hAX0
      (mul_nonneg (by norm_num) upperHsepResidualConst_pos.le)
  have hcoef : 64 * upperHsepResidualConst * C ≤
      probeSharpWaveTailRareLayerConst d := by
    rw [probeSharpWaveTailRareLayerConst]
    dsimp only [C]
    linarith
  change G * AR * AX ≤
    probeSharpWaveTailRareLayerConst d * r ^ n * sigma⁻¹ ^ 2 * Z
  calc
    G * AR * AX ≤
        (64 * upperHsepResidualConst) *
          (C * r ^ n * sigma⁻¹ ^ 2 * Z) := hproduct
    _ = (64 * upperHsepResidualConst * C) * r ^ n * sigma⁻¹ ^ 2 * Z := by
      ring
    _ ≤ probeSharpWaveTailRareLayerConst d * r ^ n * sigma⁻¹ ^ 2 * Z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef
            (pow_nonneg (Real.rpow_nonneg (by norm_num) _) n))
          (sq_nonneg sigma⁻¹)) (Real.exp_pos _).le
private theorem probeSharpWaveTailTunedBoundedLayerBound_pos
    (M : ABKModel d) (E : ℝ) {sigma : ℝ} (hsigma0 : 0 < sigma) (n : ℕ) :
    0 < probeSharpWaveTailTunedBoundedLayerBound M E sigma n := by
  rw [probeSharpWaveTailTunedBoundedLayerBound]
  exact mul_pos
    (mul_pos
      (mul_pos (probeSharpWaveTailBoundedLayerConst_pos M.shellPrefix.dimension)
        (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) n))
      (pow_pos (inv_pos.mpr hsigma0) 2)) (Real.exp_pos _)
private theorem probeSharpWaveTailTunedRareLayerBound_pos
    (M : ABKModel d) (E : ℝ) {sigma : ℝ} (hsigma0 : 0 < sigma) (n : ℕ) :
    0 < probeSharpWaveTailTunedRareLayerBound M E sigma n := by
  rw [probeSharpWaveTailTunedRareLayerBound]
  exact mul_pos
    (mul_pos
      (mul_pos (probeSharpWaveTailRareLayerConst_pos d)
        (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) n))
      (pow_pos (inv_pos.mpr hsigma0) 2)) (Real.exp_pos _)
private theorem summable_probeSharpWaveTailTunedBoundedLayerBound
    (M : ABKModel d) (E sigma : ℝ) :
    Summable (probeSharpWaveTailTunedBoundedLayerBound M E sigma) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact ((((summable_geometric_of_lt_one hr0 hr1).mul_left
      (probeSharpWaveTailBoundedLayerConst d)).mul_right
        (sigma⁻¹ ^ 2)).mul_right
      (Real.exp (-(probeSharpWaveTailTunedRate d *
        (E⁻¹ ^ 2 * M.gamma⁻¹)))))
private theorem summable_probeSharpWaveTailTunedRareLayerBound
    (M : ABKModel d) (E sigma : ℝ) :
    Summable (probeSharpWaveTailTunedRareLayerBound M E sigma) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact ((((summable_geometric_of_lt_one hr0 hr1).mul_left
      (probeSharpWaveTailRareLayerConst d)).mul_right
        (sigma⁻¹ ^ 2)).mul_right
      (Real.exp (-(probeSharpWaveTailTunedRate d *
        (E⁻¹ ^ 2 * M.gamma⁻¹)))))
private theorem tsum_probeSharpWaveTailTunedBoundedLayerBound_eq
    (M : ABKModel d) (E sigma : ℝ) :
    ∑' n, probeSharpWaveTailTunedBoundedLayerBound M E sigma n =
      probeSharpWaveTailBoundedSumConst d * sigma⁻¹ ^ 2 *
        Real.exp (-(probeSharpWaveTailTunedRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  simp only [probeSharpWaveTailTunedBoundedLayerBound]
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1, probeSharpWaveTailBoundedSumConst]
private theorem tsum_probeSharpWaveTailTunedRareLayerBound_eq
    (M : ABKModel d) (E sigma : ℝ) :
    ∑' n, probeSharpWaveTailTunedRareLayerBound M E sigma n =
      probeSharpWaveTailRareSumConst d * sigma⁻¹ ^ 2 *
        Real.exp (-(probeSharpWaveTailTunedRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  simp only [probeSharpWaveTailTunedRareLayerBound]
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1, probeSharpWaveTailRareSumConst]
def probeSharpWaveTailTunedTraceRawConst (d : ℕ) : ℝ :=
  max
    ((d : ℝ) * probeMeanGoodWaveDimensionConst d *
      superposedFluxTriangleConst * probeSharpWaveTailBoundedSumConst d)
    ((d : ℝ) * probeMeanGoodWaveDimensionConst d *
      upperAfterBandRareTriangleConst * probeSharpWaveTailRareSumConst d)
def probeSharpWaveTailTunedTraceScale
    (M : ABKModel d) (E sigma : ℝ) : ℝ :=
  probeSharpWaveTailTunedTraceRawConst d *
    (((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) *
      Real.exp (-(probeSharpWaveTailTunedRate d *
        (E⁻¹ ^ 2 * M.gamma⁻¹))))
def probeSharpWaveTailTunedFrozenPrefactor (d : ℕ) : ℝ :=
  probeSharpWaveTailTunedTraceRawConst d *
    (probeSharpWaveTailTunedRate d / 2)⁻¹
def probeSharpWaveTailTunedOutputConst (d : ℕ) : ℝ :=
  max (profileAuxiliaryConst d)
    (1 + 2 * (probeSharpWaveTailTunedFrozenPrefactor d + 8) *
      (probeSharpWaveTailTunedRate d)⁻¹)
private theorem probeMeanGoodWaveDimensionConst_nonneg_local (hd : 2 ≤ d) :
    0 ≤ probeMeanGoodWaveDimensionConst d := by
  rw [probeMeanGoodWaveDimensionConst]
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
    (probeSimplexMeanSensitivityConst_nonneg hd)
private theorem probeSharpWaveTailTunedTraceRawConst_nonneg (hd : 2 ≤ d) :
    0 ≤ probeSharpWaveTailTunedTraceRawConst d := by
  rw [probeSharpWaveTailTunedTraceRawConst]
  have hfirst : 0 ≤ (d : ℝ) * probeMeanGoodWaveDimensionConst d *
      superposedFluxTriangleConst * probeSharpWaveTailBoundedSumConst d :=
    mul_nonneg
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d)
        (probeMeanGoodWaveDimensionConst_nonneg_local hd))
      (by rw [superposedFluxTriangleConst]; positivity))
    (probeSharpWaveTailBoundedSumConst_pos hd).le
  exact hfirst.trans (le_max_left _ _)
private theorem probeSharpWaveTailTunedOutputConst_pos (hd : 2 ≤ d) :
    0 < probeSharpWaveTailTunedOutputConst d := by
  rw [probeSharpWaveTailTunedOutputConst]
  have hraw := probeSharpWaveTailTunedTraceRawConst_nonneg hd
  have hrate := probeSharpWaveTailTunedRate_pos hd
  have hfrozen : 0 ≤ probeSharpWaveTailTunedFrozenPrefactor d := by
    rw [probeSharpWaveTailTunedFrozenPrefactor]
    exact mul_nonneg hraw (inv_nonneg.mpr (div_nonneg hrate.le (by norm_num)))
  have : 0 < 1 + 2 * (probeSharpWaveTailTunedFrozenPrefactor d + 8) *
      (probeSharpWaveTailTunedRate d)⁻¹ := by positivity
  exact this.trans_le (le_max_right _ _)
private theorem probeSharpWaveTailTuned_output_choices
    (hd : 2 ≤ d) {Cup : ℝ}
    (houtput : probeSharpWaveTailTunedOutputConst d ≤ Cup) :
    profileAuxiliaryConst d ≤ Cup ∧ 1 ≤ Cup ∧
      probeSharpWaveTailTunedFrozenPrefactor d + 8 ≤
        (probeSharpWaveTailTunedRate d / 2) * Cup := by
  have hprofile := (le_max_left _ _).trans houtput
  have hbranch : 1 + 2 * (probeSharpWaveTailTunedFrozenPrefactor d + 8) *
      (probeSharpWaveTailTunedRate d)⁻¹ ≤ Cup :=
    (le_max_right _ _).trans houtput
  have hrate := probeSharpWaveTailTunedRate_pos hd
  have hfrozen : 0 ≤ probeSharpWaveTailTunedFrozenPrefactor d := by
    rw [probeSharpWaveTailTunedFrozenPrefactor]
    exact mul_nonneg (probeSharpWaveTailTunedTraceRawConst_nonneg hd)
      (inv_nonneg.mpr (div_nonneg hrate.le (by norm_num)))
  refine ⟨hprofile, by nlinarith [inv_pos.mpr hrate], ?_⟩
  have hmul : (probeSharpWaveTailTunedRate d / 2) *
      (1 + 2 * (probeSharpWaveTailTunedFrozenPrefactor d + 8) *
        (probeSharpWaveTailTunedRate d)⁻¹) ≤
      (probeSharpWaveTailTunedRate d / 2) * Cup :=
    mul_le_mul_of_nonneg_left hbranch
      (div_nonneg hrate.le (by norm_num))
  have hcancel : (probeSharpWaveTailTunedRate d / 2) *
      (2 * (probeSharpWaveTailTunedFrozenPrefactor d + 8) *
        (probeSharpWaveTailTunedRate d)⁻¹) =
      probeSharpWaveTailTunedFrozenPrefactor d + 8 := by
    field_simp [ne_of_gt hrate]
  nlinarith
private theorem cstarInv_sigmaInvSq_exp_tuned_le_halfRate
    {cstarInv rate Cup E sigma X : ℝ}
    (hrate : 0 < rate) (hCup : 1 ≤ Cup) (hsigma : 0 < sigma)
    (hgate : Real.exp (Cup / sigma) ≤ E)
    (hcstarInv : cstarInv ≤ E) (hXcube : E ^ 3 ≤ X) :
    (cstarInv * sigma⁻¹ ^ 2) * Real.exp (-(rate * X)) ≤
      (rate / 2)⁻¹ * Real.exp (-((rate / 2) * X)) := by
  have hE0 : 0 ≤ E := (Real.exp_pos (Cup / sigma)).le.trans hgate
  have hsigmaInv0 : 0 ≤ sigma⁻¹ := (inv_pos.mpr hsigma).le
  have hsigmaInvE : sigma⁻¹ ≤ E := by
    calc
      sigma⁻¹ ≤ Cup / sigma := by
        rw [div_eq_mul_inv]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hCup hsigmaInv0
      _ ≤ Real.exp (Cup / sigma) := by linarith [Real.add_one_le_exp (Cup / sigma)]
      _ ≤ E := hgate
  have hsigmaInvSqE : sigma⁻¹ ^ 2 ≤ E ^ 2 :=
    pow_le_pow_left₀ hsigmaInv0 hsigmaInvE 2
  have hpolyX : cstarInv * sigma⁻¹ ^ 2 ≤ X := by
    calc
      cstarInv * sigma⁻¹ ^ 2 ≤ E * E ^ 2 :=
        mul_le_mul hcstarInv hsigmaInvSqE (sq_nonneg sigma⁻¹) hE0
      _ = E ^ 3 := by ring
      _ ≤ X := hXcube
  have hhalf : 0 < rate / 2 := div_pos hrate (by norm_num)
  calc
    (cstarInv * sigma⁻¹ ^ 2) * Real.exp (-(rate * X)) ≤
        X * Real.exp (-(rate * X)) :=
      mul_le_mul_of_nonneg_right hpolyX (Real.exp_pos _).le
    _ ≤ ((rate / 2)⁻¹ * Real.exp ((rate / 2) * X)) *
          Real.exp (-(rate * X)) :=
      mul_le_mul_of_nonneg_right (Real.le_inv_mul_exp X hhalf)
        (Real.exp_pos _).le
    _ = (rate / 2)⁻¹ * Real.exp (-((rate / 2) * X)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
private theorem probeSharpWaveTailTunedTraceScale_le_frozen_pow
    (M : ABKModel d) {E : {E : ℝ // 1 ≤ E}} {sigma Cup : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : probeSharpWaveTailTunedOutputConst d ≤ Cup) :
    probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma ≤
      (Real.exp (-(Cup⁻¹ *
        ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8 := by
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  let rate : ℝ := probeSharpWaveTailTunedRate d
  have hd := M.shellPrefix.dimension
  have hCup0 : 0 < Cup :=
    (probeSharpWaveTailTunedOutputConst_pos hd).trans_le houtput
  obtain ⟨_hprofile, hCup1, hchoice⟩ :=
    probeSharpWaveTailTuned_output_choices hd houtput
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hXcube : (E : ℝ) ^ 3 ≤ X := by
    dsimp only [X]
    exact Algsuperdiff.Section3.Provider.Percolation.cube_le_invSq_mul_gammaInv
      M E.property hgamma
  have hpoly := cstarInv_sigmaInvSq_exp_tuned_le_halfRate
    (probeSharpWaveTailTunedRate_pos hd) hCup1 hsigma0
    ((le_max_left _ _).trans hmax) ((le_max_right _ _).trans hmax) hXcube
  have hraw := probeSharpWaveTailTunedTraceRawConst_nonneg hd
  have hhalf : probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma ≤
      probeSharpWaveTailTunedFrozenPrefactor d *
        Real.exp (-((rate / 2) * X)) := by
    rw [probeSharpWaveTailTunedTraceScale,
      probeSharpWaveTailTunedFrozenPrefactor]
    dsimp only [rate, X]
    exact (mul_le_mul_of_nonneg_left hpoly hraw).trans_eq (by ring)
  have hfrozen0 : 0 ≤ probeSharpWaveTailTunedFrozenPrefactor d := by
    rw [probeSharpWaveTailTunedFrozenPrefactor]
    exact mul_nonneg hraw
      (inv_nonneg.mpr (div_nonneg (probeSharpWaveTailTunedRate_pos hd).le
        (by norm_num)))
  have hpref := prefactor_mul_exp_le_frozenRare_pow hfrozen0
    hCup0 hX hchoice
  exact hhalf.trans (by simpa only [rate, X, eps] using hpref)
private theorem waveTail_trace_ofReal_domination :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d},
      R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) →
        ∀ {E : { E : ℝ // (1 : ℝ) ≤ E }},
          Frozen.Section3.inductionState M (m - (1 : ℤ)) E →
            ∀ {sigma : ℝ},
              (0 : ℝ) < sigma →
                sigma ≤ (1 / 2 : ℝ) →
                  (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
                    let shift : Vec d := triadicCubeShift R;
                    let B : CutoffSample d → ℝ := fun (eta : CutoffSample d) =>
                      ∑' (n : ℕ), probeSharpWaveTailTunedBoundedLayer M R.scale (↑E : ℝ) k n eta;
                    let V : CutoffSample d → ℝ := fun (eta : CutoffSample d) =>
                      ∑' (n : ℕ), probeSharpWaveTailTunedRareLayer M R.scale (↑E : ℝ) k n eta;
                    let C : ℝ := (↑d : ℝ) * probeMeanGoodWaveConst M;
                    let bounded : CutoffSample d → ℝ := fun (omega : CutoffSample d) =>
                      C * B (translateCutoffSample shift omega);
                    let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) =>
                      C * V (translateCutoffSample shift omega);
                    (2 : ℕ) ≤ d →
                      max (Real.exp (profileAuxiliaryConst d / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ) →
                        (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                            Summable fun (n : ℕ) =>
                              probeSharpWaveTailTunedBoundedLayer M R.scale (↑E : ℝ) k n
                                (translateCutoffSample shift omega)) →
                          (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                              Summable fun (n : ℕ) =>
                                probeSharpWaveTailTunedRareLayer M R.scale (↑E : ℝ) k n
                                  (translateCutoffSample shift omega)) →
                            (∀ (omega : CutoffSample d), (0 : ℝ) ≤ bounded omega) →
                              (∀ (omega : CutoffSample d), (0 : ℝ) ≤ rare omega) →
                                let L : Fin d → ℕ → CutoffSample d → ℝ :=
                                  fun (j : Fin d) (n : ℕ) (omega : CutoffSample d) =>
                                  probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
                                    (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                                    (fun (eta : CutoffSample d) =>
                                      waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                          (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                                          eta ^
                                        (2 : ℕ))
                                    (translateCutoffSample shift omega);
                                let traceR : CutoffSample d → ℝ := fun (omega : CutoffSample d) =>
                                  ∑ j : Fin d, ∑' (n : ℕ), L j n omega;
                                let traceE : CutoffSample d → ENNReal := fun (omega : CutoffSample d) =>
                                  ∑ j : Fin d, ∑' (n : ℕ), ENNReal.ofReal (L j n omega);
                                ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                                  traceR omega ≤ bounded omega + rare omega ∧
                                    traceE omega = ENNReal.ofReal (traceR omega) ∧
                                      traceE omega ≤ ENNReal.ofReal (bounded omega) + ENNReal.ofReal (rare omega) := by
  intro d M m k R hR E hstate _ hsigma0 hsigma hEgamma shift B V C bounded rare hd hmaxAux hBtranslated hVtranslated hbounded0 hrare0 L traceR traceE
  filter_upwards [hBtranslated, hVtranslated] with omega hBs hVs
  have hterm0 (j : Fin d) (n : ℕ) : 0 ≤ L j n omega := by
    dsimp only [L]
    exact probeSharpFramedGoodWavePart_nonneg hd M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
      (fun _ => sq_nonneg _) _
  have hj (j : Fin d) :
      Summable (fun n => L j n omega) ∧ (∑' n, L j n omega) ≤
        probeMeanGoodWaveConst M * B (translateCutoffSample shift omega) +
          probeMeanGoodWaveConst M * V (translateCutoffSample shift omega) := by
    let O : ℕ → ℝ := fun n => probeMeanGoodWaveConst M *
      probeSharpWaveTailTunedBoundedLayer M R.scale (E : ℝ) k n
        (translateCutoffSample shift omega)
    let W : ℕ → ℝ := fun n => probeMeanGoodWaveConst M *
      probeSharpWaveTailTunedRareLayer M R.scale (E : ℝ) k n
        (translateCutoffSample shift omega)
    have hle : ∀ n, L j n omega ≤ O n + W n := fun n => by
      simpa only [L, O, W, vecNormSq_basisVec, mul_one] using
        probeSharpFramedGoodWavePart_waveTail_tuned_le M hR hstate hsigma0
          hsigma hmaxAux hEgamma n j (translateCutoffSample shift omega)
    have hright : Summable fun n => O n + W n :=
      (hBs.mul_left (probeMeanGoodWaveConst M)).add
        (hVs.mul_left (probeMeanGoodWaveConst M))
    have hleft := Summable.of_nonneg_of_le (hterm0 j) hle hright
    have hsum := Summable.tsum_le_tsum hle hleft hright
    refine ⟨hleft, hsum.trans_eq ?_⟩
    exact ((hBs.mul_left (probeMeanGoodWaveConst M)).tsum_add
      (hVs.mul_left (probeMeanGoodWaveConst M))).trans (by
        simp only [B, V, tsum_mul_left])
  have hreal : traceR omega ≤ bounded omega + rare omega := by
    dsimp only [traceR]
    calc
      _ ≤ ∑ _j : Fin d, (probeMeanGoodWaveConst M * B
          (translateCutoffSample shift omega) + probeMeanGoodWaveConst M * V
          (translateCutoffSample shift omega)) :=
        Finset.sum_le_sum fun j _ => (hj j).2
      _ = bounded omega + rare omega := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, bounded, rare, C]
        ring
  have heq : traceE omega = ENNReal.ofReal (traceR omega) := by
    dsimp only [traceE, traceR]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => tsum_nonneg (hterm0 j))]
    exact Finset.sum_congr rfl fun j _ =>
      (ENNReal.ofReal_tsum_of_nonneg (hterm0 j) (hj j).1).symm
  have henn : traceE omega ≤
      ENNReal.ofReal (bounded omega) + ENNReal.ofReal (rare omega) := by
    calc
      traceE omega = ENNReal.ofReal (traceR omega) := heq
      _ ≤ ENNReal.ofReal (bounded omega + rare omega) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (bounded omega) + ENNReal.ofReal (rare omega) :=
        ENNReal.ofReal_add (hbounded0 omega) (hrare0 omega)
  exact ⟨hreal, heq, henn⟩

private theorem upperWaveTailE12Consumption_momentBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) {k : ℕ} {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ},
    (0 : ℝ) < sigma →
    sigma ≤ (1 / 2 : ℝ) →
    let shift : Vec d := triadicCubeShift R;
    let B : CutoffSample d → ℝ := fun (eta : CutoffSample d) =>
    ∑' (n : ℕ), probeSharpWaveTailTunedBoundedLayer M R.scale (↑E : ℝ) k n eta;
    let V : CutoffSample d → ℝ := fun (eta : CutoffSample d) =>
    ∑' (n : ℕ), probeSharpWaveTailTunedRareLayer M R.scale (↑E : ℝ) k n eta;
    let C : ℝ := (↑d : ℝ) * probeMeanGoodWaveConst M;
    let bounded : CutoffSample d → ℝ := fun (omega : CutoffSample d) => C * B (translateCutoffSample shift omega);
    let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) => C * V (translateCutoffSample shift omega);
    (2 : ℕ) ≤ d →
    (0 : ℝ) ≤ C →
    (∀ (n : ℕ),
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTailSigma sigma))
    (probeSharpWaveTailTunedBoundedLayer M R.scale (↑E : ℝ) k n)
    (probeSharpWaveTailTunedBoundedLayerBound M (↑E : ℝ) sigma n)) →
    (∀ (n : ℕ),
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
    (gammaSigma (upperProfileTargetSigma sigma)) (probeSharpWaveTailTunedRareLayer M R.scale (↑E : ℝ) k n)
    (probeSharpWaveTailTunedRareLayerBound M (↑E : ℝ) sigma n)) →
    Measurable B →
    Measurable V →
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
    (gammaSigma (upperProfileTailSigma sigma))
    (fun (ω : CutoffSample d) =>
    ∑' (k_1 : ℕ), probeSharpWaveTailTunedBoundedLayer M R.scale (↑E : ℝ) k k_1 ω)
    (gammaTriangleConst (upperProfileTailSigma sigma) *
    (probeSharpWaveTailBoundedSumConst d * sigma⁻¹ ^ (2 : ℕ) *
    Real.exp (-(probeSharpWaveTailTunedRate d * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))))) →
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
    (gammaSigma (upperProfileTargetSigma sigma))
    (fun (ω : CutoffSample d) =>
    ∑' (k_1 : ℕ), probeSharpWaveTailTunedRareLayer M R.scale (↑E : ℝ) k k_1 ω)
    (gammaTriangleConst (upperProfileTargetSigma sigma) *
    (probeSharpWaveTailRareSumConst d * sigma⁻¹ ^ (2 : ℕ) *
    Real.exp (-(probeSharpWaveTailTunedRate d * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))))) →
    (0 : ℝ) ≤
    (Disorder.cstar M)⁻¹ * sigma⁻¹ ^ (2 : ℕ) *
    Real.exp (-(probeSharpWaveTailTunedRate d * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ∧
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
    (gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) bounded
    (probeSharpWaveTailTunedTraceScale M (↑E : ℝ) sigma) ∧
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
    (gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) rare
    (probeSharpWaveTailTunedTraceScale M (↑E : ℝ) sigma) ∧
    (∀ᵐ (eta : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
    Summable fun (n : ℕ) =>
    probeSharpWaveTailTunedBoundedLayer M R.scale (↑E : ℝ) k n eta) ∧
    ∀ᵐ (eta : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
    Summable fun (n : ℕ) => probeSharpWaveTailTunedRareLayer M R.scale (↑E : ℝ) k n eta := by
  intro d M k R E sigma hsigma0 hsigma shift B V C bounded rare hd hC0 hBterm hVterm hBmeas hVmeas hBcenter hVcenter
  have hpoly0 : 0 ≤ ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) *
      Real.exp (-(probeSharpWaveTailTunedRate d * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr
        (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le)
        (sq_nonneg sigma⁻¹)) (Real.exp_pos _).le
  have hBcoef : (d : ℝ) * probeMeanGoodWaveDimensionConst d *
      gammaTriangleConst (upperProfileTailSigma sigma) *
      probeSharpWaveTailBoundedSumConst d ≤ probeSharpWaveTailTunedTraceRawConst d := by
    refine (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (gammaTriangleConst_le_superposedFluxTriangleConst (by
          rw [upperProfileTailSigma, upperProfileSigma]
          have hden : 0 < 1 + sigma / 4 := by linarith
          rw [le_div_iff₀ hden]; nlinarith))
        (mul_nonneg (Nat.cast_nonneg d) (probeMeanGoodWaveDimensionConst_nonneg_local hd)))
      (probeSharpWaveTailBoundedSumConst_pos hd).le).trans ?_
    rw [probeSharpWaveTailTunedTraceRawConst]
    exact le_max_left _ _
  have hVcoef : (d : ℝ) * probeMeanGoodWaveDimensionConst d *
      gammaTriangleConst (upperProfileTargetSigma sigma) *
      probeSharpWaveTailRareSumConst d ≤ probeSharpWaveTailTunedTraceRawConst d := by
    refine (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (gammaTriangleConst_upperProfileTarget_le hsigma0 hsigma)
        (mul_nonneg (Nat.cast_nonneg d) (probeMeanGoodWaveDimensionConst_nonneg_local hd)))
      (probeSharpWaveTailRareSumConst_pos d).le).trans ?_
    rw [probeSharpWaveTailTunedTraceRawConst]
    exact le_max_right _ _
  have hBscale : C * (gammaTriangleConst (upperProfileTailSigma sigma) *
      (probeSharpWaveTailBoundedSumConst d * sigma⁻¹ ^ 2 *
        Real.exp (-(probeSharpWaveTailTunedRate d * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))))) ≤
      probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma := by
    dsimp only [C]
    rw [probeMeanGoodWaveConst_eq_dimension_mul_cstarInv]
    rw [probeSharpWaveTailTunedTraceScale]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hBcoef hpoly0)
    ring
  have hVscale : C * (gammaTriangleConst (upperProfileTargetSigma sigma) *
      (probeSharpWaveTailRareSumConst d * sigma⁻¹ ^ 2 *
        Real.exp (-(probeSharpWaveTailTunedRate d * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))))) ≤
      probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma := by
    dsimp only [C]
    rw [probeMeanGoodWaveConst_eq_dimension_mul_cstarInv]
    rw [probeSharpWaveTailTunedTraceScale]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hVcoef hpoly0)
    ring
  have hBtarget := HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
    (upperProfileTargetSigma_le_tailSigma hsigma0 hsigma) hBcenter
  have hBOrlicz : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3)) bounded
      (probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma) := by
    have h := Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift (hBmeas.const_mul C) (hBtarget.const_mul hC0)
    have h' : IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 3)) bounded
        (C * (gammaTriangleConst (upperProfileTailSigma sigma) *
          (probeSharpWaveTailBoundedSumConst d * sigma⁻¹ ^ 2 *
            Real.exp (-(probeSharpWaveTailTunedRate d *
              ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))))) := by
      simpa only [B, bounded, upperProfileTargetSigma] using h
    exact h'.mono_scale hBscale
  have hVOrlicz : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3)) rare
      (probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma) := by
    have h := Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift (hVmeas.const_mul C) (hVcenter.const_mul hC0)
    have h' : IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 3)) rare
        (C * (gammaTriangleConst (upperProfileTargetSigma sigma) *
          (probeSharpWaveTailRareSumConst d * sigma⁻¹ ^ 2 *
            Real.exp (-(probeSharpWaveTailTunedRate d *
              ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))))) := by
      simpa only [V, rare, upperProfileTargetSigma] using h
    exact h'.mono_scale hVscale
  have hBae : ∀ᵐ eta ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => probeSharpWaveTailTunedBoundedLayer
        M R.scale (E : ℝ) k n eta :=
    Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      (upperProfileTailSigma_pos hsigma0 hsigma)
      (fun n eta => probeSharpWaveTailTunedBoundedLayer_nonneg M R.scale (E : ℝ) k n eta)
      (fun n => (measurable_probeSharpWaveTailTunedBoundedLayer
        M R.scale (E : ℝ) k n).aemeasurable)
      (fun n => probeSharpWaveTailTunedBoundedLayerBound_pos M (E : ℝ) hsigma0 n)
      (summable_probeSharpWaveTailTunedBoundedLayerBound M (E : ℝ) sigma) hBterm
  have hVae : ∀ᵐ eta ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => probeSharpWaveTailTunedRareLayer
        M R.scale (E : ℝ) k n eta :=
    Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      (upperProfileTargetSigma_pos hsigma0 hsigma)
      (fun n eta => probeSharpWaveTailTunedRareLayer_nonneg M R.scale (E : ℝ) k n eta)
      (fun n => (measurable_probeSharpWaveTailTunedRareLayer
        M R.scale (E : ℝ) k n).aemeasurable)
      (fun n => probeSharpWaveTailTunedRareLayerBound_pos M (E : ℝ) hsigma0 n)
      (summable_probeSharpWaveTailTunedRareLayerBound M (E : ℝ) sigma) hVterm
  exact ⟨hpoly0, hBOrlicz, hVOrlicz, hBae, hVae⟩

theorem exists_good_wave_tail_tuned_finite_trace_split
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : probeSharpWaveTailTunedOutputConst d ≤ Cup) :
    ∃ bounded rare : CutoffSample d → ℝ,
      (∀ omega, 0 ≤ bounded omega) ∧ Measurable bounded ∧
      (∀ omega, 0 ≤ rare omega) ∧ Measurable rare ∧
      (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        (∑ j : Fin d, ∑' n : ℕ,
          probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
            (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
              (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
            (translateCutoffSample (triadicCubeShift R) omega)) ≤
          bounded omega + rare omega) ∧
      (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
            (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
              (probeSharpLayerAnchor R.scale bfaProfileB
                (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
            (translateCutoffSample (triadicCubeShift R) omega))) =
          ENNReal.ofReal (∑ j : Fin d, ∑' n : ℕ,
            probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) ∧
      (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
            (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
              (probeSharpLayerAnchor R.scale bfaProfileB
                (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
            (translateCutoffSample (triadicCubeShift R) omega))) ≤
          ENNReal.ofReal (bounded omega) + ENNReal.ofReal (rare omega)) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 3)) bounded
        (probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 3)) rare
        (probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma) ∧
      0 ≤ probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma ∧
      probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma ≤
        (Real.exp (-(Cup⁻¹ *
          ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8 := by
  let shift : Vec d := triadicCubeShift R
  let B : CutoffSample d → ℝ := fun eta => ∑' n,
    probeSharpWaveTailTunedBoundedLayer M R.scale (E : ℝ) k n eta
  let V : CutoffSample d → ℝ := fun eta => ∑' n,
    probeSharpWaveTailTunedRareLayer M R.scale (E : ℝ) k n eta
  let C : ℝ := (d : ℝ) * probeMeanGoodWaveConst M
  let bounded : CutoffSample d → ℝ := fun omega => C * B (translateCutoffSample shift omega)
  let rare : CutoffSample d → ℝ := fun omega => C * V (translateCutoffSample shift omega)
  have hd := M.shellPrefix.dimension
  have hchoices := probeSharpWaveTailTuned_output_choices hd houtput
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 hchoices.1)).trans
        ((le_max_left _ _).trans hmax)
  have hC0 : 0 ≤ C := mul_nonneg (Nat.cast_nonneg d)
    (probeMeanGoodWaveConst_nonneg hd M)
  have hBterm : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTailSigma sigma))
      (probeSharpWaveTailTunedBoundedLayer M R.scale (E : ℝ) k n)
      (probeSharpWaveTailTunedBoundedLayerBound M (E : ℝ) sigma n) := fun n =>
    (isBigOWith_upperProfileTail_probeSharpWaveTailTunedBoundedLayer
      M hR hstate hsigma0 hsigma hmaxAux hEgamma n).mono_scale
        (probeSharpWaveTailTunedBoundedLayerScale_le
          M R.scale hsigma0 hsigma k n)
  have hVterm : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpWaveTailTunedRareLayer M R.scale (E : ℝ) k n)
      (probeSharpWaveTailTunedRareLayerBound M (E : ℝ) sigma n) := fun n =>
    (isBigOWith_upperProfileTarget_probeSharpWaveTailTunedRareLayer
      M hR hstate hsigma0 hsigma hmaxAux hEgamma n).mono_scale
        (probeSharpWaveTailTunedRareLayerScale_le
          M R.scale E.property hsigma0 hsigma k n)
  have hBmeas : Measurable B := by
    have hnn := (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (measurable_probeSharpWaveTailTunedBoundedLayer
        M R.scale (E : ℝ) k n).real_toNNReal).coe_nnreal_real
    convert hnn using 1
    funext eta
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by rw [Real.toNNReal_of_nonneg
      (probeSharpWaveTailTunedBoundedLayer_nonneg M R.scale (E : ℝ) k n eta)]; rfl
  have hVmeas : Measurable V := by
    have hnn := (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (measurable_probeSharpWaveTailTunedRareLayer
        M R.scale (E : ℝ) k n).real_toNNReal).coe_nnreal_real
    convert hnn using 1
    funext eta
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by rw [Real.toNNReal_of_nonneg
      (probeSharpWaveTailTunedRareLayer_nonneg M R.scale (E : ℝ) k n eta)]; rfl
  have hBcenter := Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
    (upperProfileTailSigma_pos hsigma0 hsigma)
    (fun n eta => probeSharpWaveTailTunedBoundedLayer_nonneg M R.scale (E : ℝ) k n eta)
    (fun n => measurable_probeSharpWaveTailTunedBoundedLayer M R.scale (E : ℝ) k n)
    (fun n => probeSharpWaveTailTunedBoundedLayerBound_pos M (E : ℝ) hsigma0 n)
    (summable_probeSharpWaveTailTunedBoundedLayerBound M (E : ℝ) sigma)
    hBterm (tsum_probeSharpWaveTailTunedBoundedLayerBound_eq M (E : ℝ) sigma).le
  have hVcenter := Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
    (upperProfileTargetSigma_pos hsigma0 hsigma)
    (fun n eta => probeSharpWaveTailTunedRareLayer_nonneg M R.scale (E : ℝ) k n eta)
    (fun n => measurable_probeSharpWaveTailTunedRareLayer M R.scale (E : ℝ) k n)
    (fun n => probeSharpWaveTailTunedRareLayerBound_pos M (E : ℝ) hsigma0 n)
    (summable_probeSharpWaveTailTunedRareLayerBound M (E : ℝ) sigma)
    hVterm (tsum_probeSharpWaveTailTunedRareLayerBound_eq M (E : ℝ) sigma).le
  obtain ⟨hpoly0, hBOrlicz, hVOrlicz, hBae, hVae⟩ :=
    @upperWaveTailE12Consumption_momentBounds1 (d) (M) (k) (R) (E) (sigma) (hsigma0) (hsigma) (hd)
      (hC0) (hBterm) (hVterm) (hBmeas) (hVmeas) (hBcenter) (hVcenter)
  have hBtranslated : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => probeSharpWaveTailTunedBoundedLayer M R.scale (E : ℝ) k n
        (translateCutoffSample shift omega) := by
    refine MeasureTheory.ae_of_ae_map
      (p := fun eta => Summable fun n => probeSharpWaveTailTunedBoundedLayer
        M R.scale (E : ℝ) k n eta)
      (measurable_translateCutoffSample shift).aemeasurable ?_
    rw [map_translateCutoffSample_cutoffSampleLaw]
    exact hBae
  have hVtranslated : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => probeSharpWaveTailTunedRareLayer M R.scale (E : ℝ) k n
        (translateCutoffSample shift omega) := by
    refine MeasureTheory.ae_of_ae_map
      (p := fun eta => Summable fun n => probeSharpWaveTailTunedRareLayer
        M R.scale (E : ℝ) k n eta)
      (measurable_translateCutoffSample shift).aemeasurable ?_
    rw [map_translateCutoffSample_cutoffSampleLaw]
    exact hVae
  have hbounded0 : ∀ omega, 0 ≤ bounded omega := fun omega =>
    mul_nonneg hC0 (tsum_nonneg fun n => probeSharpWaveTailTunedBoundedLayer_nonneg
      M R.scale (E : ℝ) k n (translateCutoffSample shift omega))
  have hrare0 : ∀ omega, 0 ≤ rare omega := fun omega =>
    mul_nonneg hC0 (tsum_nonneg fun n => probeSharpWaveTailTunedRareLayer_nonneg
      M R.scale (E : ℝ) k n (translateCutoffSample shift omega))
  let L : Fin d → ℕ → CutoffSample d → ℝ := fun j n omega =>
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
      (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
        (probeSharpLayerAnchor R.scale bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
      (translateCutoffSample shift omega)
  let traceR : CutoffSample d → ℝ := fun omega => ∑ j : Fin d, ∑' n, L j n omega
  let traceE : CutoffSample d → ENNReal := fun omega =>
    ∑ j : Fin d, ∑' n, ENNReal.ofReal (L j n omega)
  have hbridges := @waveTail_trace_ofReal_domination (d) (M) (m) (k) (R) (hR) (E) (hstate) (sigma)
    (hsigma0) (hsigma) (hEgamma) (hd) (hmaxAux) (hBtranslated) (hVtranslated) (hbounded0) (hrare0)
  have hpoint := hbridges.mono fun _ h => h.1
  have heq := hbridges.mono fun _ h => h.2.1
  have henn := hbridges.mono fun _ h => h.2.2
  have hscale0 : 0 ≤ probeSharpWaveTailTunedTraceScale M (E : ℝ) sigma := by
    rw [probeSharpWaveTailTunedTraceScale]
    exact mul_nonneg (probeSharpWaveTailTunedTraceRawConst_nonneg hd) hpoly0
  exact ⟨bounded, rare, hbounded0,
    (hBmeas.comp (measurable_translateCutoffSample shift)).const_mul C,
    hrare0, (hVmeas.comp (measurable_translateCutoffSample shift)).const_mul C,
    hpoint, heq, henn, hBOrlicz, hVOrlicz, hscale0,
    probeSharpWaveTailTunedTraceScale_le_frozen_pow M hsigma0 hsigma hmax
      hEgamma houtput⟩
end
end Algsuperdiff.Section3.Provider.CoarseEllipticity
