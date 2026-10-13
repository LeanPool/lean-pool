/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# UpperCollarBandMeanTunedConsumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Literal consumption of the collar copy of the tuned band mean

This file sums the literal ninth named summand over Whitney layers at one
translated strict descendant.  The pointwise layer estimate is the
cap/mass-interpolated estimate from `UpperCollarBandMeanTunedProfile`; the only
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

/-- The real-valued literal collar band-mean coordinate lane at one translated
strict descendant. -/
def probeSharpFramedCollarBandMeanTunedCoordinateLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (omega : CutoffSample d) : ℝ :=
  ∑' n : ℕ,
    probeSharpFramedCollarWavePart M R.scale E bfaProfileB
      (collarBandMeanDepth M E) n (m - 1) (basisVec j)
      (superposedGradConst d)
      (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
        (collarBandMeanDepth M E) ^ 2)
      (translateCutoffSample (triadicCubeShift R) omega)

/-- The same literal lane in the shape used by the framed envelope. -/
def probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (omega : CutoffSample d) : ENNReal :=
  ∑' n : ℕ, ENNReal.ofReal
    (probeSharpFramedCollarWavePart M R.scale E bfaProfileB
      (collarBandMeanDepth M E) n (m - 1) (basisVec j)
      (superposedGradConst d)
      (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
        (collarBandMeanDepth M E) ^ 2)
      (translateCutoffSample (triadicCubeShift R) omega))

/-- The exact hsep-power scale furnished by `e.hsep.tails`. -/
def probeSharpCollarBandMeanTunedPowerScale
    (M : ABKModel d) (sigma : ℝ) : ℝ :=
  hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB

/-- The deterministic Whitney sum times the exact collar-power scale. -/
def probeSharpCollarBandMeanTunedCoordinateScale
    (M : ABKModel d) (E sigma : ℝ) : ℝ :=
  (∑' n : ℕ, probeSharpCollarBandMeanTunedLayerScale M E n) *
    probeSharpCollarBandMeanTunedPowerScale M sigma

/-- The pointwise majorant left after Whitney summation. -/
def probeSharpCollarBandMeanTunedCoordinateMajorant
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ)
    (omega : CutoffSample d) : ℝ :=
  (∑' n : ℕ, probeSharpCollarBandMeanTunedLayerScale M E n) *
    slstarPowerTerm M R.scale E bfaProfileB M.gamma
      (translateCutoffSample (triadicCubeShift R) omega)

/-- The literal finite-coordinate collar band-mean trace at one strict
descendant. -/
def probeSharpFramedCollarBandMeanTunedTraceLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (omega : CutoffSample d) : ℝ :=
  ∑ j : Fin d,
    probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j omega

/-- The literal finite-coordinate trace in the envelope's shape. -/
def probeSharpFramedCollarBandMeanTunedTraceENNRealLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (omega : CutoffSample d) : ENNReal :=
  ∑ j : Fin d,
    probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane M m R E j omega

/-- The exact finite-coordinate trace scale. -/
def probeSharpCollarBandMeanTunedTraceScale
    (d : ℕ) (M : ABKModel d) (E sigma : ℝ) : ℝ :=
  (d : ℝ) * probeSharpCollarBandMeanTunedCoordinateScale M E sigma

private theorem probeSharpFramedCollarBandMeanLayer_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (root : ℤ) (E : ℝ)
    (k₀ n : ℕ) (i : ℤ) (j : Fin d) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
      (basisVec j) (superposedGradConst d)
      (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2)
      omega := by
  exact probeSharpFramedCollarWavePart_nonneg hd M root E bfaProfileB k₀ n i
    (basisVec j) (superposedGradConst d) (fun _eta => sq_nonneg _) omega

private theorem measurable_probeSharpFramedCollarBandMeanLayer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ)
    (i : ℤ) (j : Fin d) :
    Measurable fun omega : CutoffSample d =>
      probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
        (basisVec j) (superposedGradConst d)
        (fun _eta =>
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2)
        omega := by
  have hfun :
      (fun omega : CutoffSample d =>
        probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
          (basisVec j) (superposedGradConst d)
          (fun _eta =>
            waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2)
          omega) =
        fun omega =>
          (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
            (5 * (d : ℝ) ^ 2 *
              waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2)) *
          probeSharpCollarBandMeanLayerCore
            M root E k₀ n i (superposedGradConst d) omega := by
    funext omega
    exact probeSharpFramedCollarWavePart_bandMean_eq
      M root E k₀ n i j (superposedGradConst d) omega
  rw [hfun]
  exact measurable_const.mul
    (measurable_probeSharpCollarBandMeanLayerCore
      M root E k₀ n i (superposedGradConst d))

theorem probeSharpCollarBandMeanTunedPowerScale_nonneg
    (M : ABKModel d) (sigma : ℝ) :
    0 ≤ probeSharpCollarBandMeanTunedPowerScale M sigma := by
  rw [probeSharpCollarBandMeanTunedPowerScale]
  exact Real.rpow_nonneg (hsepAmplitude_pos _ _).le _


/-- The literal real Whitney family is summable at every sample point. -/
theorem summable_probeSharpFramedCollarBandMeanTunedCoordinateLayer
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : ℝ} (hE : 1 ≤ E)
    (hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) (omega : CutoffSample d) :
    Summable fun n : ℕ =>
      probeSharpFramedCollarWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M E) ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega) := by
  let P := slstarPowerTerm M R.scale E bfaProfileB M.gamma
    (translateCutoffSample (triadicCubeShift R) omega)
  have hmajor : Summable fun n : ℕ =>
      probeSharpCollarBandMeanTunedLayerScale M E n * P :=
    (summable_probeSharpCollarBandMeanTunedLayerScale M E).mul_right P
  exact Summable.of_nonneg_of_le
    (fun n => probeSharpFramedCollarBandMeanLayer_nonneg hd M R.scale E
      (collarBandMeanDepth M E) n (m - 1) j
      (translateCutoffSample (triadicCubeShift R) omega))
    (fun n => probeSharpFramedCollarWavePart_bandMeanTuned_le
      hd M hR hE hcstarE hEgamma n j
      (translateCutoffSample (triadicCubeShift R) omega))
    hmajor

theorem probeSharpFramedCollarBandMeanTunedCoordinateLane_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (E : ℝ) (j : Fin d) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j omega := by
  rw [probeSharpFramedCollarBandMeanTunedCoordinateLane]
  exact tsum_nonneg fun n =>
    probeSharpFramedCollarBandMeanLayer_nonneg hd M R.scale E
      (collarBandMeanDepth M E) n (m - 1) j
      (translateCutoffSample (triadicCubeShift R) omega)

theorem measurable_probeSharpFramedCollarBandMeanTunedCoordinateLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) :
    Measurable (probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j) := by
  have hnn : Measurable (fun omega : CutoffSample d => ∑' n : ℕ,
      (probeSharpFramedCollarWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1)
        (basisVec j) (superposedGradConst d)
        (fun _eta =>
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
            (collarBandMeanDepth M E) ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega)).toNNReal) :=
    Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      ((measurable_probeSharpFramedCollarBandMeanLayer M R.scale E
          (collarBandMeanDepth M E) n (m - 1) j).comp
        (measurable_translateCutoffSample (triadicCubeShift R))).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [probeSharpFramedCollarBandMeanTunedCoordinateLane, NNReal.coe_tsum]
  apply tsum_congr
  intro n
  rw [Real.toNNReal_of_nonneg
    (probeSharpFramedCollarBandMeanLayer_nonneg M.shellPrefix.dimension M
      R.scale E (collarBandMeanDepth M E) n (m - 1) j
      (translateCutoffSample (triadicCubeShift R) omega))]
  rfl

theorem probeSharpFramedCollarBandMeanTunedCoordinateLane_le_majorant
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : ℝ} (hE : 1 ≤ E)
    (hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j omega ≤
      probeSharpCollarBandMeanTunedCoordinateMajorant M R E omega := by
  let P := slstarPowerTerm M R.scale E bfaProfileB M.gamma
    (translateCutoffSample (triadicCubeShift R) omega)
  have hleft := summable_probeSharpFramedCollarBandMeanTunedCoordinateLayer
    hd M hR hE hcstarE hEgamma j omega
  have hright : Summable fun n : ℕ =>
      probeSharpCollarBandMeanTunedLayerScale M E n * P :=
    (summable_probeSharpCollarBandMeanTunedLayerScale M E).mul_right P
  rw [probeSharpFramedCollarBandMeanTunedCoordinateLane,
    probeSharpCollarBandMeanTunedCoordinateMajorant]
  calc
    _ ≤ ∑' n : ℕ, probeSharpCollarBandMeanTunedLayerScale M E n * P :=
      Summable.tsum_le_tsum
        (fun n => probeSharpFramedCollarWavePart_bandMeanTuned_le
          hd M hR hE hcstarE hEgamma n j
          (translateCutoffSample (triadicCubeShift R) omega))
        hleft hright
    _ = (∑' n : ℕ, probeSharpCollarBandMeanTunedLayerScale M E n) * P := by
      rw [tsum_mul_right]

theorem probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane_eq
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : ℝ} (hE : 1 ≤ E)
    (hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane M m R E j omega =
      ENNReal.ofReal
        (probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j omega) := by
  rw [probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane,
    probeSharpFramedCollarBandMeanTunedCoordinateLane]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => probeSharpFramedCollarBandMeanLayer_nonneg hd M R.scale E
      (collarBandMeanDepth M E) n (m - 1) j
      (translateCutoffSample (triadicCubeShift R) omega))
    (summable_probeSharpFramedCollarBandMeanTunedCoordinateLayer
      hd M hR hE hcstarE hEgamma j omega)).symm

/-- The frozen gates price the exact collar hsep power at the target upper
profile exponent. -/
theorem isBigOWith_upperProfileTarget_slstarPowerTerm_tuned
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
      (probeSharpCollarBandMeanTunedPowerScale M sigma) := by
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
  simpa only [probeSharpCollarBandMeanTunedPowerScale] using hweakened

private theorem measurable_slstarPowerTerm
    (M : ABKModel d) (root : ℤ) (E b gam : ℝ) :
    Measurable (slstarPowerTerm M root E b gam) := by
  simpa only [slstarPowerTerm] using!
    measurable_comp_hsep M root E b fun hs : ℕ =>
      (3 : ℝ) ^ ((gam + 2 * b) * (hs : ℝ))


theorem isBigOWith_upperProfileTarget_probeSharpCollarBandMeanTunedCoordinateMajorant
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpCollarBandMeanTunedCoordinateMajorant M R (E : ℝ))
      (probeSharpCollarBandMeanTunedCoordinateScale M (E : ℝ) sigma) := by
  have hpower := isBigOWith_upperProfileTarget_slstarPowerTerm_tuned
    M hR hS hsigma0 hsigma hmax hEgamma
  have htranslated :=
    Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M (triadicCubeShift R)
      (measurable_slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma)
      hpower
  have hsum0 : 0 ≤
      ∑' n : ℕ, probeSharpCollarBandMeanTunedLayerScale M (E : ℝ) n :=
    tsum_nonneg fun n =>
      probeSharpCollarBandMeanTunedLayerScale_nonneg hd M (E : ℝ) n
  have hscaled := htranslated.const_mul hsum0
  simpa only [probeSharpCollarBandMeanTunedCoordinateMajorant,
    probeSharpCollarBandMeanTunedCoordinateScale] using! hscaled

/-- The actual translated coordinate lane inherits the target exponent from
its proved pointwise majorant. -/
theorem isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedCoordinateLane
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarBandMeanTunedCoordinateLane
        M m R (E : ℝ) j)
      (probeSharpCollarBandMeanTunedCoordinateScale M (E : ℝ) sigma) := by
  have hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    (le_max_right _ _).trans hmax
  exact isBigOWith_gammaSigma_of_le
    (fun omega => probeSharpFramedCollarBandMeanTunedCoordinateLane_le_majorant
      hd M hR E.property hcstarE hEgamma j omega)
    (isBigOWith_upperProfileTarget_probeSharpCollarBandMeanTunedCoordinateMajorant
      hd M hR hS hsigma0 hsigma hmax hEgamma)

theorem probeSharpFramedCollarBandMeanTunedCoordinateLane_eq
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j j' : Fin d) :
    probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j =
      probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j' := by
  funext omega
  rw [probeSharpFramedCollarBandMeanTunedCoordinateLane,
    probeSharpFramedCollarBandMeanTunedCoordinateLane]
  apply tsum_congr
  intro n
  simp only [probeSharpFramedCollarWavePart, vecNormSq_basisVec]

theorem probeSharpFramedCollarBandMeanTunedTraceLane_eq_dimension_mul
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarBandMeanTunedTraceLane M m R E omega =
      (d : ℝ) *
        probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j omega := by
  rw [probeSharpFramedCollarBandMeanTunedTraceLane]
  have hall : ∀ j' : Fin d,
      probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j' omega =
        probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j omega :=
    fun j' => congrFun
      (probeSharpFramedCollarBandMeanTunedCoordinateLane_eq M m R E j' j) omega
  simp_rw [hall]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem probeSharpFramedCollarBandMeanTunedTraceLane_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (E : ℝ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarBandMeanTunedTraceLane M m R E omega := by
  rw [probeSharpFramedCollarBandMeanTunedTraceLane]
  exact Finset.sum_nonneg fun j _ =>
    probeSharpFramedCollarBandMeanTunedCoordinateLane_nonneg hd M m R E j omega

theorem measurable_probeSharpFramedCollarBandMeanTunedTraceLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ) :
    Measurable (probeSharpFramedCollarBandMeanTunedTraceLane M m R E) := by
  change Measurable fun omega : CutoffSample d =>
    ∑ j : Fin d,
      probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j omega
  exact Finset.measurable_fun_sum Finset.univ fun j _ =>
    measurable_probeSharpFramedCollarBandMeanTunedCoordinateLane M m R E j


theorem isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedTraceLane
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarBandMeanTunedTraceLane M m R (E : ℝ))
      (probeSharpCollarBandMeanTunedTraceScale d M (E : ℝ) sigma) := by
  let j₀ : Fin d :=
    ⟨0, Nat.zero_lt_of_lt M.shellPrefix.dimension⟩
  have hcoord :=
    isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedCoordinateLane
      hd M hR hS hsigma0 hsigma hmax hEgamma j₀
  have hscaled := hcoord.const_mul (Nat.cast_nonneg d)
  have hlane : probeSharpFramedCollarBandMeanTunedTraceLane M m R (E : ℝ) =
      fun omega => (d : ℝ) *
        probeSharpFramedCollarBandMeanTunedCoordinateLane
          M m R (E : ℝ) j₀ omega := by
    funext omega
    exact probeSharpFramedCollarBandMeanTunedTraceLane_eq_dimension_mul
      M m R (E : ℝ) j₀ omega
  rw [hlane]
  simpa only [probeSharpCollarBandMeanTunedTraceScale] using hscaled

theorem probeSharpFramedCollarBandMeanTunedTraceENNRealLane_eq
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : ℝ} (hE : 1 ≤ E)
    (hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (omega : CutoffSample d) :
    probeSharpFramedCollarBandMeanTunedTraceENNRealLane M m R E omega =
      ENNReal.ofReal
        (probeSharpFramedCollarBandMeanTunedTraceLane M m R E omega) := by
  rw [probeSharpFramedCollarBandMeanTunedTraceENNRealLane,
    probeSharpFramedCollarBandMeanTunedTraceLane,
    ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      probeSharpFramedCollarBandMeanTunedCoordinateLane_nonneg
        hd M m R E j omega)]
  apply Finset.sum_congr rfl
  intro j _
  exact probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane_eq
    hd M hR hE hcstarE hEgamma j omega

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
