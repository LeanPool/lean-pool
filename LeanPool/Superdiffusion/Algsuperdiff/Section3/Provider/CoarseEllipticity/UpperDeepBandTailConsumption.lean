/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperDeepBandTailOrdinaryLane
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperDeepBandTailRareProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedAbsorption

/-!
# UpperDeepBandTailConsumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact consumption of the translated framed deep-band-tail lane
This file treats the good-cell and collar deep-tail summands of the framed
descendant envelope, preserving the descendant scale and translation.  It does
not assert root aggregation, the complete envelope, or source-node status.
-/
namespace Algsuperdiff.Section3.Provider.CoarseEllipticity
open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
noncomputable section
variable {d : ℕ}
variable {d : ℕ}
/- The literal tenth named summand is the exact centered deep-band square
times the collar/frame core.  This estimate keeps the tuned cap-growth factor
and the centered tail itself; no probabilistic scale is weakened here. -/
private theorem collarDeepTail_layer_le
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M E) n)
          (collarBandMeanDepth M E) (collarBandMeanDepth M E) eta ^ 2)
        omega ≤
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        (5 * (d : ℝ) ^ 2) *
        ((4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n)) *
        (slstarPowerTerm M R.scale E bfaProfileB M.gamma omega *
          probeDeepBandGaugedTail M (originCube d R.scale)
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M E) n)
            (collarBandMeanDepth M E) (collarBandMeanDepth M E) omega ^ 2) := by
  let ell := probeSharpLayerAnchor R.scale bfaProfileB
    (collarBandMeanDepth M E) n
  let A := probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
    (5 * (d : ℝ) ^ 2)
  let T := probeDeepBandGaugedTail M (originCube d R.scale) ell
    (collarBandMeanDepth M E) (collarBandMeanDepth M E) omega ^ 2
  let C := probeSharpCollarBandMeanLayerCore M R.scale E
    (collarBandMeanDepth M E) n (m - 1) (superposedGradConst d) omega
  let K := (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n
  let P := slstarPowerTerm M R.scale E bfaProfileB M.gamma omega
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
        (vecNormSq_nonneg (basisVec j)))
      (by positivity)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact probeSharpCollarBandMeanLayerCore_nonneg M R.scale E
      (collarBandMeanDepth M E) n (m - 1) (superposedGradConst d) omega
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (sq_nonneg _))
              (probeSharpCollarBandMeanCapQuarter_nonneg
                M E (collarBandMeanDepth M E)))
            (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _))
      (pow_nonneg whitneyDecayRatio_nonneg n)
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact slstarPowerTerm_nonneg M R.scale E bfaProfileB M.gamma omega
  have hcore : C ≤ K * P := by
    dsimp only [C, K, P]
    calc
      _ ≤ (4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ)) *
          slstarPowerTerm M R.scale E bfaProfileB M.gamma omega *
          whitneyDecayRatio ^ n :=
        probeSharpCollarBandMeanLayerCore_le_atDepth
          M hR E (collarBandMeanDepth M E) n omega
      _ = _ := by ring
  have heq :
      probeSharpFramedCollarWavePart M R.scale E bfaProfileB
          (collarBandMeanDepth M E) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M E) n)
            (collarBandMeanDepth M E) (collarBandMeanDepth M E) eta ^ 2)
          omega = A * T * C := by
    simp only [probeSharpFramedCollarWavePart,
      probeSharpCollarBandMeanLayerCore, A, T, C, ell]
    ring
  rw [heq]
  calc
    A * T * C ≤ A * T * (K * P) :=
      mul_le_mul_of_nonneg_left hcore (mul_nonneg hA hT)
    _ = _ := by
      simp only [A, K, P, T, ell]
      ring
private theorem probeDeepBandGaugedFluct_eq_closed_s33
    (M : ABKModel d) (ell : ℤ) (k₀ g₀ : ℕ) :
    probeDeepBandGaugedFluct M ell k₀ g₀ =
      (HCPolySupport.IndependentSums.gammaTriangleConst 2 *
          (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)) *
        Real.sqrt M.gamma * probeBandUnitGain d ^ g₀ *
        (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) := by
  have hanchor :
      (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (((ell + (k₀ : ℤ)) : ℤ) : ℝ)) =
        (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [probeDeepBandGaugedFluct, probeDeepBandRawFluct]
  rw [← hanchor]
  ring
private theorem probeDeepBandGaugedFluct_sq_eq_closed_s33
    (M : ABKModel d) (ell : ℤ) (k₀ g₀ : ℕ) :
    probeDeepBandGaugedFluct M ell k₀ g₀ ^ 2 =
      (HCPolySupport.IndependentSums.gammaTriangleConst 2 *
          (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)) ^ 2 *
        M.gamma * (probeBandUnitGain d ^ g₀) ^ 2 *
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
  rw [probeDeepBandGaugedFluct_eq_closed_s33, mul_pow, mul_pow, mul_pow,
    hsqrt, hpow]
/- The exact grouped-tail scale has a dimension-only multiple of `gamma`,
uniformly in the tuned depth.  The potentially dangerous
`3^(2 gamma k₀)` is bounded by `81`: `gamma k₀ ≤ 2` follows directly
from the depth ceiling, `E ≥ 1`, and the frozen fifth-root gate. -/
private theorem tunedDeepTailFluct_sq_le
    (M : ABKModel d) (root : ℤ) {E : ℝ} (hE : 1 ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) (n : ℕ) :
    let k₀ := collarBandMeanDepth M E
    let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
    probeDeepBandGaugedFluct M ell k₀
        (probeSharpLayerGap bfaProfileB n) ^ 2 ≤
      (HCPolySupport.IndependentSums.gammaTriangleConst 2 *
          (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)) ^ 2 *
        M.gamma * 81 := by
  dsimp only
  let c := collarBandMeanDepthCoeff d
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  let g₀ := probeSharpLayerGap bfaProfileB n
  let q := probeBandUnitGain d
  let A := HCPolySupport.IndependentSums.gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
  have hgamma1 : M.gamma ≤ 1 :=
    gamma_le_one_of_le_rpow_neg_fifth hE M.shellPrefix.gamma_pos hEgamma
  have ht : 0 ≤ c * (E ^ 2)⁻¹ * M.gamma⁻¹ := by
    exact mul_nonneg
      (mul_nonneg (collarBandMeanDepthCoeff_pos d).le
        (inv_nonneg.mpr (sq_nonneg E)))
      (inv_nonneg.mpr M.shellPrefix.gamma_pos.le)
  have hdepth := waveBandDepth_spec
    (c := c) (E := E) M.shellPrefix.gamma_pos ht
  have hEinvSq : (E ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hE)
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    exact collarBandMeanDepthCoeff_le_one d
  have hc0 : 0 ≤ c := (collarBandMeanDepthCoeff_pos d).le
  have hcEinv : c * (E ^ 2)⁻¹ ≤ 1 := by
    calc
      c * (E ^ 2)⁻¹ ≤ 1 * 1 :=
        mul_le_mul hc1 hEinvSq (inv_nonneg.mpr (sq_nonneg E)) (by norm_num)
      _ = 1 := by ring
  have hgk : M.gamma * (k₀ : ℝ) ≤ 2 := by
    have hdepth' : M.gamma * (k₀ : ℝ) ≤ c * (E ^ 2)⁻¹ + M.gamma := hdepth
    linarith only [hdepth', hcEinv, hgamma1]
  have hbandPow : (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) ≤ 81 := by
    calc
      (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) ≤
          (3 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 81 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        norm_num
  have hq0 : 0 ≤ q := by dsimp only [q]; exact probeBandUnitGain_nonneg d
  have hq1 : q ≤ 1 := by
    exact (probeBandUnitGain_le M.shellPrefix.dimension).trans (by norm_num)
  have hqpowSq : (q ^ g₀) ^ 2 ≤ 1 := by
    have hqpow : q ^ g₀ ≤ 1 := pow_le_one₀ hq0 hq1
    exact pow_le_one₀ (pow_nonneg hq0 g₀) hqpow
  have hA0 : 0 ≤ A ^ 2 * M.gamma := by
    exact mul_nonneg (sq_nonneg A) M.shellPrefix.gamma_pos.le
  rw [probeDeepBandGaugedFluct_sq_eq_closed_s33]
  change A ^ 2 * M.gamma * (q ^ g₀) ^ 2 *
      (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) ≤ A ^ 2 * M.gamma * 81
  calc
    A ^ 2 * M.gamma * (q ^ g₀) ^ 2 *
        (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) ≤
      A ^ 2 * M.gamma * 1 * 81 := by
        gcongr
    _ = A ^ 2 * M.gamma * 81 := by ring
/- One literal translated collar deep-tail layer has the target upper-profile
exponent.  Its scale retains the exact grouped-tail fluctuation and the exact
tuned cap-growth coefficient. -/
private theorem collarDeepTail_layerAmplitude_nonnegative :
    ∀ {d : ℕ} (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (n : ℕ) (j : Fin d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let D : ℝ :=
        probeMeanGoodWaveConst M * vecNormSq (basisVec j) * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
          ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ *
                  probeSharpCollarBandMeanMassQuarterConst d *
                (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ)) *
              (3 : ℝ) ^ (1 / 16 : ℝ) *
            whitneyDecayRatio ^ n);
      (0 : ℝ) ≤ D := by
  intro d M E n j k₀ D
  dsimp only [D]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
        (vecNormSq_nonneg (basisVec j)))
      (by positivity))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (sq_nonneg _))
              (probeSharpCollarBandMeanCapQuarter_nonneg M (E : ℝ) k₀))
            (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _))
      (pow_nonneg whitneyDecayRatio_nonneg n))

private theorem collarDeepTail_layer_isBigOWith
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hCup : max (profileAuxiliaryConst d)
      (collarBandMeanDepthThreshold d) ≤ Cup)
    (n : ℕ) (j : Fin d) :
    let k₀ := collarBandMeanDepth M (E : ℝ)
    let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
    let D :=
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        (5 * (d : ℝ) ^ 2) *
        ((4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n))
    let alpha := upperProfileBaseSigma sigma /
      ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
    let AP := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
      bfaPower M.gamma bfaProfileB
    let AT := probeDeepBandGaugedFluct M ell k₀
      (probeSharpLayerGap bfaProfileB n) ^ 2
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega =>
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
            ell k₀ k₀ eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega))
      (D * (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AT)) := by
  dsimp only
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let g₀ := probeSharpLayerGap bfaProfileB n
  let D : ℝ :=
    probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
      (5 * (d : ℝ) ^ 2) *
      ((4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n)
  let P : CutoffSample d → ℝ := fun omega =>
    slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
      (translateCutoffSample (triadicCubeShift R) omega)
  let T : CutoffSample d → ℝ := fun omega =>
    probeDeepBandGaugedTail M (originCube d R.scale) ell k₀ k₀
      (translateCutoffSample (triadicCubeShift R) omega) ^ 2
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
  let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB
  let AT : ℝ := probeDeepBandGaugedFluct M ell k₀ g₀ ^ 2
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans hCup
  have hdepthThreshold : collarBandMeanDepthThreshold d ≤ Cup :=
    (le_max_right _ _).trans hCup
  have hCup0 : 0 < Cup :=
    (collarBandMeanDepthThreshold_pos d).trans_le hdepthThreshold
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹ := by
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hlarge : collarBandMeanDepthThreshold d ≤
      (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹ := hdepthThreshold.trans hX
  have hEpos : 0 < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.property
  have hk₀ : 2 ≤ k₀ := by
    have hthree : 3 ≤ k₀ := by
      dsimp only [k₀]
      exact three_le_waveBandDepth_collarBandMeanDepthCoeff
        hEpos M.shellPrefix.gamma_pos rfl hlarge
    omega
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by rw [hscale]; omega
  have hSroot : Algsuperdiff.Frozen.Section3.inductionState
      M (R.scale - 1) E := by
    rw [Algsuperdiff.Frozen.Section3.inductionState] at hS ⊢
    exact ⟨fun i hi => hS.1 i (hi.trans hroot),
      fun i hi => hS.2 i (hi.trans hroot)⟩
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmaxAux
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
      hmaxAux hEgamma
  have hgammaProfile :
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
    hgammaZ.trans
      (zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
        hsigma0 hexp)
  have hgammaHalf : M.gamma / 2 ≤ bfaProfileB * sigma := by
    have hbs : 0 ≤ bfaProfileB * sigma :=
      mul_nonneg bfaProfileB_pos.le hsigma0.le
    linarith only [hgammaProfile, hbs]
  have hrawP := isBigOWith_gammaSigma_slstarPowerTerm_of_gates
    (m := R.scale) (E := (E : ℝ))
    (sigma := upperProfileSigma sigma) (b := bfaProfileB) (gam := M.gamma)
    M M.shellPrefix.dimension E.property hSroot
    hsigmaProfile0 hsigmaProfileHalf bfaProfileB_pos
    bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20 hinvSq hEb
    hgammaZ M.shellPrefix.gamma_pos
  have halpha :
      bfaTau (upperProfileSigma sigma) M.gamma bfaProfileB = alpha := by
    dsimp only [alpha]
    rw [bfaTau, bfaPower, upperProfileBaseSigma]
    congr 2
    ring
  have hrawP' : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma alpha)
      (slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma) AP := by
    rw [← halpha]
    simpa only [AP] using hrawP
  have hPmeas : Measurable
      (slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma) := by
    simpa only [slstarPowerTerm] using!
      measurable_comp_hsep M R.scale (E : ℝ) bfaProfileB fun hs : ℕ =>
        (3 : ℝ) ^ ((M.gamma + 2 * bfaProfileB) * (hs : ℝ))
  have hP := Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
    M (triadicCubeShift R) hPmeas hrawP'
  have hrawT :=
    isBigOWith_gammaSigma_one_probeDeepBandGaugedTail_origin_sq
      M R.scale ell hk₀ (probeSharpLayerAnchor_scale_eq
        R.scale bfaProfileB k₀ n)
  have hTbaseMeas : Measurable fun omega : CutoffSample d =>
      probeDeepBandGaugedTail M (originCube d R.scale) ell k₀ k₀ omega ^ 2 := by
    have htail : Measurable
        (probeDeepBandGaugedTail M (originCube d R.scale) ell k₀ k₀) := by
      change Measurable (fun omega =>
        Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
          probeDeepBandTail M (originCube d R.scale) (ell + (k₀ : ℤ))
            k₀ k₀ omega)
      exact measurable_const.mul
        (probeDeepBandTail_measurable M (originCube d R.scale)
          (ell + (k₀ : ℤ)) k₀ k₀)
    exact htail.pow_const (2 : ℕ)
  have hT := Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
    M (triadicCubeShift R) hTbaseMeas hrawT
  have hP0 : ∀ omega, 0 ≤ P omega := fun omega => by
    dsimp only [P]
    exact slstarPowerTerm_nonneg M R.scale (E : ℝ) bfaProfileB M.gamma _
  have hT0 : ∀ omega, 0 ≤ T omega := fun omega => by
    dsimp only [T]
    positivity
  have hAP : 0 ≤ AP := by
    dsimp only [AP]
    exact Real.rpow_nonneg (hsepAmplitude_pos _ _).le _
  have hAT : 0 ≤ AT := by dsimp only [AT]; positivity
  have hproduct : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => P omega * T omega)
      (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AT) := by
    simpa only [P, T, alpha, AP, AT, g₀] using
      (isBigOWith_upperProfileTarget_collarPower_mul_one
        (mu := (cutoffSampleLaw M).toMeasure)
        (sigma := sigma) (gamma := M.gamma / 2) (b := bfaProfileB)
        hsigma0 hsigma (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num))
        bfaProfileB_pos hgammaHalf hAP hAT hP0 hT0 hP hT)
  have hD := @collarDeepTail_layerAmplitude_nonnegative (d) (M) (E) (n) (j)
  have hmajor := hproduct.const_mul hD
  have hpoint : ∀ omega : CutoffSample d,
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
            ell k₀ k₀ eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega) ≤
        D * (P omega * T omega) := by
    intro omega
    simpa only [D, P, T, k₀, ell, mul_assoc] using
      collarDeepTail_layer_le M hR (E : ℝ) n j
        (translateCutoffSample (triadicCubeShift R) omega)
  exact isBigOWith_gammaSigma_of_le hpoint (by
    simpa only [D, P, T, alpha, AP, AT, mul_assoc] using hmajor)
private theorem gammaProductConst_collarDeepTail_le_sixtyFour
    {sigma gamma : ℝ} (hsigma0 : 0 < sigma)
    (hsigma : sigma ≤ 1 / 2) (hgamma0 : 0 ≤ gamma)
    (hgamma : gamma / 2 ≤ bfaProfileB * sigma) :
    HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileBaseSigma sigma /
          ((2 * (gamma / 2) + 2 * bfaProfileB) / bfaProfileB)) 1 ≤ 64 := by
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * (gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
  have hgammaHalf0 : 0 ≤ gamma / 2 := div_nonneg hgamma0 (by norm_num)
  have halpha0 : 0 < alpha := by
    dsimp only [alpha]
    have hden : 0 < (2 * (gamma / 2) + 2 * bfaProfileB) / bfaProfileB := by
      exact div_pos
        (add_pos_of_nonneg_of_pos
          (mul_nonneg (by norm_num) hgammaHalf0)
          (mul_pos (by norm_num) bfaProfileB_pos))
        bfaProfileB_pos
    exact div_pos (upperProfileBaseSigma_pos hsigma0 hsigma) hden
  have htau : upperProfileHsepTau sigma ≤ alpha := by
    dsimp only [alpha]
    exact upperProfileHsepTau_le_collarPowerSigma hsigma0 hsigma
      hgammaHalf0 bfaProfileB_pos hgamma
  have htauLower : (1 : ℝ) / 5 ≤ upperProfileHsepTau sigma := by
    have hden : 0 < 8 + 3 * sigma + sigma ^ 2 := by positivity
    have hsigmaSq : sigma ^ 2 ≤ (1 : ℝ) / 4 := by
      calc sigma ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hsigma0.le hsigma 2
        _ = (1 : ℝ) / 4 := by norm_num
    rw [upperProfileHsepTau]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden]
    linarith only [hsigmaSq, hsigma]
  have halphaLower : (1 : ℝ) / 5 ≤ alpha := htauLower.trans htau
  have hinv : alpha⁻¹ ≤ (5 : ℝ) :=
    (inv_le_iff_one_le_mul₀ halpha0).2 (by linarith only [halphaLower])
  have hexponent :
      ((alpha * 1 / (alpha + 1))⁻¹) = alpha⁻¹ + 1 := by
    field_simp [halpha0.ne']
    ring
  change (2 : ℝ) ^ ((alpha * 1 / (alpha + 1))⁻¹) ≤ 64
  rw [hexponent]
  calc
    (2 : ℝ) ^ (alpha⁻¹ + 1) ≤ (2 : ℝ) ^ (5 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 64 := by norm_num
private theorem probeMeanGoodWaveConst_pos_collarDeepTail
    (M : ABKModel d) : 0 < probeMeanGoodWaveConst M := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  have hratio : (3 : ℝ) ^ (2 * (1 / 4 : ℝ) - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsimplex : 0 < simplexCrudeConst d (1 / 4) := by
    rw [simplexCrudeConst]
    exact div_pos (by positivity) (sub_pos.mpr hratio)
  have hW : 0 < probeSimplexW1Const d := by
    rw [probeSimplexW1Const]
    positivity
  have hsensitivity : 0 < probeSimplexMeanSensitivityConst d := by
    rw [probeSimplexMeanSensitivityConst]
    exact mul_pos
      (mul_pos (by norm_num)
        (Algsuperdiff.Section3.Provider.BadEvents.bigLambdaSensitivityConst_pos hd))
      (sq_pos_of_pos hW)
  rw [probeMeanGoodWaveConst]
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) hsimplex) hsensitivity)
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1)
private theorem probeDeepBandGainRootConst_pos_collarDeepTail
    (hd : 2 ≤ d) : 0 < probeDeepBandGainRootConst d := by
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
  rw [probeDeepBandGainRootConst, deepBandAmplitude]
  have hgain := Algsuperdiff.Section3.Provider.Stream.streamIncrementLpGainConst_pos
    d (1 / 2)
  have hmoment := HCPolySupport.IndependentSums.gammaMomentConst_pos
    (by norm_num : (0 : ℝ) < 2)
  have htriangle : 0 < HCPolySupport.IndependentSums.gammaTriangleConst 2 :=
    HCPolySupport.IndependentSums.gammaTriangleConst_pos
  have hconcentration :
      0 < Algsuperdiff.Section3.Provider.Stream.geometricConcentrationConst :=
    Algsuperdiff.Section3.Provider.Stream.geometricConcentrationConst_pos
  positivity
/-- One exact translated layer of the literal collar deep-tail summand. -/
def probeSharpFramedCollarDeepTailLayer
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (n : ℕ) (omega : CutoffSample d) : ℝ :=
  let k₀ := collarBandMeanDepth M E
  probeSharpFramedCollarWavePart M R.scale E bfaProfileB
    k₀ n (m - 1) (basisVec j) (superposedGradConst d)
    (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
      (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀ eta ^ 2)
    (translateCutoffSample (triadicCubeShift R) omega)
private theorem deepTail_coordinateTerm_orliczBound :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d},
      R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) →
        ∀ {E : { E : ℝ // (1 : ℝ) ≤ E }},
          Frozen.Section3.inductionState M (m - (1 : ℤ)) E →
            ∀ {sigma Cup : ℝ},
              (0 : ℝ) < sigma →
                sigma ≤ (1 / 2 : ℝ) →
                  max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ) →
                    (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
                      max (profileAuxiliaryConst d) (collarBandMeanDepthThreshold d) ≤ Cup →
                        ∀ (j : Fin d),
                          let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
                          let tailA : ℝ := gammaTriangleConst (2 : ℝ) * (probeDeepBandGainRootConst d * (3 : ℝ) * √(2 : ℝ));
                          let D₀ : ℝ :=
                            probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                              ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                                      probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ *
                                    probeSharpCollarBandMeanMassQuarterConst d *
                                  (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ)) *
                                (3 : ℝ) ^ (1 / 16 : ℝ));
                          let B₀ : ℝ :=
                            D₀ * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (tailA ^ (2 : ℕ) * (81 : ℝ)) * M.gamma);
                          let B : ℕ → ℝ := fun (n : ℕ) => B₀ * whitneyDecayRatio ^ n;
                          let X : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
                            probeSharpFramedCollarDeepTailLayer M m R (↑E : ℝ) j n omega;
                          let alpha : ℝ :=
                            upperProfileBaseSigma sigma /
                              (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB);
                          let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB;
                          let G : ℝ := Ch04.gammaProductConst alpha (1 : ℝ);
                          (0 : ℝ) ≤ G →
                            G ≤ (64 : ℝ) →
                              (0 : ℝ) ≤ AP →
                                AP ≤ superposedFluxHsepConst ^ (3 : ℝ) →
                                  (0 : ℝ) ≤ superposedFluxHsepConst ^ (3 : ℝ) →
                                    (0 : ℝ) < tailA →
                                      (0 : ℝ) < D₀ →
                                        (0 : ℝ) ≤ whitneyDecayRatio →
                                          ∀ (n : ℕ),
                                            IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
                                              (gammaSigma (upperProfileTargetSigma sigma)) (X n) (B n) := by
  intro _ M _ _ R hR E hS sigma _ hsigma0 hsigma hmax hEgamma hCup j k₀ tailA D₀ B₀ B X alpha AP G hG0 hG hAP0 hAP hHcube0 htailA hD₀0 hr0 n
  let ell : ℕ → ℤ := fun n => probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let AT : ℝ := probeDeepBandGaugedFluct M (ell n) k₀
    (probeSharpLayerGap bfaProfileB n) ^ 2
  have hAT0 : 0 ≤ AT := by dsimp only [AT]; positivity
  have hAT : AT ≤ tailA ^ 2 * M.gamma * 81 := by
    dsimp only [AT, ell, k₀, tailA]
    exact tunedDeepTailFluct_sq_le M R.scale E.property hEgamma n
  have hGAP : G * AP ≤ 64 * superposedFluxHsepConst ^ (3 : ℝ) :=
    mul_le_mul hG hAP hAP0 (by norm_num)
  have hGAP0 : 0 ≤ G * AP := mul_nonneg hG0 hAP0
  have htailBound0 : 0 ≤ tailA ^ 2 * M.gamma * 81 :=
    (mul_pos (mul_pos (sq_pos_of_pos htailA) M.shellPrefix.gamma_pos)
      (by norm_num)).le
  have hfactor : G * AP * AT ≤
      64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (tailA ^ 2 * 81) * M.gamma := by
    calc
      G * AP * AT ≤
          (64 * superposedFluxHsepConst ^ (3 : ℝ)) *
            (tailA ^ 2 * M.gamma * 81) :=
        mul_le_mul hGAP hAT hAT0
          (mul_nonneg (by norm_num) hHcube0)
      _ = 64 * superposedFluxHsepConst ^ (3 : ℝ) *
          (tailA ^ 2 * 81) * M.gamma := by ring
  have hDn0 : 0 ≤ D₀ * whitneyDecayRatio ^ n :=
    mul_nonneg hD₀0.le (pow_nonneg hr0 n)
  have hscale :
      (D₀ * whitneyDecayRatio ^ n) * (G * AP * AT) ≤ B n := by
    calc
      (D₀ * whitneyDecayRatio ^ n) * (G * AP * AT) ≤
          (D₀ * whitneyDecayRatio ^ n) *
            (64 * superposedFluxHsepConst ^ (3 : ℝ) *
              (tailA ^ 2 * 81) * M.gamma) :=
        mul_le_mul_of_nonneg_left hfactor hDn0
      _ = B n := by
        dsimp only [B, B₀]
        ring
  have hraw := collarDeepTail_layer_isBigOWith
    M hR hS hsigma0 hsigma hmax hEgamma hCup n j
  have hraw' : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma)) (X n)
      ((D₀ * whitneyDecayRatio ^ n) * (G * AP * AT)) := by
    simpa only [X, probeSharpFramedCollarDeepTailLayer, k₀, ell, D₀, G, alpha, AP, AT,
      vecNormSq_basisVec, one_mul, mul_assoc] using hraw
  exact hraw'.mono_scale hscale

private theorem upperDeepBandTailConsumption_comparisonBounds1 :
    ∀ {d : ℕ} (_ : (2 : ℕ) ≤ d) (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma Cup : ℝ}
      (_ : (0 : ℝ) < sigma) (_ : sigma ≤ (1 / 2 : ℝ))
      (_ : max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ)) (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))),
      let X : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let Z : ℝ := Real.exp (-(collarBandMeanTunedDecayRate d * X));
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let tailA : ℝ := gammaTriangleConst (2 : ℝ) * (probeDeepBandGainRootConst d * (3 : ℝ) * √(2 : ℝ));
      let meanD : ℝ := probeMeanGoodWaveDimensionConst d;
      let fiveD : ℝ := (5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ);
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let capGrowth : ℝ := probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ * (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ));
      let tailC : ℝ := (64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (tailA ^ (2 : ℕ) * (81 : ℝ));
      let rinv : ℝ := ((1 : ℝ) - whitneyDecayRatio)⁻¹;
      let D₀ : ℝ := probeMeanGoodWaveConst M * fiveD * fixed * capGrowth;
      let T : ℝ := gammaTriangleConst (upperProfileTargetSigma sigma);
      let Tbar : ℝ := upperAfterBandRareTriangleConst;
      let K : ℝ := (↑d : ℝ) * Tbar * (meanD * fiveD * fixed * collarBandMeanTunedCapPrefactor d * tailC * rinv);
      ∀ (_ : collarBandMeanDepthThreshold d ≤ X) (_ : (0 : ℝ) < (↑E : ℝ)),
        (0 : ℝ) ≤ Z ∧
          (↑d : ℝ) * T * (meanD * (Disorder.cstar M)⁻¹ * fiveD * fixed) * capGrowth * (tailC * M.gamma * rinv) ≤
              (↑d : ℝ) * Tbar * (meanD * (Disorder.cstar M)⁻¹ * fiveD * fixed) * (collarBandMeanTunedCapPrefactor d * Z) *
                (tailC * M.gamma * rinv) ∧
            D₀ = meanD * (Disorder.cstar M)⁻¹ * fiveD * fixed * capGrowth ∧
              (Disorder.cstar M)⁻¹ * M.gamma ≤ (1 : ℝ) ∧ (0 : ℝ) ≤ K := by
  intro d hd M E _ _ hsigma0 hsigma hmax hEgamma X Z k₀ tailA meanD fiveD fixed capGrowth tailC rinv D₀ T Tbar K hlarge hEpos
  have hcap : capGrowth ≤ collarBandMeanTunedCapPrefactor d * Z := by
    dsimp only [capGrowth, k₀, Z, X]
    exact probeSharpCollarBandMeanTunedCapGrowth_le_exp M hEpos hlarge
  have hT : T ≤ Tbar := by
    dsimp only [T, Tbar]
    exact gammaTriangleConst_upperProfileTarget_le hsigma0 hsigma
  have hmean0 : 0 ≤ meanD := by
    dsimp only [meanD]
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  have hcstar0 : 0 ≤
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1).le
  have hfive0 : 0 ≤ fiveD := by dsimp only [fiveD]; positivity
  have hfixed0 : 0 ≤ fixed := by
    dsimp only [fixed]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (sq_nonneg _))
        (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
      (Real.rpow_nonneg (by norm_num) _)
  have hcap0 : 0 ≤ capGrowth := by
    dsimp only [capGrowth]
    exact mul_nonneg
      (probeSharpCollarBandMeanCapQuarter_nonneg M (E : ℝ) k₀)
      (Real.rpow_nonneg (by norm_num) _)
  have htailC0 : 0 ≤ tailC := by
    dsimp only [tailC]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg superposedFluxHsepConst_pos.le _))
      (mul_nonneg (sq_nonneg tailA) (by norm_num))
  have hrinv0 : 0 ≤ rinv := by
    dsimp only [rinv]
    exact inv_nonneg.mpr (sub_nonneg.mpr whitneyDecayRatio_lt_one.le)
  have hT0 : 0 ≤ T := gammaTriangleConst_pos.le
  have hTbar0 : 0 ≤ Tbar := by
    dsimp only [Tbar]
    rw [upperAfterBandRareTriangleConst]
    positivity
  have hcapBar0 : 0 ≤ collarBandMeanTunedCapPrefactor d :=
    collarBandMeanTunedCapPrefactor_nonneg d
  have hZ0 : 0 ≤ Z := (Real.exp_pos _).le
  have hpre0 : 0 ≤ (d : ℝ) * T *
      (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
        fiveD * fixed) := by positivity
  have hpreBar0 : 0 ≤ (d : ℝ) * Tbar *
      (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
        fiveD * fixed) := by positivity
  have hpost0 : 0 ≤ tailC * M.gamma * rinv := by
    exact mul_nonneg (mul_nonneg htailC0 M.shellPrefix.gamma_pos.le) hrinv0
  have hpre : (d : ℝ) * T *
        (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          fiveD * fixed) ≤
      (d : ℝ) * Tbar *
        (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          fiveD * fixed) := by
    gcongr
  have hraw :
      ((d : ℝ) * T *
          (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
            fiveD * fixed)) * capGrowth * (tailC * M.gamma * rinv) ≤
        ((d : ℝ) * Tbar *
          (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
            fiveD * fixed)) *
          (collarBandMeanTunedCapPrefactor d * Z) *
          (tailC * M.gamma * rinv) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hpre hcap hcap0 hpreBar0) hpost0
  have hD₀ : D₀ = meanD *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * fiveD * fixed *
      capGrowth := by
    dsimp only [D₀]
    rw [show probeMeanGoodWaveConst M = meanD *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ by
      dsimp only [meanD]
      exact probeMeanGoodWaveConst_eq_dimension_mul_cstarInv M]
  have hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    (le_max_right _ _).trans hmax
  have hEgammaOne : (E : ℝ) * M.gamma ≤ 1 :=
    mul_gamma_le_one_of_le_rpow_neg_fifth E.property
      M.shellPrefix.gamma_pos hEgamma
  have hcstarGamma :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcstarE M.shellPrefix.gamma_pos.le).trans
      hEgammaOne
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  exact ⟨hZ0, hraw, hD₀, hcstarGamma, hK0⟩

/-- The finite-coordinate real trace of the literal collar deep-tail summand. -/
def probeSharpFramedCollarDeepTailTraceLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ) (omega : CutoffSample d) : ℝ :=
  ∑ j : Fin d, ∑' n : ℕ, probeSharpFramedCollarDeepTailLayer M m R E j n omega
private theorem measurable_collarDeepTail_layer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ) (i : ℤ)
    (j : Fin d) :
    Measurable fun omega : CutoffSample d =>
      probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
        (basisVec j) (superposedGradConst d)
        (fun eta => probeDeepBandGaugedTail M (originCube d root)
          (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ k₀ eta ^ 2)
        omega := by
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  have htail : Measurable
      (probeDeepBandGaugedTail M (originCube d root) ell k₀ k₀) := by
    change Measurable (fun omega =>
      Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
        probeDeepBandTail M (originCube d root) (ell + (k₀ : ℤ))
          k₀ k₀ omega)
    exact measurable_const.mul
      (probeDeepBandTail_measurable M (originCube d root)
        (ell + (k₀ : ℤ)) k₀ k₀)
  have hcore := measurable_probeSharpCollarBandMeanLayerCore
    M root E k₀ n i (superposedGradConst d)
  rw [show
    (fun omega : CutoffSample d =>
      probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
        (basisVec j) (superposedGradConst d)
        (fun eta => probeDeepBandGaugedTail M (originCube d root)
          (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ k₀ eta ^ 2)
        omega) =
      fun omega =>
        (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          (5 * (d : ℝ) ^ 2)) *
        (probeDeepBandGaugedTail M (originCube d root) ell k₀ k₀ omega ^ 2) *
        probeSharpCollarBandMeanLayerCore M root E k₀ n i
          (superposedGradConst d) omega by
    funext omega
    simp only [probeSharpFramedCollarWavePart,
      probeSharpCollarBandMeanLayerCore, ell]
    ring]
  exact (measurable_const.mul (htail.pow_const (2 : ℕ))).mul hcore
theorem probeSharpFramedCollarDeepTailLayer_nonneg
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (n : ℕ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarDeepTailLayer M m R E j n omega := by
  rw [probeSharpFramedCollarDeepTailLayer]
  exact probeSharpFramedCollarWavePart_nonneg M.shellPrefix.dimension
    M R.scale E bfaProfileB (collarBandMeanDepth M E) n (m - 1)
    (basisVec j) (superposedGradConst d) (fun eta => sq_nonneg _) _
theorem measurable_probeSharpFramedCollarDeepTailLayer (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) (E : ℝ) (j : Fin d) (n : ℕ) :
    Measurable (probeSharpFramedCollarDeepTailLayer M m R E j n) := by
  simpa only [probeSharpFramedCollarDeepTailLayer, Function.comp_apply] using!
    (measurable_collarDeepTail_layer M R.scale E (collarBandMeanDepth M E) n (m - 1) j).comp
      (measurable_translateCutoffSample (triadicCubeShift R))
/- Whitney summation of the literal tenth lane at one coordinate.  The output
scale has a single tuned cap-growth factor and a dimension-only deep-tail
constant times `gamma`; in particular no `E⁻²` ordinary lane appears. -/
theorem collarDeepTail_coordinate_isBigOWith_and_ae_summable
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hCup : max (profileAuxiliaryConst d)
      (collarBandMeanDepthThreshold d) ≤ Cup)
    (j : Fin d) :
    let k₀ := collarBandMeanDepth M (E : ℝ)
    let tailA := HCPolySupport.IndependentSums.gammaTriangleConst 2 *
      (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
    let D₀ := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ))
    let B₀ := D₀ *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (tailA ^ 2 * 81) * M.gamma)
    IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma (upperProfileTargetSigma sigma))
        (fun omega => ∑' n : ℕ,
          probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j n omega)
        (gammaTriangleConst (upperProfileTargetSigma sigma) *
          (B₀ * (1 - whitneyDecayRatio)⁻¹)) ∧
      ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        Summable fun n : ℕ =>
          probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j n omega := by
  dsimp only
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let ell : ℕ → ℤ := fun n =>
    probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let tailA : ℝ := HCPolySupport.IndependentSums.gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
  let D₀ : ℝ := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ))
  let B₀ : ℝ := D₀ *
    (64 * superposedFluxHsepConst ^ (3 : ℝ) *
      (tailA ^ 2 * 81) * M.gamma)
  let B : ℕ → ℝ := fun n => B₀ * whitneyDecayRatio ^ n
  let X : ℕ → CutoffSample d → ℝ := fun n omega =>
    probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j n omega
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans hCup
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmaxAux
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hgammaProfile :
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
    hgamma.trans
      (zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
        hsigma0 hexp)
  have hgammaHalf : M.gamma / 2 ≤ bfaProfileB * sigma := by
    have hbs : 0 ≤ bfaProfileB * sigma :=
      mul_nonneg bfaProfileB_pos.le hsigma0.le
    linarith only [hgammaProfile, hbs]
  have hgammaB : M.gamma ≤ bfaProfileB := by
    calc
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma := hgammaProfile
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsigma
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
      _ ≤ bfaProfileB := by linarith only [bfaProfileB_pos]
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
  let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB
  let G : ℝ := HCPolySupport.Book.Ch04.gammaProductConst alpha 1
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hG : G ≤ 64 := by
    dsimp only [G, alpha]
    exact gammaProductConst_collarDeepTail_le_sixtyFour
      hsigma0 hsigma M.shellPrefix.gamma_pos.le hgammaHalf
  have hAP0 : 0 ≤ AP := by
    dsimp only [AP]
    exact Real.rpow_nonneg (hsepAmplitude_pos _ _).le _
  have hAP : AP ≤ superposedFluxHsepConst ^ (3 : ℝ) := by
    dsimp only [AP]
    exact hsepAmplitude_rpow_bfaPower_le_profile_cube
      (by rw [upperProfileSigma]; positivity)
      (by rw [upperProfileSigma]; linarith) hgammaB
  have hHcube0 : 0 ≤ superposedFluxHsepConst ^ (3 : ℝ) :=
    Real.rpow_nonneg superposedFluxHsepConst_pos.le _
  have htailA : 0 < tailA := by
    dsimp only [tailA]
    exact mul_pos HCPolySupport.IndependentSums.gammaTriangleConst_pos
      (mul_pos
        (mul_pos (probeDeepBandGainRootConst_pos_collarDeepTail hd)
          (by norm_num))
        (Real.sqrt_pos.2 (by norm_num)))
  have htailC0 : 0 ≤ tailA ^ 2 * 81 := by positivity
  have hD₀0 : 0 < D₀ := by
    have hdR : 0 < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
    have hgrad : 0 < superposedGradConst d :=
      lt_of_lt_of_le zero_lt_one
        (one_le_superposedGradConst (le_trans (by norm_num) hd))
    have hcapEnv : 0 < probeSharpCollarBandMeanCapEnvelope M (E : ℝ) k₀ := by
      rw [probeSharpCollarBandMeanCapEnvelope]
      positivity
    have hcap : 0 < probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ := by
      rw [probeSharpCollarBandMeanCapQuarter]
      exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hcapEnv)
    have hmass : 0 < probeSharpCollarBandMeanMassQuarterConst d := by
      rw [probeSharpCollarBandMeanMassQuarterConst]
      exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))
    have hdim : 0 < 5 * (d : ℝ) ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hdR)
    have hinner : 0 < 4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ) := by
      positivity
    dsimp only [D₀]
    exact mul_pos
      (mul_pos (probeMeanGoodWaveConst_pos_collarDeepTail M) hdim) hinner
  have hB₀0 : 0 < B₀ := by
    dsimp only [B₀]
    exact mul_pos hD₀0
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            (Real.rpow_pos_of_pos superposedFluxHsepConst_pos _))
          (mul_pos (sq_pos_of_pos htailA) (by norm_num)))
        M.shellPrefix.gamma_pos)
  have hr0 : 0 ≤ whitneyDecayRatio := whitneyDecayRatio_nonneg
  have hrpos : 0 < whitneyDecayRatio := by
    rw [whitneyDecayRatio]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hBpos : ∀ n, 0 < B n := fun n => by
    dsimp only [B]
    exact mul_pos hB₀0 (pow_pos hrpos n)
  have hBsum : Summable B := by
    simpa only [B] using
      (summable_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one).mul_left B₀
  have hX0 : ∀ n omega, 0 ≤ X n omega := fun n omega => by
    dsimp only [X]
    exact probeSharpFramedCollarDeepTailLayer_nonneg M m R (E : ℝ) j n omega
  have hXmeas : ∀ n, Measurable (X n) := fun n => by
    dsimp only [X]
    exact measurable_probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j n
  have hterm := @deepTail_coordinateTerm_orliczBound (d) (M) (m) (k) (R) (hR) (E) (hS) (sigma)
    (Cup) (hsigma0) (hsigma) (hmax) (hEgamma) (hCup) (j) (hG0) (hG) (hAP0) (hAP) (hHcube0)
      (htailA) (hD₀0) (hr0)
  constructor
  · refine Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
      (upperProfileTargetSigma_pos hsigma0 hsigma) hX0 hXmeas hBpos hBsum
      hterm ?_
    rw [show B = fun n : ℕ => B₀ * whitneyDecayRatio ^ n by rfl,
      tsum_mul_left,
      tsum_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one]
  · exact Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      (upperProfileTargetSigma_pos hsigma0 hsigma) hX0
      (fun n => (hXmeas n).aemeasurable) hBpos hBsum hterm
theorem probeSharpFramedCollarDeepTailTraceLane_nonneg (M : ABKModel d)
    (m : ℤ) (R : TriadicCube d) (E : ℝ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarDeepTailTraceLane M m R E omega := by
  rw [probeSharpFramedCollarDeepTailTraceLane]
  exact Finset.sum_nonneg fun j _ => tsum_nonneg fun n =>
    probeSharpFramedCollarDeepTailLayer_nonneg M m R E j n omega
theorem measurable_probeSharpFramedCollarDeepTailTraceLane (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) (E : ℝ) :
    Measurable (probeSharpFramedCollarDeepTailTraceLane M m R E) := by
  change Measurable fun omega => ∑ j : Fin d, ∑' n : ℕ, probeSharpFramedCollarDeepTailLayer M m R
    E j n omega
  refine Finset.measurable_fun_sum Finset.univ fun j _ => ?_
  have hnn : Measurable (fun omega : CutoffSample d => ∑' n : ℕ,
      (probeSharpFramedCollarDeepTailLayer M m R E j n omega).toNNReal) :=
    Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (measurable_probeSharpFramedCollarDeepTailLayer M m R E j n).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  exact tsum_congr fun n => by
    rw [Real.toNNReal_of_nonneg (probeSharpFramedCollarDeepTailLayer_nonneg
      M m R E j n omega)]
    rfl
theorem ae_ofReal_probeSharpFramedCollarDeepTailTraceLane_eq_sum_tsum
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hCup : max (profileAuxiliaryConst d) (collarBandMeanDepthThreshold d) ≤ Cup) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (probeSharpFramedCollarDeepTailTraceLane
        M m R (E : ℝ) omega) =
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j n omega) := by
  have hsum : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, ∀ j : Fin d,
      Summable fun n : ℕ => probeSharpFramedCollarDeepTailLayer
        M m R (E : ℝ) j n omega :=
    eventually_countable_forall.2 fun j =>
      (collarDeepTail_coordinate_isBigOWith_and_ae_summable
        M hR hS hsigma0 hsigma hmax hEgamma hCup j).2
  filter_upwards [hsum] with omega homega
  rw [probeSharpFramedCollarDeepTailTraceLane,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => tsum_nonneg fun n =>
      probeSharpFramedCollarDeepTailLayer_nonneg M m R (E : ℝ) j n omega)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_tsum_of_nonneg
    (fun n => probeSharpFramedCollarDeepTailLayer_nonneg M m R (E : ℝ) j n omega)
    (homega j)
/- The complete finite-coordinate trace of named summand 10, before the final
deterministic tuned-exponential absorption. -/
theorem collarDeepTail_trace_isBigOWith
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hCup : max (profileAuxiliaryConst d)
      (collarBandMeanDepthThreshold d) ≤ Cup) :
    let k₀ := collarBandMeanDepth M (E : ℝ)
    let tailA := HCPolySupport.IndependentSums.gammaTriangleConst 2 *
      (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
    let D₀ := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ))
    let B₀ := D₀ *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (tailA ^ 2 * 81) * M.gamma)
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarDeepTailTraceLane M m R (E : ℝ))
      ((d : ℝ) *
        (gammaTriangleConst (upperProfileTargetSigma sigma) *
          (B₀ * (1 - whitneyDecayRatio)⁻¹))) := by
  dsimp only
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let tailA := HCPolySupport.IndependentSums.gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
  let D₀ := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ))
  let B₀ := D₀ *
    (64 * superposedFluxHsepConst ^ (3 : ℝ) *
      (tailA ^ 2 * 81) * M.gamma)
  have hcoordinate := (collarDeepTail_coordinate_isBigOWith_and_ae_summable
    M hR hS hsigma0 hsigma hmax hEgamma hCup j₀).1
  have hlayerEq : ∀ (j : Fin d) (n : ℕ) (omega : CutoffSample d),
      probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j n omega =
        probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j₀ n omega := by
    intro j n omega
    simp only [probeSharpFramedCollarDeepTailLayer,
      probeSharpFramedCollarWavePart, vecNormSq_basisVec]
  have htraceEq :
      probeSharpFramedCollarDeepTailTraceLane M m R (E : ℝ) =
        fun omega => (d : ℝ) * (∑' n : ℕ,
          probeSharpFramedCollarDeepTailLayer M m R (E : ℝ) j₀ n omega) := by
    funext omega
    rw [probeSharpFramedCollarDeepTailTraceLane]
    simp_rw [hlayerEq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hscaled := hcoordinate.const_mul (Nat.cast_nonneg d)
  rw [htraceEq]
  simpa only [j₀, k₀, tailA, D₀, B₀, mul_assoc] using hscaled
/- The exact trace scale has genuine tuned exponential decay.  All factors
outside the exponential are dimension-only; the gate also absorbs the
intermediate `cstar⁻¹ * gamma` factor. -/
theorem collarDeepTail_traceScale_le_exp
    (hd : 2 ≤ d) (M : ABKModel d) {E : {E : ℝ // 1 ≤ E}}
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hCup : max (profileAuxiliaryConst d)
      (collarBandMeanDepthThreshold d) ≤ Cup) :
    let k₀ := collarBandMeanDepth M (E : ℝ)
    let tailA := HCPolySupport.IndependentSums.gammaTriangleConst 2 *
      (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
    let D₀ := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ))
    let B₀ := D₀ *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (tailA ^ 2 * 81) * M.gamma)
    let K := (d : ℝ) * upperAfterBandRareTriangleConst *
      (probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) *
        (4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (1 / 16 : ℝ)) *
        collarBandMeanTunedCapPrefactor d *
        (64 * superposedFluxHsepConst ^ (3 : ℝ) *
          (tailA ^ 2 * 81)) *
        (1 - whitneyDecayRatio)⁻¹)
    (d : ℝ) *
        (gammaTriangleConst (upperProfileTargetSigma sigma) *
          (B₀ * (1 - whitneyDecayRatio)⁻¹)) ≤
      K * Real.exp (-(collarBandMeanTunedDecayRate d *
        ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) := by
  dsimp only
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let Z : ℝ := Real.exp (-(collarBandMeanTunedDecayRate d * X))
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let tailA : ℝ := HCPolySupport.IndependentSums.gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
  let meanD : ℝ := probeMeanGoodWaveDimensionConst d
  let fiveD : ℝ := 5 * (d : ℝ) ^ 2
  let fixed : ℝ := 4 * superposedGradConst d ^ 2 *
    probeSharpCollarBandMeanMassQuarterConst d *
    (3 : ℝ) ^ (1 / 16 : ℝ)
  let capGrowth : ℝ :=
    probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ))
  let tailC : ℝ := 64 * superposedFluxHsepConst ^ (3 : ℝ) *
    (tailA ^ 2 * 81)
  let rinv : ℝ := (1 - whitneyDecayRatio)⁻¹
  let D₀ : ℝ := probeMeanGoodWaveConst M * fiveD * fixed * capGrowth
  let B₀ : ℝ := D₀ * tailC * M.gamma
  let T : ℝ := gammaTriangleConst (upperProfileTargetSigma sigma)
  let Tbar : ℝ := upperAfterBandRareTriangleConst
  let K : ℝ := (d : ℝ) * Tbar *
    (meanD * fiveD * fixed * collarBandMeanTunedCapPrefactor d * tailC * rinv)
  have hdepthThreshold : collarBandMeanDepthThreshold d ≤ Cup :=
    (le_max_right _ _).trans hCup
  have hCup0 : 0 < Cup :=
    (collarBandMeanDepthThreshold_pos d).trans_le hdepthThreshold
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hlarge : collarBandMeanDepthThreshold d ≤ X :=
    hdepthThreshold.trans hX
  have hEpos : 0 < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.property
  obtain ⟨hZ0, hraw, hD₀, hcstarGamma, hK0⟩ :=
    (show (0 ≤ Z) ∧ (((d : ℝ) * T *
          (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
            fiveD * fixed)) * capGrowth * (tailC * M.gamma * rinv) ≤
        ((d : ℝ) * Tbar *
          (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
            fiveD * fixed)) *
          (collarBandMeanTunedCapPrefactor d * Z) *
          (tailC * M.gamma * rinv)) ∧ (D₀ = meanD *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * fiveD * fixed *
      capGrowth) ∧ ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma ≤ 1) ∧ (0 ≤ K) from
      @upperDeepBandTailConsumption_comparisonBounds1 (d) (hd) (M) (E) (sigma) (Cup) (hsigma0)
        (hsigma) (hmax) (hEgamma) (hlarge) (hEpos))
  have hBtarget :
      probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
          (4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanCapQuarter M (E : ℝ)
              (collarBandMeanDepth M (E : ℝ)) *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (2 * bfaProfileB *
              (collarBandMeanDepth M (E : ℝ) : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ)) *
          (64 * superposedFluxHsepConst ^ (3 : ℝ) *
            ((HCPolySupport.IndependentSums.gammaTriangleConst 2 *
              (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)) ^ 2 * 81) *
            M.gamma) = B₀ := by
    dsimp only [B₀, D₀, fiveD, fixed, capGrowth, tailC, k₀, tailA]
    ring
  have hKtarget :
      (d : ℝ) * upperAfterBandRareTriangleConst *
        (probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) *
          (4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (1 / 16 : ℝ)) *
          collarBandMeanTunedCapPrefactor d *
          (64 * superposedFluxHsepConst ^ (3 : ℝ) *
            ((HCPolySupport.IndependentSums.gammaTriangleConst 2 *
              (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)) ^ 2 * 81)) *
          (1 - whitneyDecayRatio)⁻¹) = K := by
    dsimp only [K, Tbar, meanD, fiveD, fixed, tailC, tailA, rinv]
  rw [hBtarget, hKtarget]
  rw [← mul_assoc]
  change (d : ℝ) * T * (B₀ * rinv) ≤ K * Z
  dsimp only [B₀]
  rw [hD₀]
  calc
    (d : ℝ) * T *
        ((meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          fiveD * fixed * capGrowth) * tailC * M.gamma * rinv) ≤
      ((d : ℝ) * Tbar *
        (meanD * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          fiveD * fixed)) *
        (collarBandMeanTunedCapPrefactor d * Z) *
        (tailC * M.gamma * rinv) := by
      simpa only [mul_assoc] using hraw
    _ = (K * Z) *
        ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma) := by
      dsimp only [K]
      ring
    _ ≤ (K * Z) * 1 :=
      mul_le_mul_of_nonneg_left hcstarGamma (mul_nonneg hK0 hZ0)
    _ = K * Z := by ring
/-- Dimension-only threshold for the direct tuned collar deep-tail trace. -/
def collarDeepTailTunedOutputConst (d : ℕ) : ℝ :=
  let tailA := gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
  let K := (d : ℝ) * upperAfterBandRareTriangleConst *
    (probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (1 / 16 : ℝ)) * collarBandMeanTunedCapPrefactor d *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) * (tailA ^ 2 * 81)) *
      (1 - whitneyDecayRatio)⁻¹)
  max (max (profileAuxiliaryConst d) (collarBandMeanDepthThreshold d))
    (1 + (K + 8) * (collarBandMeanTunedDecayRate d)⁻¹)
/-- Literal named summand 10 at one strict descendant, with the exact local
eighth-power rare reserve used by the upper assembly. -/
theorem collarDeepTail_trace_isBigOWith_frozenReserve
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : collarDeepTailTunedOutputConst d ≤ Cup) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma ((1 - sigma) / 3))
      (probeSharpFramedCollarDeepTailTraceLane M m R (E : ℝ))
      ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
        Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) ^ 8) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let tailA : ℝ := gammaTriangleConst 2 *
    (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)
  let K : ℝ := (d : ℝ) * upperAfterBandRareTriangleConst *
    (probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (1 / 16 : ℝ)) * collarBandMeanTunedCapPrefactor d *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) * (tailA ^ 2 * 81)) *
      (1 - whitneyDecayRatio)⁻¹)
  let rate : ℝ := collarBandMeanTunedDecayRate d
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  have hbase : max (profileAuxiliaryConst d)
      (collarBandMeanDepthThreshold d) ≤ Cup := by
    exact (le_max_left _ _).trans (by
      simpa only [collarDeepTailTunedOutputConst, tailA, K] using houtput)
  have hCup0 : 0 < Cup :=
    (collarBandMeanDepthThreshold_pos d).trans_le
      ((le_max_right _ _).trans hbase)
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hraw := collarDeepTail_trace_isBigOWith
    M hR hS hsigma0 hsigma hmax hEgamma hbase
  have hdecay := collarDeepTail_traceScale_le_exp
    hd M hsigma0 hsigma hmax hEgamma hbase
  have hmean0 : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  have hK0 : 0 ≤ K := by
    dsimp only [K, tailA]
    have hT : 0 ≤ upperAfterBandRareTriangleConst := by
      rw [upperAfterBandRareTriangleConst]
      positivity
    have hfixed : 0 ≤ 4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (1 / 16 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
        (Real.rpow_nonneg (by norm_num) _)
    have htail : 0 ≤ 64 * superposedFluxHsepConst ^ (3 : ℝ) *
        ((gammaTriangleConst 2 *
          (probeDeepBandGainRootConst d * 3 * Real.sqrt 2)) ^ 2 * 81) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg superposedFluxHsepConst_pos.le _))
        (mul_nonneg (sq_nonneg _) (by norm_num))
    have hinv : 0 ≤ (1 - whitneyDecayRatio)⁻¹ :=
      inv_nonneg.mpr (sub_nonneg.mpr whitneyDecayRatio_lt_one.le)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hT)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hmean0 (by positivity)) hfixed)
              (collarBandMeanTunedCapPrefactor_nonneg d)) htail) hinv)
  have hbranch : 1 + (K + 8) * rate⁻¹ ≤ Cup :=
    (le_max_right _ _).trans (by
      simpa only [collarDeepTailTunedOutputConst, tailA, K, rate] using houtput)
  have hrate : 0 < rate := by
    dsimp only [rate]
    exact collarBandMeanTunedDecayRate_pos d
  have hchoice : K + 8 ≤ rate * Cup := by
    have hmul := mul_le_mul_of_nonneg_left hbranch hrate.le
    calc
      K + 8 = rate * ((K + 8) * rate⁻¹) := by field_simp [hrate.ne']
      _ ≤ rate * (1 + (K + 8) * rate⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith) hrate.le
      _ ≤ rate * Cup := hmul
  have habsorb : K * Real.exp (-(rate * X)) ≤ eps ^ 8 := by
    dsimp only [eps]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hchoice
  have hpow : 1 ≤ (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have hepsScale : eps ^ 8 ≤
      (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 8 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hpow (pow_nonneg (Real.exp_pos _).le 8)
  have hscale := hdecay.trans (habsorb.trans hepsScale)
  exact hraw.mono_scale (by
    simpa only [upperProfileTargetSigma, tailA, K, rate, X, eps, one_mul,
      mul_assoc] using hscale)
end
end Algsuperdiff.Section3.Provider.CoarseEllipticity
