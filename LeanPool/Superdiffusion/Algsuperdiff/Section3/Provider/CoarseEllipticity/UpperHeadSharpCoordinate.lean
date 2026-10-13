/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHeadSharpSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedAbsorption

/-!
# UpperHeadSharpCoordinate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Sharp one-coordinate wave-head consumption

This file retains the `gamma * hsep` factor in the squared wave-head bound.
The profile hypotheses are derived from the existing induction and energy
gates.

The terminal declarations also assemble the tuned collar-head coordinate
estimate, finite trace, and deterministic scale absorption.
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


theorem collar_head_layer_le
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun eta => waveHeadTerm M R.scale E bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M E) n) eta ^ 2)
        omega ≤
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        (5 * (d : ℝ) ^ 2 * waveL4HeadConst d ^ 2) *
        ((4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n)) *
        (slstarPowerTerm M R.scale E bfaProfileB M.gamma omega *
          (M.gamma * (hsep M R.scale E bfaProfileB omega : ℝ))) := by
  let ell := probeSharpLayerAnchor R.scale bfaProfileB
    (collarBandMeanDepth M E) n
  let A := probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
    (5 * (d : ℝ) ^ 2)
  let H := waveHeadTerm M R.scale E bfaProfileB ell omega ^ 2
  let C := probeSharpCollarBandMeanLayerCore M R.scale E
    (collarBandMeanDepth M E) n (m - 1) (superposedGradConst d) omega
  let K := (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n
  let P := slstarPowerTerm M R.scale E bfaProfileB M.gamma omega
  let G := M.gamma * (hsep M R.scale E bfaProfileB omega : ℝ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
        (vecNormSq_nonneg (basisVec j)))
      (by positivity)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact probeSharpCollarBandMeanLayerCore_nonneg M R.scale E
      (collarBandMeanDepth M E) n (m - 1) (superposedGradConst d) omega
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hfixed : 0 ≤ 4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (sq_nonneg _))
              (probeSharpCollarBandMeanCapQuarter_nonneg
                M E (collarBandMeanDepth M E)))
            (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _)
    exact mul_nonneg hfixed
      (pow_nonneg whitneyDecayRatio_nonneg n)
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact slstarPowerTerm_nonneg M R.scale E bfaProfileB M.gamma omega
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact mul_nonneg M.shellPrefix.gamma_pos.le (Nat.cast_nonneg _)
  have hhead : H ≤ waveL4HeadConst d ^ 2 * G := by
    simpa only [H, G, ell] using waveHeadTerm_sq_le
      M R.scale E bfaProfileB ell omega
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
          (fun eta => waveHeadTerm M R.scale E bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M E) n) eta ^ 2)
          omega = A * H * C := by
    simp only [probeSharpFramedCollarWavePart,
      probeSharpCollarBandMeanLayerCore, A, H, C, ell]
    ring
  rw [heq]
  calc
    A * H * C ≤ A * (waveL4HeadConst d ^ 2 * G) * (K * P) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hhead hA) hcore hC
        (mul_nonneg hA (mul_nonneg (sq_nonneg _) hG))
    _ = _ := by
      simp only [A, K, P, G]
      ring

theorem collar_head_coordinate_is_big_o_with
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) :
    let D₀ :=
      probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        (5 * (d : ℝ) ^ 2 * waveL4HeadConst d ^ 2) *
        (4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M (E : ℝ)
            (collarBandMeanDepth M (E : ℝ)) *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB *
            (collarBandMeanDepth M (E : ℝ) : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ))
    let alpha := upperProfileBaseSigma sigma /
      ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
    let AP := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
      bfaPower M.gamma bfaProfileB
    let AG := upperHeadHsepOneScale sigma M.gamma
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega))
      ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) *
        (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG)) := by
  dsimp only
  let D₀ : ℝ :=
    probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
      (5 * (d : ℝ) ^ 2 * waveL4HeadConst d ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ)
          (collarBandMeanDepth M (E : ℝ)) *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB *
          (collarBandMeanDepth M (E : ℝ) : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ))
  let D : ℕ → ℝ := fun n => D₀ * whitneyDecayRatio ^ n
  let P : CutoffSample d → ℝ := fun omega =>
    slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
      (translateCutoffSample (triadicCubeShift R) omega)
  let G : CutoffSample d → ℝ := fun omega =>
    M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB
      (translateCutoffSample (triadicCubeShift R) omega) : ℝ)
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
  let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB
  let AG : ℝ := upperHeadHsepOneScale sigma M.gamma
  have hD₀0 : 0 ≤ D₀ := by
    dsimp only [D₀]
    have hfixed : 0 ≤ 4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ)
          (collarBandMeanDepth M (E : ℝ)) *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB *
          (collarBandMeanDepth M (E : ℝ) : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (sq_nonneg _))
              (probeSharpCollarBandMeanCapQuarter_nonneg M (E : ℝ)
                (collarBandMeanDepth M (E : ℝ))))
            (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
          (vecNormSq_nonneg (basisVec j)))
        (by positivity))
      hfixed
  have hD0 : ∀ n, 0 ≤ D n := fun n => by
    dsimp only [D]
    exact mul_nonneg hD₀0 (pow_nonneg whitneyDecayRatio_nonneg n)
  have hDsum : Summable D := by
    simpa only [D] using
      (summable_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one).mul_left D₀
  have hDtsum0 : 0 ≤ ∑' n, D n := tsum_nonneg hD0
  have hP0 : ∀ omega, 0 ≤ P omega := fun omega => by
    dsimp only [P]
    exact slstarPowerTerm_nonneg M R.scale (E : ℝ) bfaProfileB M.gamma _
  have hG0 : ∀ omega, 0 ≤ G omega := fun omega => by
    dsimp only [G]
    exact mul_nonneg M.shellPrefix.gamma_pos.le (Nat.cast_nonneg _)
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by rw [hscale]; omega
  have hSroot : Algsuperdiff.Frozen.Section3.inductionState
      M (R.scale - 1) E := by
    rw [Algsuperdiff.Frozen.Section3.inductionState] at hstate ⊢
    exact ⟨fun i hi => hstate.1 i (hi.trans hroot),
      fun i hi => hstate.2 i (hi.trans hroot)⟩
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
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
    hgammaZ.trans
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
  have halpha :
      bfaTau (upperProfileSigma sigma) M.gamma bfaProfileB = alpha := by
    dsimp only [alpha]
    rw [bfaTau, bfaPower, upperProfileBaseSigma]
    congr 2
    ring
  have hraw' : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma alpha)
      (slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma) AP := by
    rw [← halpha]
    simpa only [AP] using hraw
  have hhead := isBigOWith_gammaSigma_one_gamma_mul_hsep
    M R.scale hSroot hsigma0 hsigma hmax hEgamma
  have hPmeas : Measurable
      (slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma) := by
    simpa only [slstarPowerTerm] using!
      measurable_comp_hsep M R.scale (E : ℝ) bfaProfileB fun hs : ℕ =>
        (3 : ℝ) ^ ((M.gamma + 2 * bfaProfileB) * (hs : ℝ))
  have hGmeas : Measurable fun omega : CutoffSample d =>
      M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB omega : ℝ) := by
    exact measurable_comp_hsep M R.scale (E : ℝ) bfaProfileB fun hs : ℕ =>
      M.gamma * (hs : ℝ)
  have hP := Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
    M (triadicCubeShift R) hPmeas hraw'
  have hG := Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
    M (triadicCubeShift R) hGmeas hhead
  have hAP : 0 ≤ AP := by
    dsimp only [AP]
    exact (Real.rpow_pos_of_pos
      (hsepAmplitude_pos (upperProfileSigma sigma) bfaProfileB) _).le
  have hAG : 0 ≤ AG := by
    dsimp only [AG]
    exact (upperHeadHsepOneScale_pos hsigma0 hsigma
      M.shellPrefix.gamma_pos).le
  have hproduct : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => P omega * G omega)
      (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG) := by
    simpa only [P, G, alpha, AP, AG] using
      (isBigOWith_upperProfileTarget_collarPower_mul_one
        (mu := (cutoffSampleLaw M).toMeasure)
        (sigma := sigma) (gamma := M.gamma / 2) (b := bfaProfileB)
        hsigma0 hsigma (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num))
        bfaProfileB_pos hgammaHalf hAP hAG hP0 hG0 hP hG)
  have hmajor := hproduct.const_mul hDtsum0
  have hpoint : ∀ omega : CutoffSample d,
      (∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega)) ≤
        (∑' n, D n) * (P omega * G omega) := by
    intro omega
    let X : ℕ → ℝ := fun n =>
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega)
    have hX0 : ∀ n, 0 ≤ X n := fun n => by
      dsimp only [X]
      exact probeSharpFramedCollarWavePart_nonneg M.shellPrefix.dimension
        M R.scale (E : ℝ) bfaProfileB (collarBandMeanDepth M (E : ℝ))
        n (m - 1) (basisVec j) (superposedGradConst d)
        (fun eta => sq_nonneg _) _
    have hXle : ∀ n, X n ≤ D n * (P omega * G omega) := fun n => by
      have h := collar_head_layer_le M hR (E : ℝ) n j
        (translateCutoffSample (triadicCubeShift R) omega)
      dsimp only [X, D, D₀, P, G]
      simpa only [mul_assoc] using h
    have hright : Summable fun n => D n * (P omega * G omega) :=
      hDsum.mul_right (P omega * G omega)
    have hXsum : Summable X :=
      Summable.of_nonneg_of_le hX0 hXle hright
    calc
      ∑' n, X n ≤ ∑' n, D n * (P omega * G omega) :=
        Summable.tsum_le_tsum hXle hXsum hright
      _ = (∑' n, D n) * (P omega * G omega) := by
        rw [tsum_mul_right]
  exact isBigOWith_gammaSigma_of_le hpoint (by
    simpa only [D, D₀, P, G, alpha, AP, AG] using hmajor)

def collarHeadHsepOneConst : ℝ :=
  (((7 : ℝ) / 8 * bfaProfileB * Real.log 3)⁻¹) *
    superposedFluxHsepConst

/-- The dimension prefactor for the tuned collar-head finite trace. -/
def collarHeadTunedTracePrefactor (d : ℕ) : ℝ :=
  (d : ℝ) * probeMeanGoodWaveDimensionConst d *
    (5 * (d : ℝ) ^ 2 * waveL4HeadConst d ^ 2) *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (1 / 16 : ℝ)) *
    collarBandMeanTunedCapPrefactor d *
    (1 - whitneyDecayRatio)⁻¹ *
    (64 * superposedFluxHsepConst ^ (3 : ℝ) *
      collarHeadHsepOneConst)

/-- The terminal threshold paying the tuned collar-head prefactor. -/
def collarHeadTunedOutputConst (d : ℕ) : ℝ :=
  max (collarBandMeanDepthThreshold d)
    (1 + (collarHeadTunedTracePrefactor d + 8) *
      (collarBandMeanTunedDecayRate d)⁻¹)

theorem collar_head_tuned_trace_prefactor_nonneg (hd : 2 ≤ d) :
    0 ≤ collarHeadTunedTracePrefactor d := by
  rw [collarHeadTunedTracePrefactor]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg d)
              (by
                rw [probeMeanGoodWaveDimensionConst]
                exact mul_nonneg
                  (mul_nonneg (by norm_num)
                    (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ))
                      (by norm_num)))
                  (probeSimplexMeanSensitivityConst_nonneg hd)))
            (by positivity))
          (by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity) (sq_nonneg _))
                (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
              (Real.rpow_nonneg (by norm_num) _)))
        (collarBandMeanTunedCapPrefactor_nonneg d))
      (inv_nonneg.mpr (sub_nonneg.mpr whitneyDecayRatio_lt_one.le)))
    (by
      have hbase : 0 ≤ (7 : ℝ) / 8 * bfaProfileB * Real.log 3 :=
        mul_nonneg
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
          (Real.log_pos (by norm_num)).le
      have hconst : 0 ≤ collarHeadHsepOneConst := by
        rw [collarHeadHsepOneConst]
        exact mul_nonneg (inv_nonneg.mpr hbase)
          superposedFluxHsepConst_pos.le
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg superposedFluxHsepConst_pos.le _)) hconst)

theorem collar_head_tuned_output_const_pos (hd : 2 ≤ d) :
    0 < collarHeadTunedOutputConst d := by
  rw [collarHeadTunedOutputConst]
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  have hK := collar_head_tuned_trace_prefactor_nonneg hd
  have hr : 0 < (collarBandMeanTunedDecayRate d)⁻¹ :=
    inv_pos.mpr (collarBandMeanTunedDecayRate_pos d)
  positivity

theorem gamma_product_const_collar_head_le_sixty_four
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
    have hsigmaSq : sigma ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith
    rw [upperProfileHsepTau]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden]
    nlinarith
  have halphaLower : (1 : ℝ) / 5 ≤ alpha := htauLower.trans htau
  have hinv : alpha⁻¹ ≤ (5 : ℝ) :=
    (inv_le_iff_one_le_mul₀ halpha0).2 (by nlinarith)
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

theorem upper_head_hsep_one_scale_le_const_mul_gamma
    {sigma gamma : ℝ} (hsigma0 : 0 < sigma)
    (hsigma : sigma ≤ 1 / 2) (hgamma : 0 ≤ gamma) :
    upperHeadHsepOneScale sigma gamma ≤
      collarHeadHsepOneConst * gamma := by
  let p : ℝ := upperProfileBaseSigma sigma
  let c : ℝ := p * bfaProfileB * Real.log 3
  let c₀ : ℝ := (7 : ℝ) / 8 * bfaProfileB * Real.log 3
  let H : ℝ := superposedFluxHsepConst
  let K : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB
  have hp0 : 0 < p := upperProfileBaseSigma_pos hsigma0 hsigma
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    rw [upperProfileBaseSigma, upperProfileSigma]
    linarith
  have hpLower : (7 : ℝ) / 8 ≤ p := by
    dsimp only [p]
    rw [upperProfileBaseSigma, upperProfileSigma]
    linarith
  have hbLog : 0 < bfaProfileB * Real.log 3 :=
    mul_pos bfaProfileB_pos (Real.log_pos (by norm_num))
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact mul_pos (mul_pos (by norm_num) bfaProfileB_pos)
      (Real.log_pos (by norm_num))
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (mul_pos hp0 bfaProfileB_pos)
      (Real.log_pos (by norm_num))
  have hcLower : c₀ ≤ c := by
    dsimp only [c₀, c]
    have hfirst := mul_le_mul_of_nonneg_right hpLower bfaProfileB_pos.le
    exact mul_le_mul_of_nonneg_right hfirst
      (Real.log_pos (by norm_num)).le
  have hcinv : c⁻¹ ≤ c₀⁻¹ := (inv_le_inv₀ hc hc₀).2 hcLower
  have hK1 : 1 ≤ K := by
    dsimp only [K]
    rw [hsepAmplitude]
    nlinarith [sq_nonneg (1 + Real.log
      (hsepTailConst (upperProfileSigma sigma) bfaProfileB))]
  have hsigmaInternal0 : 0 < upperProfileSigma sigma := by
    rw [upperProfileSigma]
    positivity
  have hsigmaInternal : upperProfileSigma sigma ≤ 1 / 8 := by
    rw [upperProfileSigma]
    linarith
  have hKH : K ≤ H := by
    dsimp only [K, H]
    exact hsepAmplitude_le_superposedFluxHsepConst
      hsigmaInternal0 hsigmaInternal
  have hKpow : K ^ p ≤ H :=
    (Real.rpow_le_self_of_one_le hK1 hp1).trans hKH
  have hcinv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hc₀inv0 : 0 ≤ c₀⁻¹ := inv_nonneg.mpr hc₀.le
  have hKpow0 : 0 ≤ K ^ p := Real.rpow_nonneg (by positivity) _
  have hH0 : 0 ≤ H := superposedFluxHsepConst_pos.le
  rw [upperHeadHsepOneScale, collarHeadHsepOneConst]
  change gamma * c⁻¹ * K ^ p ≤ (c₀⁻¹ * H) * gamma
  calc
    gamma * c⁻¹ * K ^ p ≤ gamma * c₀⁻¹ * H := by
      gcongr
    _ = (c₀⁻¹ * H) * gamma := by ring

/-- The exact finite-coordinate scale produced by the tuned collar-head
estimate has a dimension-only prefactor, the indispensable `cstar⁻¹ * gamma`,
and genuine tuned exponential decay. -/
theorem collar_head_tuned_trace_scale_le_exp
    (hd : 2 ≤ d) (M : ABKModel d) {E sigma : ℝ}
    (hE : 0 < E) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgammaB : M.gamma ≤ bfaProfileB)
    (hgammaHalf : M.gamma / 2 ≤ bfaProfileB * sigma)
    (hlarge : collarBandMeanDepthThreshold d ≤
      E⁻¹ ^ 2 * M.gamma⁻¹) :
    let D₀ :=
      probeMeanGoodWaveConst M *
        (5 * (d : ℝ) ^ 2 * waveL4HeadConst d ^ 2) *
        (4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M E
            (collarBandMeanDepth M E) *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB *
            (collarBandMeanDepth M E : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ))
    let alpha := upperProfileBaseSigma sigma /
      ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
    let AP := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
      bfaPower M.gamma bfaProfileB
    let AG := upperHeadHsepOneScale sigma M.gamma
    (d : ℝ) *
        ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) *
          (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG)) ≤
      collarHeadTunedTracePrefactor d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
        Real.exp (-(collarBandMeanTunedDecayRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  dsimp only
  let headC : ℝ := 5 * (d : ℝ) ^ 2 * waveL4HeadConst d ^ 2
  let fixedC : ℝ := 4 * superposedGradConst d ^ 2 *
    probeSharpCollarBandMeanMassQuarterConst d *
    (3 : ℝ) ^ (1 / 16 : ℝ)
  let capGrowth : ℝ :=
    probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
      (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ))
  let Dbar : ℝ := probeMeanGoodWaveDimensionConst d * headC * fixedC *
    collarBandMeanTunedCapPrefactor d
  let D₀ : ℝ := probeMeanGoodWaveConst M * headC *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ))
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
  let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB
  let AG : ℝ := upperHeadHsepOneScale sigma M.gamma
  let Z : ℝ := Real.exp (-(collarBandMeanTunedDecayRate d *
    (E⁻¹ ^ 2 * M.gamma⁻¹)))
  let P : ℝ := HCPolySupport.Book.Ch04.gammaProductConst alpha 1
  have hmean0 : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  have hcstar0 : 0 ≤
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1).le
  have hheadC0 : 0 ≤ headC := by dsimp only [headC]; positivity
  have hfixedC0 : 0 ≤ fixedC := by
    dsimp only [fixedC]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (sq_nonneg _))
        (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
      (Real.rpow_nonneg (by norm_num) _)
  have hcap0 : 0 ≤ capGrowth := by
    dsimp only [capGrowth]
    exact mul_nonneg
      (probeSharpCollarBandMeanCapQuarter_nonneg M E
        (collarBandMeanDepth M E))
      (Real.rpow_nonneg (by norm_num) _)
  have hDbar0 : 0 ≤ Dbar := by
    dsimp only [Dbar]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hmean0 hheadC0) hfixedC0)
      (collarBandMeanTunedCapPrefactor_nonneg d)
  have hD₀0 : 0 ≤ D₀ := by
    dsimp only [D₀]
    have hinner :
        4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanCapQuarter M E
              (collarBandMeanDepth M E) *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (2 * bfaProfileB *
              (collarBandMeanDepth M E : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ) = fixedC * capGrowth := by
      dsimp only [fixedC, capGrowth]
      ring
    rw [hinner]
    exact mul_nonneg
      (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M) hheadC0)
      (mul_nonneg hfixedC0 hcap0)
  have hZ0 : 0 ≤ Z := by dsimp only [Z]; positivity
  have hcap : capGrowth ≤ collarBandMeanTunedCapPrefactor d * Z := by
    dsimp only [capGrowth, Z]
    exact probeSharpCollarBandMeanTunedCapGrowth_le_exp M hE hlarge
  have hD₀ : D₀ ≤ Dbar *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z := by
    dsimp only [D₀, Dbar]
    rw [show probeMeanGoodWaveConst M =
        probeMeanGoodWaveDimensionConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ by
      exact probeMeanGoodWaveConst_eq_dimension_mul_cstarInv M]
    calc
      (probeMeanGoodWaveDimensionConst d *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) * headC *
          (4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanCapQuarter M E
              (collarBandMeanDepth M E) *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (2 * bfaProfileB *
              (collarBandMeanDepth M E : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ)) =
        (probeMeanGoodWaveDimensionConst d *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) *
          headC * fixedC * capGrowth := by
        dsimp only [fixedC, capGrowth]
        ring
      _ ≤
        (probeMeanGoodWaveDimensionConst d *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) *
          headC * fixedC *
            (collarBandMeanTunedCapPrefactor d * Z) := by
        gcongr
      _ = (probeMeanGoodWaveDimensionConst d * headC * fixedC *
          collarBandMeanTunedCapPrefactor d) *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z := by ring
  have hsum : (∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) =
      D₀ * (1 - whitneyDecayRatio)⁻¹ := by
    rw [tsum_mul_left,
      tsum_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one]
  have hrinv0 : 0 ≤ (1 - whitneyDecayRatio)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr whitneyDecayRatio_lt_one.le)
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hP : P ≤ 64 := by
    dsimp only [P, alpha]
    exact gamma_product_const_collar_head_le_sixty_four
      hsigma0 hsigma M.shellPrefix.gamma_pos.le hgammaHalf
  have hAP0 : 0 ≤ AP := by
    dsimp only [AP]
    exact Real.rpow_nonneg (hsepAmplitude_pos _ _).le _
  have hAP : AP ≤ superposedFluxHsepConst ^ (3 : ℝ) := by
    dsimp only [AP]
    exact hsepAmplitude_rpow_bfaPower_le_profile_cube
      (by rw [upperProfileSigma]; positivity)
      (by rw [upperProfileSigma]; linarith) hgammaB
  have hAG0 : 0 ≤ AG := by
    dsimp only [AG]
    exact (upperHeadHsepOneScale_pos hsigma0 hsigma
      M.shellPrefix.gamma_pos).le
  have hAG : AG ≤ collarHeadHsepOneConst * M.gamma := by
    dsimp only [AG]
    exact upper_head_hsep_one_scale_le_const_mul_gamma
      hsigma0 hsigma M.shellPrefix.gamma_pos.le
  have hHcube0 : 0 ≤ 64 * superposedFluxHsepConst ^ (3 : ℝ) :=
    mul_nonneg (by norm_num)
      (Real.rpow_nonneg superposedFluxHsepConst_pos.le _)
  have hAGbar0 : 0 ≤ collarHeadHsepOneConst * M.gamma :=
    hAG0.trans hAG
  change (d : ℝ) *
      ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) * (P * AP * AG)) ≤
    collarHeadTunedTracePrefactor d *
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma * Z
  rw [hsum]
  calc
    (d : ℝ) *
        (D₀ * (1 - whitneyDecayRatio)⁻¹ * (P * AP * AG)) ≤
      (d : ℝ) *
        ((Dbar *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z) *
          (1 - whitneyDecayRatio)⁻¹ *
          (64 * superposedFluxHsepConst ^ (3 : ℝ) *
            (collarHeadHsepOneConst * M.gamma))) := by
      gcongr
    _ = collarHeadTunedTracePrefactor d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma * Z := by
      rw [collarHeadTunedTracePrefactor]
      dsimp only [Dbar, headC, fixedC]
      ring


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
