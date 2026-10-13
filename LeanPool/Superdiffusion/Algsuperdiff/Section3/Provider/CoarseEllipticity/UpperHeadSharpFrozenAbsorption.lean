/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHeadSharpCoordinate
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperBandMeanConsumption

/-!
# UpperHeadSharpFrozenAbsorption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Frozen-scale comparison for the sharp wave-head carrier

This file performs terminal numerical comparisons for the sharp wave-head
carrier, both locally at one strict descendant and after the root-plus-depth
assembly.  It retains the ordinary factor
`cstar⁻¹ * s * gamma * (2 * s - gamma)⁻³` and absorbs the rare carrier
at the frozen exceptional scale.  The endpoint `s = 1` is stated explicitly.

These are internal Provider estimates.  They do not alter a frozen
declaration and carry no source-node or closure status.
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


/-! ## Direct tuned collar-head trace -/

/-- One dimension-only gate for the direct tuned collar-head trace.  It pays
both the profile auxiliary threshold and the tuned trace absorption. -/
def collarHeadTunedPerDescendantOutputConst (d : ℕ) : ℝ :=
  max (profileAuxiliaryConst d) (collarHeadTunedOutputConst d)

private abbrev upperHeadSharpFrozenAbsorption_momentBounds1_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma Cup : ℝ}
      (_ : (0 : ℝ) < sigma) (_ : sigma ≤ (1 / 2 : ℝ))
      (_ : max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ)) (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
      (_ : (2 : ℕ) ≤ d),
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let D₀ : ℝ :=
        probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ) * waveL4HeadConst d ^ (2 : ℕ)) *
          ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                  probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)) *
                probeSharpCollarBandMeanMassQuarterConst d *
              (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑(collarBandMeanDepth M (↑E : ℝ)) : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ));
      let Y : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
          (basisVec j₀) (superposedGradConst d)
          (fun (eta : CutoffSample d) =>
            waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
              (2 : ℕ))
          (translateCutoffSample (triadicCubeShift R) omega);
      let alpha : ℝ :=
        upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB);
      let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB;
      let AG : ℝ := upperHeadHsepOneScale sigma M.gamma;
      let X : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let Z : ℝ := Real.exp (-(collarBandMeanTunedDecayRate d * X));
      let K : ℝ := collarHeadTunedTracePrefactor d;
      ∀ (_ : collarHeadTunedOutputConst d ≤ Cup) (_ : (0 : ℝ) < Cup)
        (_ : max (Real.exp (profileAuxiliaryConst d / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
        (_ :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma))
            (fun (omega : CutoffSample d) =>
              ∑' (n : ℕ),
                probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                  (m - (1 : ℤ)) (basisVec ⟨(0 : ℕ), (by positivity)⟩) (superposedGradConst d)
                  (fun (eta : CutoffSample d) =>
                    waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                        (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                      (2 : ℕ))
                  (translateCutoffSample (triadicCubeShift R) omega))
            ((∑' (n : ℕ),
                probeMeanGoodWaveConst M * vecNormSq (basisVec ⟨(0 : ℕ), (by positivity)⟩) *
                      ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ) * waveL4HeadConst d ^ (2 : ℕ)) *
                    ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                            probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)) *
                          probeSharpCollarBandMeanMassQuarterConst d *
                        (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑(collarBandMeanDepth M (↑E : ℝ)) : ℝ)) *
                      (3 : ℝ) ^ (1 / 16 : ℝ)) *
                  whitneyDecayRatio ^ n) *
              (Ch04.gammaProductConst
                    (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB))
                    (1 : ℝ) *
                  hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB *
                upperHeadHsepOneScale sigma M.gamma)))
        (_ :
          (fun (omega : CutoffSample d) =>
              ∑ j : Fin d,
                ∑' (n : ℕ),
                  probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                    (m - (1 : ℤ)) (basisVec j) (superposedGradConst d)
                    (fun (eta : CutoffSample d) =>
                      waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                          (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                        (2 : ℕ))
                    (translateCutoffSample (triadicCubeShift R) omega)) =
            fun (omega : CutoffSample d) =>
            (↑d : ℝ) *
              ∑' (n : ℕ),
                probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                  (m - (1 : ℤ)) (basisVec j₀) (superposedGradConst d)
                  (fun (eta : CutoffSample d) =>
                    waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                        (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                      (2 : ℕ))
                  (translateCutoffSample (triadicCubeShift R) omega))
        (_ : Measurable fun (omega : CutoffSample d) => ∑' (n : ℕ), Y n omega),
        (Measurable fun (omega : CutoffSample d) =>
            ∑ j : Fin d,
              ∑' (n : ℕ),
                probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                  (m - (1 : ℤ)) (basisVec j) (superposedGradConst d)
                  (fun (eta : CutoffSample d) =>
                    waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                        (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                      (2 : ℕ))
                  (translateCutoffSample (triadicCubeShift R) omega)) ∧
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma))
              (fun (omega : CutoffSample d) =>
                ∑ j : Fin d,
                  ∑' (n : ℕ),
                    probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                      (m - (1 : ℤ)) (basisVec j) (superposedGradConst d)
                      (fun (eta : CutoffSample d) =>
                        waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                            (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                          (2 : ℕ))
                      (translateCutoffSample (triadicCubeShift R) omega))
              ((↑d : ℝ) * ((∑' (n : ℕ), D₀ * whitneyDecayRatio ^ n) * (Ch04.gammaProductConst alpha (1 : ℝ) * AP * AG))) ∧
            Cup ≤ X ∧
              (0 : ℝ) ≤ K ∧
                (↑d : ℝ) * ((∑' (n : ℕ), D₀ * whitneyDecayRatio ^ n) * (Ch04.gammaProductConst alpha (1 : ℝ) * AP * AG)) ≤
                    K * Z ∧
                  K + (8 : ℝ) ≤ collarBandMeanTunedDecayRate d * Cup

private theorem upperHeadSharpFrozenAbsorption_momentBounds1 : upperHeadSharpFrozenAbsorption_momentBounds1_statement := by
  intro d M m R E sigma Cup hsigma0 hsigma hmax hEgamma hd _ D₀ Y alpha AP AG X Z K htuned hCup0 hmaxAux hcoordinate htraceEq hXsumMeas
  have htraceMeas : Measurable (fun omega => ∑ j : Fin d, ∑' n : ℕ,
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega)) := by
    rw [htraceEq]
    simpa only [Y] using hXsumMeas.const_mul d
  have hscaled := hcoordinate.const_mul (Nat.cast_nonneg d)
  have htraceRaw : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega))
      ((d : ℝ) *
        ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) *
          (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG))) := by
    rw [htraceEq]
    simpa only [D₀, alpha, AP, AG, vecNormSq_basisVec, one_mul,
      mul_assoc] using hscaled
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hlarge : collarBandMeanDepthThreshold d ≤ X := by
    exact (le_max_left _ _).trans (htuned.trans hX)
  have hgammaProfile : M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
    hgamma.trans
      (zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
        hsigma0 ((le_max_left _ _).trans hmaxAux))
  have hgammaHalf : M.gamma / 2 ≤ bfaProfileB * sigma := by
    nlinarith [mul_nonneg bfaProfileB_pos.le hsigma0.le]
  have hgammaB : M.gamma ≤ bfaProfileB := by
    calc
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma := hgammaProfile
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsigma
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
      _ ≤ bfaProfileB := by nlinarith [bfaProfileB_pos]
  have hscaleExp := collar_head_tuned_trace_scale_le_exp
    hd M (E := (E : ℝ)) (sigma := sigma)
      (lt_of_lt_of_le zero_lt_one E.property) hsigma0 hsigma
      hgammaB hgammaHalf (by simpa only [X] using hlarge)
  have hcstarGamma :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma ≤ 1 :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hmax)
      M.shellPrefix.gamma_pos.le).trans
      (mul_gamma_le_one_of_le_rpow_neg_fifth E.property
        M.shellPrefix.gamma_pos hEgamma)
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact collar_head_tuned_trace_prefactor_nonneg hd
  have hZ0 : 0 ≤ Z := by dsimp only [Z]; positivity
  have hscaleK :
      (d : ℝ) *
          ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) *
            (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG)) ≤
        K * Z := by
    calc
      _ ≤ K * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          M.gamma * Z := by
        simpa only [D₀, alpha, AP, AG, K, Z, X] using hscaleExp
      _ = (K * Z) *
          ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma) := by ring
      _ ≤ (K * Z) * 1 :=
        mul_le_mul_of_nonneg_left hcstarGamma (mul_nonneg hK0 hZ0)
      _ = K * Z := by ring
  have hchoice : K + 8 ≤ collarBandMeanTunedDecayRate d * Cup := by
    have hsecond : 1 + (K + 8) *
        (collarBandMeanTunedDecayRate d)⁻¹ ≤ Cup :=
      (le_max_right _ _).trans (by
        simpa only [collarHeadTunedOutputConst, K] using htuned)
    have hmul := mul_le_mul_of_nonneg_left hsecond
      (collarBandMeanTunedDecayRate_pos d).le
    have hcancel : collarBandMeanTunedDecayRate d *
        ((K + 8) * (collarBandMeanTunedDecayRate d)⁻¹) = K + 8 := by
      field_simp [ne_of_gt (collarBandMeanTunedDecayRate_pos d)]
    calc
      K + 8 = collarBandMeanTunedDecayRate d *
          ((K + 8) * (collarBandMeanTunedDecayRate d)⁻¹) := hcancel.symm
      _ ≤ collarBandMeanTunedDecayRate d *
          (1 + (K + 8) * (collarBandMeanTunedDecayRate d)⁻¹) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (collarBandMeanTunedDecayRate_pos d).le
      _ ≤ collarBandMeanTunedDecayRate d * Cup := hmul
  exact ⟨htraceMeas, htraceRaw, hX, hK0, hscaleK, hchoice⟩

private theorem upperHeadSharpFrozenAbsorption_comparisonBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (_ : (2 : ℕ) ≤ d),
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let D₀ : ℝ :=
        probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ) * waveL4HeadConst d ^ (2 : ℕ)) *
          ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                  probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)) *
                probeSharpCollarBandMeanMassQuarterConst d *
              (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑(collarBandMeanDepth M (↑E : ℝ)) : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ));
      let Y : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
          (basisVec j₀) (superposedGradConst d)
          (fun (eta : CutoffSample d) =>
            waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
              (2 : ℕ))
          (translateCutoffSample (triadicCubeShift R) omega);
      (∀ (j : Fin d) (n : ℕ) (omega : CutoffSample d),
          probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
              (basisVec j) (superposedGradConst d)
              (fun (eta : CutoffSample d) =>
                waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                    (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                  (2 : ℕ))
              (translateCutoffSample (triadicCubeShift R) omega) =
            probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
              (basisVec j₀) (superposedGradConst d)
              (fun (eta : CutoffSample d) =>
                waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                    (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                  (2 : ℕ))
              (translateCutoffSample (triadicCubeShift R) omega)) ∧
        ((fun (omega : CutoffSample d) =>
              ∑ j : Fin d,
                ∑' (n : ℕ),
                  probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                    (m - (1 : ℤ)) (basisVec j) (superposedGradConst d)
                    (fun (eta : CutoffSample d) =>
                      waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                          (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                        (2 : ℕ))
                    (translateCutoffSample (triadicCubeShift R) omega)) =
            fun (omega : CutoffSample d) =>
            (↑d : ℝ) *
              ∑' (n : ℕ),
                probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                  (m - (1 : ℤ)) (basisVec j₀) (superposedGradConst d)
                  (fun (eta : CutoffSample d) =>
                    waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                        (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                      (2 : ℕ))
                  (translateCutoffSample (triadicCubeShift R) omega)) ∧
          (∀ (n : ℕ) (omega : CutoffSample d), (0 : ℝ) ≤ Y n omega) ∧
            (∀ (n : ℕ), Measurable (Y n)) ∧ ∀ (omega : CutoffSample d), Summable fun (n : ℕ) => Y n omega := by
  intro d M m _ R hR E hd j₀ D₀ Y
  have hlayerEq : ∀ (j : Fin d) (n : ℕ) (omega : CutoffSample d),
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega) =
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j₀)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega) := by
    intro j n omega
    rw [probeSharpFramedCollarWavePart, probeSharpFramedCollarWavePart,
      vecNormSq_basisVec, vecNormSq_basisVec]
  have htraceEq :
      (fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega)) =
        fun omega => (d : ℝ) *
          (∑' n : ℕ,
            probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j₀)
              (superposedGradConst d)
              (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega)) := by
    funext omega
    simp_rw [hlayerEq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hX0 : ∀ n omega, 0 ≤ Y n omega := fun n omega => by
    dsimp only [Y]
    exact probeSharpFramedCollarWavePart_nonneg hd M R.scale (E : ℝ)
      bfaProfileB (collarBandMeanDepth M (E : ℝ)) n (m - 1)
      (basisVec j₀) (superposedGradConst d) (fun eta => sq_nonneg _) _
  have hXmeas : ∀ n, Measurable (Y n) := fun n => by
    let ell := probeSharpLayerAnchor R.scale bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n
    have hcore :=
      (measurable_probeSharpCollarBandMeanLayerCore M R.scale (E : ℝ)
        (collarBandMeanDepth M (E : ℝ)) n (m - 1)
        (superposedGradConst d)).comp
        (measurable_translateCutoffSample (triadicCubeShift R))
    have hhead : Measurable
        (waveHeadTerm M R.scale (E : ℝ) bfaProfileB ell) := by
      simpa only [waveHeadTerm] using!
        (measurable_comp_hsep M R.scale (E : ℝ) bfaProfileB fun hs : ℕ =>
          Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
            waveL4Head M ell hs)
    have hproduct :=
      (hcore.const_mul
        (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
          (5 * (d : ℝ) ^ 2))).mul
        ((hhead.pow_const (2 : ℕ)).comp
          (measurable_translateCutoffSample (triadicCubeShift R)))
    convert hproduct using 1
    funext omega
    simp only [Y, ell, probeSharpFramedCollarWavePart,
      probeSharpCollarBandMeanLayerCore, Function.comp_apply, Pi.mul_apply]
    ring
  have hXsum : ∀ omega, Summable fun n => Y n omega := by
    intro omega
    let Q : ℝ := slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
      (translateCutoffSample (triadicCubeShift R) omega) *
      (M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB
        (translateCutoffSample (triadicCubeShift R) omega) : ℝ))
    have hle : ∀ n, Y n omega ≤ (D₀ * whitneyDecayRatio ^ n) * Q := fun n => by
      have h := collar_head_layer_le M hR (E : ℝ) n j₀
        (translateCutoffSample (triadicCubeShift R) omega)
      simpa only [Y, D₀, Q, vecNormSq_basisVec, mul_one, one_mul, mul_assoc] using h
    have hright : Summable fun n => (D₀ * whitneyDecayRatio ^ n) * Q :=
      ((summable_geometric_of_norm_lt_one
        norm_whitneyDecayRatio_lt_one).mul_left D₀).mul_right Q
    exact Summable.of_nonneg_of_le (fun n => hX0 n omega) hle hright
  exact ⟨hlayerEq, htraceEq, hX0, hXmeas, hXsum⟩

/-- The literal finite-coordinate collar-head trace at the common tuned depth
has the eighth-power local rare scale required by the per-descendant upper
assembly.  No root, grid, or depth wrapper intervenes. -/
theorem collar_head_tuned_trace_is_big_o_with_eighth_power
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : collarHeadTunedPerDescendantOutputConst d ≤ Cup) :
    let trace := fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega)
    (∀ omega, 0 ≤ trace omega) ∧ Measurable trace ∧
      (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        ENNReal.ofReal (trace omega) =
          ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (superposedGradConst d)
              (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 3)) trace
        ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
          Real.exp (-(Cup⁻¹ *
            ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) ^ 8) := by
  dsimp only
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let D₀ : ℝ :=
    probeMeanGoodWaveConst M *
      (5 * (d : ℝ) ^ 2 * waveL4HeadConst d ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ)
          (collarBandMeanDepth M (E : ℝ)) *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB *
          (collarBandMeanDepth M (E : ℝ) : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ))
  let Y : ℕ → CutoffSample d → ℝ := fun n omega =>
    probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j₀)
      (superposedGradConst d)
      (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
        (probeSharpLayerAnchor R.scale bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
      (translateCutoffSample (triadicCubeShift R) omega)
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
  let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB
  let AG : ℝ := upperHeadHsepOneScale sigma M.gamma
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  let Z : ℝ := Real.exp (-(collarBandMeanTunedDecayRate d * X))
  let K : ℝ := collarHeadTunedTracePrefactor d
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans (by
      simpa only [collarHeadTunedPerDescendantOutputConst] using houtput)
  have htuned : collarHeadTunedOutputConst d ≤ Cup :=
    (le_max_right _ _).trans (by
      simpa only [collarHeadTunedPerDescendantOutputConst] using houtput)
  have hCup0 : 0 < Cup :=
    (collar_head_tuned_output_const_pos hd).trans_le htuned
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hcoordinate := collar_head_coordinate_is_big_o_with
    M hR hS hsigma0 hsigma hmaxAux hEgamma j₀
  dsimp only [j₀] at hcoordinate
  obtain ⟨hlayerEq, htraceEq, hX0, hXmeas, hXsum⟩ :=
    (show (∀ (j : Fin d) (n : ℕ) (omega : CutoffSample d),
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega) =
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j₀)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega)) ∧ ((fun omega => ∑ j : Fin d, ∑' n :
            ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega)) =
        fun omega => (d : ℝ) *
          (∑' n : ℕ,
            probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j₀)
              (superposedGradConst d)
              (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) ∧ (∀ n omega, 0 ≤ Y n omega) ∧
                (∀ n, Measurable (Y n)) ∧ (∀ omega, Summable fun n => Y n omega) from
      @upperHeadSharpFrozenAbsorption_comparisonBounds1 (d) (M) (m) (k) (R) (hR) (E) (hd))
  have hXsumMeas : Measurable (fun omega => ∑' n, Y n omega) := by
    have hnn : Measurable (fun omega : CutoffSample d =>
        ∑' n, (Y n omega).toNNReal) :=
      Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
        (hXmeas n).real_toNNReal
    have hnn := hnn.coe_nnreal_real
    convert hnn using 1
    funext omega
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by
      rw [Real.toNNReal_of_nonneg (hX0 n omega)]
      rfl
  have htrace0 : ∀ omega, 0 ≤ ∑ j : Fin d, ∑' n : ℕ,
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega) := by
    intro omega
    rw [show (∑ j : Fin d, ∑' n : ℕ,
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega)) =
      (d : ℝ) * ∑' n, Y n omega by
        simpa only [Y] using congrFun htraceEq omega]
    exact mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg fun n => hX0 n omega)
  obtain ⟨htraceMeas, htraceRaw, hX, hK0, hscaleK, hchoice⟩ :=
    (show (Measurable (fun omega => ∑ j : Fin d, ∑' n : ℕ,
      probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega))) ∧ (IsBigOWith (cutoffSampleLaw
          M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega))
      ((d : ℝ) *
        ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) *
          (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG)))) ∧ (Cup ≤ X) ∧ (0 ≤ K) ∧
            ((d : ℝ) *
          ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) *
            (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG)) ≤
        K * Z) ∧ (K + 8 ≤ collarBandMeanTunedDecayRate d * Cup) from
      @upperHeadSharpFrozenAbsorption_momentBounds1 (d) (M) (m) (R) (E) (sigma) (Cup) (hsigma0)
        (hsigma) (hmax) (hEgamma) (hd) (htuned) (hCup0) (hmaxAux) (hcoordinate) (htraceEq)
          (hXsumMeas))
  have habsorb : K * Z ≤ eps ^ 8 := by
    dsimp only [Z, eps]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hchoice
  have hpow : 1 ≤ (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have heps0 : 0 ≤ eps ^ 8 := pow_nonneg (Real.exp_pos _).le 8
  have hscale :
      (d : ℝ) *
          ((∑' n : ℕ, D₀ * whitneyDecayRatio ^ n) *
            (HCPolySupport.Book.Ch04.gammaProductConst alpha 1 * AP * AG)) ≤
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 8 :=
    hscaleK.trans (habsorb.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow heps0))
  have hfinal := htraceRaw.mono_scale hscale
  refine ⟨htrace0, htraceMeas, ?_, ?_⟩
  · filter_upwards [] with omega
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => tsum_nonneg fun n =>
      probeSharpFramedCollarWavePart_nonneg hd M R.scale (E : ℝ)
        bfaProfileB (collarBandMeanDepth M (E : ℝ)) n (m - 1)
        (basisVec j) (superposedGradConst d) (fun eta => sq_nonneg _) _)]
    exact Finset.sum_congr rfl fun j _ =>
      ENNReal.ofReal_tsum_of_nonneg
        (fun n => probeSharpFramedCollarWavePart_nonneg hd M R.scale (E : ℝ)
          bfaProfileB (collarBandMeanDepth M (E : ℝ)) n (m - 1)
          (basisVec j) (superposedGradConst d) (fun eta => sq_nonneg _) _)
        (by simpa only [Y, hlayerEq] using hXsum omega)
  · simpa only [upperProfileTargetSigma, eps, X, mul_assoc] using hfinal

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
