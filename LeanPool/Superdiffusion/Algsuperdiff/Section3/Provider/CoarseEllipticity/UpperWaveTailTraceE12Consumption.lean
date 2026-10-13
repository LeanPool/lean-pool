/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailE12Consumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedAbsorption

/-!
# UpperWaveTailTraceE12Consumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact consumption for the strict-descendant wave-tail trace

This file forms the finite-coordinate trace of the literal named framed
wave-tail Whitney lane at one strict descendant.  The coordinatewise comparison
is intersected over the finite basis and summed, yielding the exact
bounded-plus-rare real trace carriers at the translated descendant sample.

The final declaration also prices the literal collar wave-tail summand at the
common collar/band-mean depth, directly from the induction state and frozen
gates.  The descendant maximum, positive-depth aggregation, root row, other
named lanes, complete envelope, cutoff observable, and all-exponent estimate
remain outside this file.  These declarations are conditional internal Provider
A and carry no source-node, source-node-instance, fractional-node, or closure
status.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}


/-! ## Direct common-depth collar wave-tail terminal -/

/-- Dimension-only output threshold for the literal collar copy of the
common-depth squared wave tail.  The displayed coefficient is exactly the
finite-coordinate Whitney-sum prefactor used in the proof below; the leading
`1` makes its nonnegativity explicit. -/
def probeSharpCollarWaveTailTunedOutputConst (d : ℕ) : ℝ :=
  let K := 1 +
    (d : ℝ) * upperAfterBandRareTriangleConst *
      probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (1 / 16 : ℝ)) *
      collarBandMeanTunedCapPrefactor d *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (4 * waveTailProfileConst d) ^ 2) *
      (1 - whitneyDecayRatio)⁻¹
  let rate := probeSharpWaveTailTunedRate d
  max (max (profileAuxiliaryConst d) (collarBandMeanDepthThreshold d))
    (1 + 2 * (K * (rate / 2)⁻¹ + 8) * rate⁻¹)

private abbrev upperWaveTailTraceE12Consumption_comparisonBounds3_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ} (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let capGrowth : ℝ := probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ * (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ));
      let D₀ : ℝ := probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) * fixed * capGrowth;
      let B₀ : ℝ := D₀ * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (waveC ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) * Z));
      let K : ℝ :=
        (1 : ℝ) +
          (↑d : ℝ) * upperAfterBandRareTriangleConst * probeMeanGoodWaveDimensionConst d * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                  fixed *
                collarBandMeanTunedCapPrefactor d *
              ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ (2 : ℕ)) *
            ((1 : ℝ) - whitneyDecayRatio)⁻¹;
      ∀ (_ : (0 : ℝ) ≤ fixed) (_ : (0 : ℝ) ≤ capGrowth)
        (_ : capGrowth ≤ collarBandMeanTunedCapPrefactor d) (_ : (0 : ℝ) ≤ probeMeanGoodWaveDimensionConst d)
        (_ : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * sigma⁻¹ ^ (2 : ℕ) * Z),
        (↑d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) * (B₀ * ((1 : ℝ) - whitneyDecayRatio)⁻¹)) ≤
            K * ((Disorder.cstar M)⁻¹ * sigma⁻¹ ^ (2 : ℕ) * Z) ∧
          (0 : ℝ) ≤ (↑E : ℝ) ∧ (0 : ℝ) ≤ sigma⁻¹

private abbrev upperWaveTailTraceE12Consumption_comparisonBounds4_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma Cup : ℝ}
      (_ : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let capGrowth : ℝ := probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ * (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ));
      let D₀ : ℝ := probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) * fixed * capGrowth;
      let B₀ : ℝ := D₀ * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (waveC ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) * Z));
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let X : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j₀)
          (superposedGradConst d)
          (fun (eta : CutoffSample d) =>
            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
              (2 : ℕ))
          (translateCutoffSample shift omega);
      let K : ℝ :=
        (1 : ℝ) +
          (↑d : ℝ) * upperAfterBandRareTriangleConst * probeMeanGoodWaveDimensionConst d * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                  fixed *
                collarBandMeanTunedCapPrefactor d *
              ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ (2 : ℕ)) *
            ((1 : ℝ) - whitneyDecayRatio)⁻¹;
      ∀ (_ : (0 : ℝ) < rate) (_ : (0 : ℝ) ≤ K) (_ : (0 : ℝ) < Cup)
        (_ : K * (rate / (2 : ℝ))⁻¹ + (8 : ℝ) ≤ rate / (2 : ℝ) * Cup) (_ : Cup ≤ Xpar)
        (_ : ∀ (n : ℕ) (omega : CutoffSample d), (0 : ℝ) ≤ X n omega)
        (_ :
          ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)), Summable fun (n : ℕ) => X n omega)
        (_ : Measurable fun (omega : CutoffSample d) => ∑' (n : ℕ), X n omega)
        (_ :
          (fun (omega : CutoffSample d) =>
              ∑ j : Fin d,
                ∑' (n : ℕ),
                  probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                    (superposedGradConst d)
                    (fun (eta : CutoffSample d) =>
                      waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
                          eta ^
                        (2 : ℕ))
                    (translateCutoffSample shift omega)) =
            fun (omega : CutoffSample d) => (↑d : ℝ) * ∑' (n : ℕ), X n omega)
        (_ :
          (↑d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) * (B₀ * ((1 : ℝ) - whitneyDecayRatio)⁻¹)) ≤
            K * ((Disorder.cstar M)⁻¹ * sigma⁻¹ ^ (2 : ℕ) * Z))
        (_ : (Disorder.cstar M)⁻¹ * sigma⁻¹ ^ (2 : ℕ) ≤ Xpar),
        (↑d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) * (B₀ * ((1 : ℝ) - whitneyDecayRatio)⁻¹)) ≤
            (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * Real.exp (-(Cup⁻¹ * Xpar)) ^ (8 : ℕ) ∧
          (∀ (omega : CutoffSample d),
              (0 : ℝ) ≤
                ∑ j : Fin d,
                  ∑' (n : ℕ),
                    probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                      (superposedGradConst d)
                      (fun (eta : CutoffSample d) =>
                        waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
                            eta ^
                          (2 : ℕ))
                      (translateCutoffSample shift omega)) ∧
            (Measurable fun (omega : CutoffSample d) =>
                ∑ j : Fin d,
                  ∑' (n : ℕ),
                    probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                      (superposedGradConst d)
                      (fun (eta : CutoffSample d) =>
                        waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
                            eta ^
                          (2 : ℕ))
                      (translateCutoffSample shift omega)) ∧
              ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                ENNReal.ofReal
                    (∑ j : Fin d,
                      ∑' (n : ℕ),
                        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                          (superposedGradConst d)
                          (fun (eta : CutoffSample d) =>
                            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                              (2 : ℕ))
                          (translateCutoffSample shift omega)) =
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      ENNReal.ofReal
                        (probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                          (superposedGradConst d)
                          (fun (eta : CutoffSample d) =>
                            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                              (2 : ℕ))
                          (translateCutoffSample shift omega))

private abbrev upperWaveTailTraceE12Consumption_momentBounds3_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma Cup : ℝ}
      (hsigma0 : (0 : ℝ) < sigma) (hsigma : sigma ≤ (1 / 2 : ℝ))
      (hmax : max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ)) (hd : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let capGrowth : ℝ := probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ * (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ));
      let D₀ : ℝ := probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) * fixed * capGrowth;
      let B₀ : ℝ := D₀ * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (waveC ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) * Z));
      let B : ℕ → ℝ := fun (n : ℕ) => B₀ * whitneyDecayRatio ^ n;
      let j₀ : Fin d := ⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two hd⟩;
      let X : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j₀)
          (superposedGradConst d)
          (fun (eta : CutoffSample d) =>
            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
              (2 : ℕ))
          (translateCutoffSample shift omega);
      let K : ℝ :=
        (1 : ℝ) +
          (↑d : ℝ) * upperAfterBandRareTriangleConst * probeMeanGoodWaveDimensionConst d * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                  fixed *
                collarBandMeanTunedCapPrefactor d *
              ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ (2 : ℕ)) *
            ((1 : ℝ) - whitneyDecayRatio)⁻¹;
      ∀ (hrate : (0 : ℝ) < rate) (hfixed0 : (0 : ℝ) ≤ fixed) (hcapGrowth0 : (0 : ℝ) ≤ capGrowth) (hD₀0 : (0 : ℝ) ≤ D₀)
        (hwaveProfile : (0 : ℝ) < waveTailProfileConst d) (hZ : (0 : ℝ) < Z) (hBpos : ∀ (n : ℕ), (0 : ℝ) < B n)
        (hBsum : Summable B) (hK0 : (0 : ℝ) ≤ K) (hCup1 : (1 : ℝ) ≤ Cup) (hCup0 : (0 : ℝ) < Cup)
        (hchoice : K * (rate / (2 : ℝ))⁻¹ + (8 : ℝ) ≤ rate / (2 : ℝ) * Cup) (hgammaZ : M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ))
        (hXgate : Cup ≤ Xpar) (hlarge : collarBandMeanDepthThreshold d ≤ Xpar)
        (hSroot : Frozen.Section3.inductionState M (R.scale - (1 : ℤ)) E)
        (hsigmaProfile0 : (0 : ℝ) < upperProfileSigma sigma) (hsigmaProfileHalf : upperProfileSigma sigma ≤ (1 / 2 : ℝ))
        (hEexp : Real.exp (badClustersConst d / upperProfileSigma sigma) ≤ (↑E : ℝ))
        (hEb : badClustersConst d / bfaProfileB ≤ (↑E : ℝ)) (hE4 : (4 : ℝ) ≤ (↑E : ℝ)) (hunit : BadEvents.unitGate M)
        (hgamma20 : M.gamma ≤ (1 / 20 : ℝ)) (hinvSq : (↑E : ℝ)⁻¹ ^ (2 : ℕ) ≤ Disorder.cstar M)
        (hgammaGate : M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ)) (hgammaHalf : M.gamma / (2 : ℝ) ≤ bfaProfileB * sigma)
        (hP :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
            (gammaSigma
              (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB)))
            (fun (omega : CutoffSample d) =>
              slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma (translateCutoffSample (triadicCubeShift R) omega))
            (hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB))
        (hP0 :
          ∀ (omega : CutoffSample d),
            (0 : ℝ) ≤
              slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma (translateCutoffSample (triadicCubeShift R) omega))
        (hAP0 : (0 : ℝ) ≤ hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB)
        (hAP :
          hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB ≤
            superposedFluxHsepConst ^ (3 : ℝ))
        (hG0 :
          (0 : ℝ) ≤
            Book.Ch04.gammaProductConst
              (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB))
              (upperProfileTailSigma sigma))
        (hG :
          Book.Ch04.gammaProductConst
              (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB))
              (upperProfileTailSigma sigma) ≤
            (64 : ℝ))
        (htailExponent :
          (2 : ℝ) / upperProfileSigma sigma / ((2 : ℝ) + (2 : ℝ) / upperProfileSigma sigma) = upperProfileTailSigma sigma)
        (hdepthWave : (3 : ℝ) ^ (-((↑d : ℝ) / (4 : ℝ)) * (↑k₀ : ℝ)) ≤ Z),
        IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
            (fun (omega : CutoffSample d) =>
              ∑ j : Fin d,
                ∑' (n : ℕ),
                  probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                    (superposedGradConst d)
                    (fun (eta : CutoffSample d) =>
                      waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
                          eta ^
                        (2 : ℕ))
                    (translateCutoffSample shift omega))
            ((↑d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) * (B₀ * ((1 : ℝ) - whitneyDecayRatio)⁻¹))) ∧
          (↑d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) * (B₀ * ((1 : ℝ) - whitneyDecayRatio)⁻¹)) ≤
              (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * Real.exp (-(Cup⁻¹ * Xpar)) ^ (8 : ℕ) ∧
            (∀ (omega : CutoffSample d),
                (0 : ℝ) ≤
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                        (superposedGradConst d)
                        (fun (eta : CutoffSample d) =>
                          waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                              (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                            (2 : ℕ))
                        (translateCutoffSample shift omega)) ∧
              (Measurable fun (omega : CutoffSample d) =>
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                        (superposedGradConst d)
                        (fun (eta : CutoffSample d) =>
                          waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                              (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                            (2 : ℕ))
                        (translateCutoffSample shift omega)) ∧
                ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                  ENNReal.ofReal
                      (∑ j : Fin d,
                        ∑' (n : ℕ),
                          probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                            (superposedGradConst d)
                            (fun (eta : CutoffSample d) =>
                              waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                  (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                                (2 : ℕ))
                            (translateCutoffSample shift omega)) =
                    ∑ j : Fin d,
                      ∑' (n : ℕ),
                        ENNReal.ofReal
                          (probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                            (superposedGradConst d)
                            (fun (eta : CutoffSample d) =>
                              waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                  (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                                (2 : ℕ))
                            (translateCutoffSample shift omega))

private theorem upperWaveTailTraceE12Consumption_momentBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ},
    (0 : ℝ) < sigma →
    sigma ≤ (1 / 2 : ℝ) →
    (2 : ℕ) ≤ d →
    let shift : Vec d := triadicCubeShift R;
    let alpha : ℝ :=
    upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB);
    let beta : ℝ := upperProfileTailSigma sigma;
    let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB;
    let G : ℝ := Book.Ch04.gammaProductConst alpha beta;
    Frozen.Section3.inductionState M (R.scale - (1 : ℤ)) E →
    (0 : ℝ) < upperProfileSigma sigma →
    upperProfileSigma sigma ≤ (1 / 2 : ℝ) →
    upperProfileSigma sigma ≤ (1 / 8 : ℝ) →
    Real.exp (badClustersConst d / upperProfileSigma sigma) ≤ (↑E : ℝ) →
    badClustersConst d / bfaProfileB ≤ (↑E : ℝ) →
    (4 : ℝ) ≤ (↑E : ℝ) →
    BadEvents.unitGate M →
    M.gamma ≤ (1 / 20 : ℝ) →
    (↑E : ℝ)⁻¹ ^ (2 : ℕ) ≤ Disorder.cstar M →
    M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ) →
    M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma →
    M.gamma / (2 : ℝ) ≤ bfaProfileB * sigma →
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma alpha)
    (fun (omega : CutoffSample d) =>
    slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma
    (translateCutoffSample shift omega))
    AP ∧
    (∀ (omega : CutoffSample d),
    (0 : ℝ) ≤
    slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma
    (translateCutoffSample shift omega)) ∧
    (0 : ℝ) ≤ AP ∧
    AP ≤ superposedFluxHsepConst ^ (3 : ℝ) ∧
    (0 : ℝ) ≤ G ∧
    G ≤ (64 : ℝ) ∧
    (2 : ℝ) / upperProfileSigma sigma /
    ((2 : ℝ) + (2 : ℝ) / upperProfileSigma sigma) =
    beta := by
  intro d M m R E sigma hsigma0 hsigma hd shift alpha beta AP G hSroot hsigmaProfile0 hsigmaProfileHalf hsigmaProfileEighth hEexp hEb hE4 hunit hgamma20 hinvSq hgammaGate hgammaProfile hgammaHalf
  have hgammaB : M.gamma ≤ bfaProfileB := by
    calc
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma := hgammaProfile
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsigma
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
      _ = (3 / 4 : ℝ) * bfaProfileB := by ring
      _ ≤ 1 * bfaProfileB :=
        mul_le_mul_of_nonneg_right (by norm_num) bfaProfileB_pos.le
      _ = bfaProfileB := one_mul _
  have hrawP := isBigOWith_gammaSigma_slstarPowerTerm_of_gates
    (m := R.scale) (E := (E : ℝ))
    (sigma := upperProfileSigma sigma) (b := bfaProfileB) (gam := M.gamma)
    M hd E.property hSroot hsigmaProfile0 hsigmaProfileHalf bfaProfileB_pos
    bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20 hinvSq hEb
    hgammaGate M.shellPrefix.gamma_pos
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
  have hP :=
    Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift hPmeas hrawP'
  have hP0 : ∀ omega : CutoffSample d,
      0 ≤ slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
        (translateCutoffSample shift omega) := fun omega =>
    slstarPowerTerm_nonneg M R.scale (E : ℝ) bfaProfileB M.gamma _
  have hAP0 : 0 ≤ AP := by
    dsimp only [AP]
    exact Real.rpow_nonneg (hsepAmplitude_pos _ _).le _
  have hAP : AP ≤ superposedFluxHsepConst ^ (3 : ℝ) := by
    dsimp only [AP]
    exact hsepAmplitude_rpow_bfaPower_le_profile_cube
      hsigmaProfile0 hsigmaProfileEighth hgammaB
  have halpha0 : 0 < alpha := by
    dsimp only [alpha]
    have hnum : 0 < 2 * (M.gamma / 2) + 2 * bfaProfileB :=
      add_pos_of_nonneg_of_pos
        (mul_nonneg (by norm_num)
          (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num)))
        (mul_pos (by norm_num) bfaProfileB_pos)
    have hden : 0 <
        (2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB :=
      div_pos hnum bfaProfileB_pos
    exact div_pos (upperProfileBaseSigma_pos hsigma0 hsigma) hden
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact upperProfileTailSigma_pos hsigma0 hsigma
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hG : G ≤ 64 := by
    have htarget := upperProfileTargetSigma_le_collarPower_mul_tail
      hsigma0 hsigma (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num))
      bfaProfileB_pos hgammaHalf
    have hprod0 : 0 < alpha * beta / (alpha + beta) :=
      div_pos (mul_pos halpha0 hbeta0) (add_pos halpha0 hbeta0)
    have htargetLower : (1 : ℝ) / 6 ≤ upperProfileTargetSigma sigma := by
      rw [upperProfileTargetSigma]
      linarith only [hsigma]
    have hprodLower : (1 : ℝ) / 6 ≤ alpha * beta / (alpha + beta) := by
      exact htargetLower.trans (by simpa only [alpha, beta] using htarget)
    have hmul := mul_le_mul_of_nonneg_left hprodLower
      (by norm_num : (0 : ℝ) ≤ 6)
    have hone : 1 ≤ 6 * (alpha * beta / (alpha + beta)) := by
      norm_num at hmul ⊢
      exact hmul
    have hinv : (alpha * beta / (alpha + beta))⁻¹ ≤ (6 : ℝ) :=
      (inv_le_iff_one_le_mul₀ hprod0).2 hone
    dsimp only [G]
    change (2 : ℝ) ^ ((alpha * beta / (alpha + beta))⁻¹) ≤ 64
    calc
      (2 : ℝ) ^ ((alpha * beta / (alpha + beta))⁻¹) ≤
          (2 : ℝ) ^ (6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hinv
      _ = 64 := by norm_num
  have htailExponent :
      (2 / upperProfileSigma sigma) /
          (2 + 2 / upperProfileSigma sigma) = beta := by
    dsimp only [beta]
    unfold upperProfileTailSigma upperProfileSigma
    have hs : sigma ≠ 0 := ne_of_gt hsigma0
    have hden : 1 + sigma / 4 ≠ 0 := by positivity
    field_simp [hs, hden]
    ring
  exact ⟨hP, hP0, hAP0, hAP, hG0, hG, htailExponent⟩

private theorem upperWaveTailTraceE12Consumption_comparisonBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ} (_ : (0 : ℝ) < sigma)
      (_ : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let capGrowth : ℝ := probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ * (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ));
      let D₀ : ℝ := probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) * fixed * capGrowth;
      let B₀ : ℝ := D₀ * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (waveC ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) * Z));
      let B : ℕ → ℝ := fun (n : ℕ) => B₀ * whitneyDecayRatio ^ n;
      ∀ (_ : (0 : ℝ) ≤ fixed),
        (0 : ℝ) ≤ capGrowth ∧ (0 : ℝ) ≤ D₀ ∧ (0 : ℝ) < waveTailProfileConst d ∧ (0 : ℝ) < Z ∧ ∀ (n : ℕ), (0 : ℝ) < B n := by
  intro d M E _ hsigma0 hd k₀ waveC _ _ Z fixed capGrowth D₀ B₀ B hfixed0
  have hcapGrowth0 : 0 ≤ capGrowth := by
    dsimp only [capGrowth]
    exact mul_nonneg
      (probeSharpCollarBandMeanCapQuarter_nonneg M (E : ℝ) k₀)
      (Real.rpow_nonneg (by norm_num) _)
  have hD₀0 : 0 ≤ D₀ := by
    dsimp only [D₀]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M) (by positivity))
        hfixed0)
      hcapGrowth0
  have hwaveProfile : 0 < waveTailProfileConst d := by
    have hdR : 0 < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
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
          (sq_pos_of_pos hdR))
        geometricConcentrationConst_pos
    rw [waveTailProfileConst]
    exact mul_pos (by norm_num)
      (mul_pos (by norm_num)
        (mul_pos (mul_pos hgain hhead)
          (mul_pos (hsepAmplitude_pos _ _)
            (mul_pos (by norm_num) (inv_pos.mpr bfaProfileB_pos)))))
  have hwaveC : 0 < waveC := by
    dsimp only [waveC]
    positivity
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hB₀ : 0 < B₀ := by
    have hmean : 0 < probeMeanGoodWaveConst M := by
      have hratio : (3 : ℝ) ^ (2 * (1 / 4 : ℝ) - 1) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      have hsimplex : 0 < simplexCrudeConst d (1 / 4) := by
        rw [simplexCrudeConst]
        exact div_pos (by positivity) (sub_pos.mpr hratio)
      have hW : 0 < probeSimplexW1Const d := by
        rw [probeSimplexW1Const]
        positivity
      have hsens : 0 < probeSimplexMeanSensitivityConst d := by
        rw [probeSimplexMeanSensitivityConst]
        exact mul_pos
          (mul_pos (by norm_num)
            (Algsuperdiff.Section3.Provider.BadEvents.bigLambdaSensitivityConst_pos hd))
          (sq_pos_of_pos hW)
      rw [probeMeanGoodWaveConst]
      exact mul_pos (mul_pos (mul_pos (by norm_num) hsimplex) hsens)
        (inv_pos.mpr
          (Algsuperdiff.Section3.Disorder.cstar_characterization M).1)
    have hdR : 0 < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
    have hgrad : 0 < superposedGradConst d :=
      lt_of_lt_of_le zero_lt_one
        (one_le_superposedGradConst (le_trans (by norm_num) hd))
    have hmass : 0 < probeSharpCollarBandMeanMassQuarterConst d := by
      rw [probeSharpCollarBandMeanMassQuarterConst]
      exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))
    have hcapEnvelope : 0 <
        probeSharpCollarBandMeanCapEnvelope M (E : ℝ) k₀ := by
      rw [probeSharpCollarBandMeanCapEnvelope]
      positivity
    have hcap : 0 < probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ := by
      rw [probeSharpCollarBandMeanCapQuarter]
      exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hcapEnvelope)
    have hfixed : 0 < fixed := by
      dsimp only [fixed]
      positivity
    have hcapGrowth : 0 < capGrowth := by
      dsimp only [capGrowth]
      positivity
    have hD : 0 < D₀ := by
      dsimp only [D₀]
      exact mul_pos (mul_pos (mul_pos hmean (by positivity)) hfixed) hcapGrowth
    dsimp only [B₀]
    exact mul_pos hD
      (mul_pos
        (mul_pos (by positivity)
          (Real.rpow_pos_of_pos superposedFluxHsepConst_pos _))
        (mul_pos
          (mul_pos (sq_pos_of_pos hwaveC)
            (sq_pos_of_pos (inv_pos.mpr hsigma0))) hZ))
  have hBpos : ∀ n, 0 < B n := fun n => by
    dsimp only [B]
    exact mul_pos hB₀ (pow_pos (by
      rw [whitneyDecayRatio]
      exact Real.rpow_pos_of_pos (by norm_num) _) n)
  exact ⟨hcapGrowth0, hD₀0, hwaveProfile, hZ, hBpos⟩

private theorem upperWaveTailTraceE12Consumption_comparisonBounds2 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) {sigma Cup : ℝ} (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : (2 : ℕ) ≤ d),
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let K : ℝ :=
        (1 : ℝ) +
          (↑d : ℝ) * upperAfterBandRareTriangleConst * probeMeanGoodWaveDimensionConst d * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                  fixed *
                collarBandMeanTunedCapPrefactor d *
              ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ (2 : ℕ)) *
            ((1 : ℝ) - whitneyDecayRatio)⁻¹;
      ∀ (_ : (0 : ℝ) < rate) (_ : (0 : ℝ) ≤ fixed)
        (_ :
          max (max (profileAuxiliaryConst d) (collarBandMeanDepthThreshold d))
              ((1 : ℝ) + (2 : ℝ) * (K * (rate / (2 : ℝ))⁻¹ + (8 : ℝ)) * rate⁻¹) ≤
            Cup)
        (_ : profileAuxiliaryConst d ≤ Cup),
        (0 : ℝ) ≤ K ∧
          (1 : ℝ) ≤ Cup ∧
            (0 : ℝ) < Cup ∧
              K * (rate / (2 : ℝ))⁻¹ + (8 : ℝ) ≤ rate / (2 : ℝ) * Cup ∧
                max (Real.exp (profileAuxiliaryConst d / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ) ∧
                  Real.exp (profileAuxiliaryConst d / sigma) ≤ (↑E : ℝ) ∧
                    M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ) ∧
                      Cup ≤ Xpar ∧
                        collarBandMeanDepthThreshold d ≤ Xpar ∧
                          Frozen.Section3.inductionState M (R.scale - (1 : ℤ)) E ∧
                            (0 : ℝ) < upperProfileSigma sigma ∧
                              upperProfileSigma sigma ≤ (1 / 2 : ℝ) ∧
                                upperProfileSigma sigma ≤ (1 / 8 : ℝ) ∧
                                  Real.exp (badClustersConst d / upperProfileSigma sigma) ≤ (↑E : ℝ) ∧
                                    badClustersConst d / bfaProfileB ≤ (↑E : ℝ) := by
  intro d M m k R hR E hS sigma Cup hsigma0 hsigma hmax hEgamma hd waveC Xpar rate fixed K hrate hfixed0 houtput haux
  have hdepth : collarBandMeanDepthThreshold d ≤ Cup :=
    (le_max_right _ _).trans ((le_max_left _ _).trans houtput)
  have hbranch : 1 + 2 * (K * (rate / 2)⁻¹ + 8) * rate⁻¹ ≤ Cup :=
    (le_max_right _ _).trans houtput
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    have hdimConst : 0 ≤ probeMeanGoodWaveDimensionConst d := by
      rw [probeMeanGoodWaveDimensionConst]
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
        (probeSimplexMeanSensitivityConst_nonneg hd)
    have hinvRatio : 0 ≤ (1 - whitneyDecayRatio)⁻¹ :=
      (inv_pos.mpr (sub_pos.mpr whitneyDecayRatio_lt_one)).le
    have hA : 0 ≤ (d : ℝ) * upperAfterBandRareTriangleConst *
        probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed *
        collarBandMeanTunedCapPrefactor d *
        (64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2) *
        (1 - whitneyDecayRatio)⁻¹ := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (Nat.cast_nonneg d) (by
                    rw [upperAfterBandRareTriangleConst]
                    positivity))
                  hdimConst)
                (by positivity))
              hfixed0)
            (collarBandMeanTunedCapPrefactor_nonneg d))
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (Real.rpow_nonneg superposedFluxHsepConst_pos.le _))
            (sq_nonneg waveC)))
        hinvRatio
    linarith only [hA]
  have hCup1 : 1 ≤ Cup := by
    have hinvRate : 0 < rate⁻¹ := inv_pos.mpr hrate
    have hhalfInv : 0 ≤ (rate / 2)⁻¹ :=
      (inv_pos.mpr (div_pos hrate (by norm_num))).le
    have hinside : 0 ≤ K * (rate / 2)⁻¹ + 8 := by positivity
    nlinarith only [hbranch, hinside, hinvRate]
  have hCup0 : 0 < Cup := lt_of_lt_of_le zero_lt_one hCup1
  have hchoice : K * (rate / 2)⁻¹ + 8 ≤ (rate / 2) * Cup := by
    have hmul : (rate / 2) *
        (1 + 2 * (K * (rate / 2)⁻¹ + 8) * rate⁻¹) ≤
        (rate / 2) * Cup :=
      mul_le_mul_of_nonneg_left hbranch
        (div_nonneg hrate.le (by norm_num))
    have hcancel : (rate / 2) *
        (2 * (K * (rate / 2)⁻¹ + 8) * rate⁻¹) =
        K * (rate / 2)⁻¹ + 8 := by
      field_simp [ne_of_gt hrate]
    nlinarith only [hmul, hcancel, hrate]
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmaxAux
  have hgammaZ : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hXgate : Cup ≤ Xpar := by
    dsimp only [Xpar]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgammaZ
  have hlarge : collarBandMeanDepthThreshold d ≤ Xpar := hdepth.trans hXgate
  have hscaleR : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by rw [hscaleR]; omega
  have hSroot : Algsuperdiff.Frozen.Section3.inductionState
      M (R.scale - 1) E := inductionState_restrict hroot hS
  have hsigmaProfile0 : 0 < upperProfileSigma sigma := by
    rw [upperProfileSigma]
    positivity
  have hsigmaProfileHalf : upperProfileSigma sigma ≤ 1 / 2 := by
    rw [upperProfileSigma]
    linarith only [hsigma]
  have hsigmaProfileEighth : upperProfileSigma sigma ≤ 1 / 8 := by
    rw [upperProfileSigma]
    linarith only [hsigma]
  have hEexp : Real.exp
      (badClustersConst d / upperProfileSigma sigma) ≤ (E : ℝ) := by
    simpa only [upperProfileSigma, bfaProfileSigma] using
      exp_badClustersConst_div_bfaProfileSigma_le_of_profileAuxiliaryGate
        hsigma0 hexp
  have hEb : badClustersConst d / bfaProfileB ≤ (E : ℝ) :=
    badClustersConst_div_bfaProfileB_le_of_profileAuxiliaryGate
      hsigma0 hsigma hexp
  exact ⟨hK0, hCup1, hCup0, hchoice, hmaxAux, hexp, hgammaZ, hXgate, hlarge, hSroot,
    hsigmaProfile0, hsigmaProfileHalf, hsigmaProfileEighth, hEexp, hEb⟩

private theorem upperWaveTailTraceE12Consumption_comparisonBounds3 : upperWaveTailTraceE12Consumption_comparisonBounds3_statement := by
  intro d M E sigma hsigma0 hsigma _ _ waveC _ _ Z fixed capGrowth D₀ B₀ K hfixed0 hcapGrowth0 hcap hmeanDim hpoly0
  have hrawScale :
      (d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)) ≤
      K * (((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z) := by
    have htri := gammaTriangleConst_upperProfileTarget_le hsigma0 hsigma
    have hinvRatio : 0 ≤ (1 - whitneyDecayRatio)⁻¹ :=
      (inv_pos.mpr (sub_pos.mpr whitneyDecayRatio_lt_one)).le
    have hfive0 : 0 ≤ 5 * (d : ℝ) ^ 2 := by positivity
    have hupper0 : 0 ≤ upperAfterBandRareTriangleConst := by
      rw [upperAfterBandRareTriangleConst]
      positivity
    have hwaveFactor0 : 0 ≤
        64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2 :=
      mul_nonneg
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg superposedFluxHsepConst_pos.le _))
        (sq_nonneg waveC)
    have hprefix :
        (d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
            probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed ≤
          (d : ℝ) * upperAfterBandRareTriangleConst *
            probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed := by
      have h₁ := mul_le_mul_of_nonneg_left htri (Nat.cast_nonneg d)
      have h₂ := mul_le_mul_of_nonneg_right h₁ hmeanDim
      have h₃ := mul_le_mul_of_nonneg_right h₂ hfive0
      exact mul_le_mul_of_nonneg_right h₃ hfixed0
    have htargetPrefix0 : 0 ≤
        (d : ℝ) * upperAfterBandRareTriangleConst *
          probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg d) hupper0) hmeanDim)
          hfive0)
        hfixed0
    have hcapScaled :
        ((d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
            probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed) *
            capGrowth ≤
          ((d : ℝ) * upperAfterBandRareTriangleConst *
            probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed) *
            collarBandMeanTunedCapPrefactor d :=
      mul_le_mul hprefix hcap hcapGrowth0 htargetPrefix0
    have hcoeff :
        (d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
            probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed *
            capGrowth *
            (64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2) *
            (1 - whitneyDecayRatio)⁻¹ ≤
          (d : ℝ) * upperAfterBandRareTriangleConst *
            probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed *
            collarBandMeanTunedCapPrefactor d *
            (64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2) *
            (1 - whitneyDecayRatio)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcapScaled hwaveFactor0) hinvRatio
    have hcoeffK :
        (d : ℝ) * upperAfterBandRareTriangleConst *
            probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed *
            collarBandMeanTunedCapPrefactor d *
            (64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2) *
            (1 - whitneyDecayRatio)⁻¹ ≤ K := by
      dsimp only [K]
      exact le_add_of_nonneg_left zero_le_one
    dsimp only [B₀, D₀]
    rw [probeMeanGoodWaveConst_eq_dimension_mul_cstarInv]
    calc
      (d : ℝ) *
          (gammaTriangleConst (upperProfileTargetSigma sigma) *
            ((probeMeanGoodWaveDimensionConst d *
                (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
                (5 * (d : ℝ) ^ 2) * fixed * capGrowth) *
              (64 * superposedFluxHsepConst ^ (3 : ℝ) *
                (waveC ^ 2 * sigma⁻¹ ^ 2 * Z)) *
              (1 - whitneyDecayRatio)⁻¹)) =
        ((d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
          probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed *
          capGrowth * (64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2) *
          (1 - whitneyDecayRatio)⁻¹) *
          (((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z) := by
        ring
      _ ≤ ((d : ℝ) * upperAfterBandRareTriangleConst *
          probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed *
          collarBandMeanTunedCapPrefactor d *
          (64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2) *
          (1 - whitneyDecayRatio)⁻¹) *
          (((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z) := by
        exact mul_le_mul_of_nonneg_right hcoeff hpoly0
      _ ≤ K *
          (((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z) := by
        exact mul_le_mul_of_nonneg_right hcoeffK hpoly0
  have hE0 : 0 ≤ (E : ℝ) := E.property.trans' zero_le_one
  have hsigmaInv0 : 0 ≤ sigma⁻¹ := (inv_pos.mpr hsigma0).le
  exact ⟨hrawScale, hE0, hsigmaInv0⟩

private theorem upperWaveTailTraceE12Consumption_comparisonBounds4 : upperWaveTailTraceE12Consumption_comparisonBounds4_statement := by
  intro d M m k R E sigma Cup hd k₀ shift _ Xpar rate Z _ _ _ B₀ _ X K hrate hK0 hCup0 hchoice hXgate hX0 hXsumAE hXsumMeas hfun hrawScale hpolyX
  have hhalf : 0 < rate / 2 := div_pos hrate (by norm_num)
  have hpoly :
      ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z ≤
        (rate / 2)⁻¹ * Real.exp (-((rate / 2) * Xpar)) := by
    calc
      ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z ≤
          Xpar * Real.exp (-(rate * Xpar)) := by
        dsimp only [Z]
        exact mul_le_mul_of_nonneg_right hpolyX (Real.exp_pos _).le
      _ ≤ ((rate / 2)⁻¹ * Real.exp ((rate / 2) * Xpar)) *
            Real.exp (-(rate * Xpar)) :=
        mul_le_mul_of_nonneg_right (Real.le_inv_mul_exp Xpar hhalf)
          (Real.exp_pos _).le
      _ = (rate / 2)⁻¹ * Real.exp (-((rate / 2) * Xpar)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
  have hhalfScale :
      (d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)) ≤
      (K * (rate / 2)⁻¹) * Real.exp (-((rate / 2) * Xpar)) := by
    exact hrawScale.trans <| (mul_le_mul_of_nonneg_left hpoly hK0).trans_eq (by ring)
  have hpref := prefactor_mul_exp_le_frozenRare_pow
    (mul_nonneg hK0 (inv_nonneg.mpr hhalf.le)) hCup0 hXgate hchoice
  have hterminalScale :
      (d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)) ≤
      (Real.exp (-(Cup⁻¹ * Xpar))) ^ 8 :=
    hhalfScale.trans (by
      simpa only [mul_assoc] using hpref)
  have hthree : 1 ≤ (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have hfinalScale :
      (d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)) ≤
      (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
        (Real.exp (-(Cup⁻¹ * Xpar))) ^ 8 :=
    hterminalScale.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hthree
        (pow_nonneg (Real.exp_pos _).le 8))
  have hliteral0 : ∀ omega,
      0 ≤ ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega) := by
    intro omega
    rw [show (∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega)) =
        (d : ℝ) * ∑' n, X n omega by exact congrFun hfun omega]
    exact mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg fun n => hX0 n omega)
  have hliteralMeas : Measurable (fun omega =>
      ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega)) := by
    rw [hfun]
    exact hXsumMeas.const_mul d
  have hbridge : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (∑ j : Fin d, ∑' n : ℕ,
            probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
              k₀ n (m - 1) (basisVec j) (superposedGradConst d)
              (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
              (translateCutoffSample shift omega)) =
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
            k₀ n (m - 1) (basisVec j) (superposedGradConst d)
            (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
              (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
            (translateCutoffSample shift omega)) := by
    filter_upwards [hXsumAE] with omega hsum
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => tsum_nonneg fun n =>
      probeSharpFramedCollarWavePart_nonneg hd M R.scale (E : ℝ)
        bfaProfileB k₀ n (m - 1) (basisVec j) (superposedGradConst d)
        (fun eta => sq_nonneg _) (translateCutoffSample shift omega))]
    exact Finset.sum_congr rfl fun j _ =>
      ENNReal.ofReal_tsum_of_nonneg
        (fun n => probeSharpFramedCollarWavePart_nonneg hd M R.scale (E : ℝ)
          bfaProfileB k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => sq_nonneg _) (translateCutoffSample shift omega))
        (by
          simpa only [X, probeSharpFramedCollarWavePart, vecNormSq_basisVec]
            using hsum)
  exact ⟨hfinalScale, hliteral0, hliteralMeas, hbridge⟩

private theorem upperWaveTailTraceE12Consumption_comparisonBounds5 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ}
      (_ : (0 : ℝ) < sigma) (_ : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let X : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j₀)
          (superposedGradConst d)
          (fun (eta : CutoffSample d) =>
            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
              (2 : ℕ))
          (translateCutoffSample shift omega);
      ∀ (_ : (0 : ℝ) < waveTailProfileConst d) (_ : (0 : ℝ) < upperProfileSigma sigma)
        (_ : upperProfileSigma sigma ≤ (1 / 2 : ℝ))
        (_ : (3 : ℝ) ^ (-((↑d : ℝ) / (4 : ℝ)) * (↑k₀ : ℝ)) ≤ Z),
        (∀ (n : ℕ),
            waveTailGainScale d bfaProfileB (upperProfileSigma sigma) ((2 : ℝ) / upperProfileSigma sigma) R.scale
                  (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) ^
                (2 : ℕ) ≤
              waveC ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) * Z) ∧
          ∀ (n : ℕ) (omega : CutoffSample d), (0 : ℝ) ≤ X n omega := by
  intro d M m k R E sigma hsigma0 hd k₀ _ waveC _ _ Z j₀ X hwaveProfile hsigmaProfile0 hsigmaProfileHalf hdepthWave
  have hgain (n : ℕ) :
      waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
          (2 / upperProfileSigma sigma) R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) ≤
        waveC * sigma⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
    have hgap : R.scale - probeSharpLayerAnchor R.scale bfaProfileB k₀ n =
        (whitneyScaleSeq bfaProfileB 0 (k₀ + n) n : ℕ) := by
      rw [probeSharpLayerAnchor, whitneyScaleSeq]
      push_cast
      ring
    have hprofile :
        waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
            (2 / upperProfileSigma sigma) R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) ≤
          waveTailProfileConst d * (upperProfileSigma sigma)⁻¹ *
            (3 : ℝ) ^
              (-((d : ℝ) / 8) * ((k₀ + n : ℕ) : ℝ)) :=
      waveTailGainScale_profile_le
        (M := M) (sigma := upperProfileSigma sigma)
        (lout := R.scale)
        (ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
        (k₀ := k₀ + n) (k := n)
        hsigmaProfile0 hsigmaProfileHalf hgap
    have hkn : (k₀ : ℝ) ≤ ((k₀ + n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right k₀ n
    have hdecay :
        (3 : ℝ) ^ (-((d : ℝ) / 8) * ((k₀ + n : ℕ) : ℝ)) ≤
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hd0 : 0 ≤ (d : ℝ) / 8 := by positivity
      exact mul_le_mul_of_nonpos_left hkn (neg_nonpos.mpr hd0)
    have hinv : (upperProfileSigma sigma)⁻¹ = 4 * sigma⁻¹ := by
      rw [upperProfileSigma]
      field_simp [ne_of_gt hsigma0]
    calc
      waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
          (2 / upperProfileSigma sigma) R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) ≤
        waveTailProfileConst d * (upperProfileSigma sigma)⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * ((k₀ + n : ℕ) : ℝ)) := hprofile
      _ ≤ waveTailProfileConst d * (upperProfileSigma sigma)⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left hdecay
          (mul_nonneg hwaveProfile.le
            (inv_nonneg.mpr hsigmaProfile0.le))
      _ = waveC * sigma⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ)) := by
        rw [hinv]
        dsimp only [waveC]
        ring
  have hgainSq (n : ℕ) :
      waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
          (2 / upperProfileSigma sigma) R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) ^ 2 ≤
        waveC ^ 2 * sigma⁻¹ ^ 2 * Z := by
    let A := waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
      (2 / upperProfileSigma sigma) R.scale
      (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
    have hA0 : 0 ≤ A := by
      dsimp only [A]
      exact waveTailGainScale_nonneg _ _ _ _ _ _
    have hsq := pow_le_pow_left₀ hA0 (hgain n) 2
    have hpowers :
        ((3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ))) ^ 2 =
          (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    calc
      waveTailGainScale d bfaProfileB (upperProfileSigma sigma)
          (2 / upperProfileSigma sigma) R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) ^ 2 ≤
        (waveC * sigma⁻¹ *
          (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ))) ^ 2 := hsq
      _ = waveC ^ 2 * sigma⁻¹ ^ 2 *
          (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) := by
        calc
          (waveC * sigma⁻¹ *
              (3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ))) ^ 2 =
            waveC ^ 2 * sigma⁻¹ ^ 2 *
              ((3 : ℝ) ^ (-((d : ℝ) / 8) * (k₀ : ℝ))) ^ 2 := by ring
          _ = _ := by rw [hpowers]
      _ ≤ waveC ^ 2 * sigma⁻¹ ^ 2 * Z :=
        mul_le_mul_of_nonneg_left hdepthWave
          (mul_nonneg (sq_nonneg waveC) (sq_nonneg sigma⁻¹))
  have hX0 : ∀ n omega, 0 ≤ X n omega := fun n omega => by
    dsimp only [X]
    exact probeSharpFramedCollarWavePart_nonneg hd M R.scale (E : ℝ)
      bfaProfileB k₀ n (m - 1) (basisVec j₀) (superposedGradConst d)
      (fun eta => sq_nonneg _) _
  exact ⟨hgainSq, hX0⟩

private theorem upperWaveTailTraceE12Consumption_momentBounds2 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ}
      (_ : (0 : ℝ) < sigma) (_ : sigma ≤ (1 / 2 : ℝ)) (_ : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let capGrowth : ℝ := probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ * (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ));
      let D₀ : ℝ := probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) * fixed * capGrowth;
      let B₀ : ℝ := D₀ * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (waveC ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) * Z));
      let B : ℕ → ℝ := fun (n : ℕ) => B₀ * whitneyDecayRatio ^ n;
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let X : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j₀)
          (superposedGradConst d)
          (fun (eta : CutoffSample d) =>
            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
              (2 : ℕ))
          (translateCutoffSample shift omega);
      ∀ (_ : (0 : ℝ) < Z) (_ : ∀ (n : ℕ), (0 : ℝ) < B n) (_ : Summable B)
        (_ : collarBandMeanDepthThreshold d ≤ Xpar)
        (_ :
          ∀ (n : ℕ) (omega : CutoffSample d),
            (0 : ℝ) ≤
              (fun (n : ℕ) (omega : CutoffSample d) =>
                  probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                    (m - (1 : ℤ)) (basisVec ⟨(0 : ℕ), (by positivity)⟩) (superposedGradConst d)
                    (fun (eta : CutoffSample d) =>
                      waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                          (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                        (2 : ℕ))
                    (translateCutoffSample (triadicCubeShift R) omega))
                n omega)
        (_ : ∀ (n : ℕ), Measurable (X n))
        (_ :
          ∀ (n : ℕ),
            IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma)) (X n)
              (B n)),
        (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            Summable fun (n : ℕ) => X n omega) ∧
          (Measurable fun (omega : CutoffSample d) => ∑' (n : ℕ), X n omega) ∧
            ((fun (omega : CutoffSample d) =>
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                        (superposedGradConst d)
                        (fun (eta : CutoffSample d) =>
                          waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                              (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                            (2 : ℕ))
                        (translateCutoffSample shift omega)) =
                fun (omega : CutoffSample d) => (↑d : ℝ) * ∑' (n : ℕ), X n omega) ∧
              IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
                  (fun (omega : CutoffSample d) =>
                    ∑ j : Fin d,
                      ∑' (n : ℕ),
                        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                          (superposedGradConst d)
                          (fun (eta : CutoffSample d) =>
                            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
                              (2 : ℕ))
                          (translateCutoffSample shift omega))
                  ((↑d : ℝ) *
                    (gammaTriangleConst (upperProfileTargetSigma sigma) * (B₀ * ((1 : ℝ) - whitneyDecayRatio)⁻¹))) ∧
                capGrowth ≤ collarBandMeanTunedCapPrefactor d ∧
                  (0 : ℝ) ≤ probeMeanGoodWaveDimensionConst d ∧ (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ * sigma⁻¹ ^ (2 : ℕ) * Z := by
  intro d M m R E sigma hsigma0 hsigma hd k₀ shift _ Xpar _ Z _ capGrowth _ B₀ B _ X hZ hBpos hBsum hlarge hX0 hXmeas hterm
  have hcoord := Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
    (upperProfileTargetSigma_pos hsigma0 hsigma) hX0 hXmeas hBpos hBsum
    hterm (by
      rw [show B = fun n : ℕ => B₀ * whitneyDecayRatio ^ n by rfl,
        tsum_mul_left,
        tsum_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one])
  have hXsumAE : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => X n omega :=
    Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      (upperProfileTargetSigma_pos hsigma0 hsigma) hX0
      (fun n => (hXmeas n).aemeasurable) hBpos hBsum hterm
  have hcoordTarget : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3))
      (fun omega => ∑' n, X n omega)
      (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)) := by
    simpa only [upperProfileTargetSigma] using hcoord
  have hXsumMeas : Measurable (fun omega => ∑' n, X n omega) := by
    have hnn := (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (hXmeas n).real_toNNReal).coe_nnreal_real
    convert hnn using 1
    funext omega
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by
      rw [Real.toNNReal_of_nonneg (hX0 n omega)]
      rfl
  have hfun : (fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega)) =
      fun omega => (d : ℝ) * ∑' n, X n omega := by
    funext omega
    simp only [X, probeSharpFramedCollarWavePart, vecNormSq_basisVec,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have htraceRaw := hcoordTarget.const_mul (Nat.cast_nonneg d)
  have htrace : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3))
      (fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega))
      ((d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹))) := by
    rw [hfun]
    simpa only [mul_assoc] using htraceRaw
  have hcap : capGrowth ≤ collarBandMeanTunedCapPrefactor d := by
    have hraw := probeSharpCollarBandMeanTunedCapGrowth_le_exp M
      (lt_of_lt_of_le zero_lt_one E.property) (by
        simpa only [Xpar] using hlarge)
    have hcapRateX0 : 0 ≤ collarBandMeanTunedDecayRate d * Xpar :=
      mul_nonneg (collarBandMeanTunedDecayRate_pos d).le
        (mul_nonneg (sq_nonneg (E : ℝ)⁻¹)
          (inv_nonneg.mpr M.shellPrefix.gamma_pos.le))
    have hexpOne : Real.exp (-(collarBandMeanTunedDecayRate d * Xpar)) ≤ 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (neg_nonpos.mpr hcapRateX0)
    have hweaken := mul_le_mul_of_nonneg_left hexpOne
      (collarBandMeanTunedCapPrefactor_nonneg d)
    have hcapRaw : capGrowth ≤ collarBandMeanTunedCapPrefactor d *
        Real.exp (-(collarBandMeanTunedDecayRate d * Xpar)) := by
      simpa only [capGrowth, k₀, Xpar] using hraw
    have hcapWeak : collarBandMeanTunedCapPrefactor d *
        Real.exp (-(collarBandMeanTunedDecayRate d * Xpar)) ≤
        collarBandMeanTunedCapPrefactor d := by
      simpa only [mul_one] using hweaken
    exact hcapRaw.trans hcapWeak
  have hmeanDim : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  have hpoly0 : 0 ≤
      ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z :=
    mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr
          (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le)
        (sq_nonneg sigma⁻¹)) hZ.le
  exact ⟨hXsumAE, hXsumMeas, hfun, htrace, hcap, hmeanDim, hpoly0⟩

private theorem upperWaveTailTraceE12Consumption_estimate1 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ}
      {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)))
      {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ} (hsigma0 : (0 : ℝ) < sigma) (hsigma : sigma ≤ (1 / 2 : ℝ))
      (hd : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let alpha : ℝ :=
        upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB);
      let beta : ℝ := upperProfileTailSigma sigma;
      let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB;
      let G : ℝ := Book.Ch04.gammaProductConst alpha beta;
      let waveC : ℝ := (4 : ℝ) * waveTailProfileConst d;
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      let fixed : ℝ :=
        (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanMassQuarterConst d * (3 : ℝ) ^ (1 / 16 : ℝ);
      let capGrowth : ℝ := probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ * (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ));
      let D₀ : ℝ := probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) * fixed * capGrowth;
      let B₀ : ℝ := D₀ * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * (waveC ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) * Z));
      let B : ℕ → ℝ := fun (n : ℕ) => B₀ * whitneyDecayRatio ^ n;
      let j₀ : Fin d := ⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two hd⟩;
      let X : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j₀)
          (superposedGradConst d)
          (fun (eta : CutoffSample d) =>
            waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^
              (2 : ℕ))
          (translateCutoffSample shift omega);
      ∀ (hD₀0 : (0 : ℝ) ≤ D₀) (hwaveProfile : (0 : ℝ) < waveTailProfileConst d)
        (hSroot : Frozen.Section3.inductionState M (R.scale - (1 : ℤ)) E)
        (hsigmaProfile0 : (0 : ℝ) < upperProfileSigma sigma) (hsigmaProfileHalf : upperProfileSigma sigma ≤ (1 / 2 : ℝ))
        (hEexp : Real.exp (badClustersConst d / upperProfileSigma sigma) ≤ (↑E : ℝ))
        (hEb : badClustersConst d / bfaProfileB ≤ (↑E : ℝ)) (hE4 : (4 : ℝ) ≤ (↑E : ℝ)) (hunit : BadEvents.unitGate M)
        (hgamma20 : M.gamma ≤ (1 / 20 : ℝ)) (hinvSq : (↑E : ℝ)⁻¹ ^ (2 : ℕ) ≤ Disorder.cstar M)
        (hgammaGate : M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ)) (hgammaHalf : M.gamma / (2 : ℝ) ≤ bfaProfileB * sigma)
        (hP :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
            (gammaSigma
              (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB)))
            (fun (omega : CutoffSample d) =>
              slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma (translateCutoffSample (triadicCubeShift R) omega))
            (hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB))
        (hP0 :
          ∀ (omega : CutoffSample d),
            (0 : ℝ) ≤
              slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma (translateCutoffSample (triadicCubeShift R) omega))
        (hAP0 : (0 : ℝ) ≤ hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB)
        (hAP :
          hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB ≤
            superposedFluxHsepConst ^ (3 : ℝ))
        (hG0 :
          (0 : ℝ) ≤
            Book.Ch04.gammaProductConst
              (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB))
              (upperProfileTailSigma sigma))
        (hG :
          Book.Ch04.gammaProductConst
              (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB))
              (upperProfileTailSigma sigma) ≤
            (64 : ℝ))
        (htailExponent :
          (2 : ℝ) / upperProfileSigma sigma / ((2 : ℝ) + (2 : ℝ) / upperProfileSigma sigma) = upperProfileTailSigma sigma)
        (hgainSq :
          ∀ (n : ℕ),
            waveTailGainScale d bfaProfileB (upperProfileSigma sigma) ((2 : ℝ) / upperProfileSigma sigma) R.scale
                  (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n) ^
                (2 : ℕ) ≤
              ((4 : ℝ) * waveTailProfileConst d) ^ (2 : ℕ) * sigma⁻¹ ^ (2 : ℕ) *
                Real.exp (-(probeSharpWaveTailTunedRate d * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))))
        (n : ℕ),
        IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma)) (X n)
          (B n) := by
  intro d M m k R hR E sigma hsigma0 hsigma hd k₀ shift alpha beta AP G waveC Xpar rate Z fixed capGrowth D₀ B₀ B j₀ X hD₀0 hwaveProfile hSroot hsigmaProfile0 hsigmaProfileHalf hEexp hEb hE4 hunit hgamma20 hinvSq hgammaGate hgammaHalf hP hP0 hAP0 hAP hG0 hG htailExponent hgainSq n
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let T : CutoffSample d → ℝ := fun omega =>
    waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale ell
      (translateCutoffSample shift omega) ^ 2
  let AT : ℝ := waveTailGainScale d bfaProfileB
    (upperProfileSigma sigma) (2 / upperProfileSigma sigma)
    R.scale ell ^ 2
  let D : ℝ := D₀ * whitneyDecayRatio ^ n
  have hsigma2 : 0 < 2 / upperProfileSigma sigma :=
    div_pos (by norm_num) hsigmaProfile0
  have hrawT := isBigOWith_gammaSigma_probeWaveTailTerm_sq_of_gates
    (m := R.scale) M hd E.property hSroot hsigmaProfile0
    hsigmaProfileHalf hsigma2 bfaProfileB_pos bfaProfileB_le_one_eighth
    hEexp hE4 hunit hgamma20 hinvSq hEb hgammaGate R.scale ell
  rw [htailExponent] at hrawT
  have hTmeas : Measurable fun omega : CutoffSample d =>
      waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale ell omega ^ 2 :=
    (measurable_waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale ell).pow_const 2
  have hT :=
    Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift hTmeas hrawT
  have hT0 : ∀ omega, 0 ≤ T omega := fun omega => by
    dsimp only [T]
    exact sq_nonneg _
  have hAT0 : 0 ≤ AT := by dsimp only [AT]; exact sq_nonneg _
  have hproduct := isBigOWith_upperProfileTarget_collarPower_mul_tail
    (mu := (cutoffSampleLaw M).toMeasure)
    (sigma := sigma) (gamma := M.gamma / 2) (b := bfaProfileB)
    hsigma0 hsigma (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num))
    bfaProfileB_pos hgammaHalf hAP0 hAT0 hP0 hT0 hP hT
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg hD₀0 (pow_nonneg whitneyDecayRatio_nonneg n)
  have hmajor := hproduct.const_mul hD0
  have hpoint : ∀ omega, X n omega ≤
      D *
        ((slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
            (translateCutoffSample shift omega)) * T omega) := by
    intro omega
    have hcore := probeSharpCollarBandMeanLayerCore_le_atDepth
      M hR (E : ℝ) k₀ n
        (translateCutoffSample shift omega)
    have houter0 : 0 ≤ probeMeanGoodWaveConst M *
        vecNormSq (basisVec j₀) * (5 * (d : ℝ) ^ 2) := by
      exact mul_nonneg
        (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M)
          (vecNormSq_nonneg (basisVec j₀))) (by positivity)
    have htail0 : 0 ≤ T omega := hT0 omega
    calc
      X n omega =
          (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
            (5 * (d : ℝ) ^ 2)) *
            probeSharpCollarBandMeanLayerCore M R.scale (E : ℝ)
              k₀ n (m - 1) (superposedGradConst d)
              (translateCutoffSample shift omega) * T omega := by
        simp only [X, T, probeSharpFramedCollarWavePart,
          probeSharpCollarBandMeanLayerCore]
        ring
      _ ≤ (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
            (5 * (d : ℝ) ^ 2)) *
          ((4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ)) *
            slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
              (translateCutoffSample shift omega) *
            whitneyDecayRatio ^ n) * T omega :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcore houter0) htail0
      _ = D *
          (slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
            (translateCutoffSample shift omega) * T omega) := by
        simp only [D, D₀, fixed, capGrowth, vecNormSq_basisVec]
        ring
  have hraw : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma)) (X n)
      (D * (G * AP * AT)) := by
    exact isBigOWith_gammaSigma_of_le hpoint (by
      simpa only [G, alpha, beta, AP, AT, T, D, mul_assoc] using hmajor)
  have hGAP : G * AP ≤ 64 * superposedFluxHsepConst ^ (3 : ℝ) :=
    mul_le_mul hG hAP hAP0 (by norm_num)
  have hGAP0 : 0 ≤ G * AP := mul_nonneg hG0 hAP0
  have hAT : AT ≤ waveC ^ 2 * sigma⁻¹ ^ 2 * Z := by
    dsimp only [AT, ell]
    exact hgainSq n
  have htailScale0 : 0 ≤ waveC ^ 2 * sigma⁻¹ ^ 2 * Z := by
    positivity
  have hfactor : G * AP * AT ≤
      64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (waveC ^ 2 * sigma⁻¹ ^ 2 * Z) :=
    mul_le_mul hGAP hAT hAT0
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg superposedFluxHsepConst_pos.le _))
  have hscale : D * (G * AP * AT) ≤ B n := by
    calc
      D * (G * AP * AT) ≤ D *
          (64 * superposedFluxHsepConst ^ (3 : ℝ) *
            (waveC ^ 2 * sigma⁻¹ ^ 2 * Z)) :=
        mul_le_mul_of_nonneg_left hfactor hD0
      _ = B n := by
        simp only [D, B, B₀]
        ring
  exact hraw.mono_scale hscale

private theorem upperWaveTailTraceE12Consumption_estimate2 :
    ∀ {d : ℕ} (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (hd : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let Xpar : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := probeSharpWaveTailTunedRate d;
      let Z : ℝ := Real.exp (-(rate * Xpar));
      (3 : ℝ) ^ (-((↑d : ℝ) / (4 : ℝ)) * (↑k₀ : ℝ)) ≤ Z := by
  intro d M E hd k₀ Xpar rate Z
  have hA0 : 0 ≤ (d : ℝ) / 4 * Real.log 3 := by
    exact mul_nonneg (by positivity)
      (lt_trans zero_lt_one one_lt_log_three).le
  have hlower : collarBandMeanDepthCoeff d * Xpar ≤ (k₀ : ℝ) := by
    dsimp only [Xpar, k₀]
    exact collarBandMeanDepthCoeff_mul_invSq_gammaInv_le_depth M (E : ℝ)
  have hproduct : rate * Xpar ≤
      ((d : ℝ) / 4 * Real.log 3) * (k₀ : ℝ) := by
    dsimp only [rate, probeSharpWaveTailTunedRate]
    calc
      ((d : ℝ) / 4 * Real.log 3 * collarBandMeanDepthCoeff d) * Xpar =
          ((d : ℝ) / 4 * Real.log 3) *
            (collarBandMeanDepthCoeff d * Xpar) := by ring
      _ ≤ ((d : ℝ) / 4 * Real.log 3) * (k₀ : ℝ) :=
        mul_le_mul_of_nonneg_left hlower hA0
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  calc
    Real.log 3 * (-((d : ℝ) / 4) * (k₀ : ℝ)) =
        -(((d : ℝ) / 4 * Real.log 3) * (k₀ : ℝ)) := by ring
    _ ≤ -(rate * Xpar) := neg_le_neg hproduct

private theorem upperWaveTailTraceE12Consumption_momentBounds3 : upperWaveTailTraceE12Consumption_momentBounds3_statement := by
  classical
  intro d M m k R hR E sigma Cup hsigma0 hsigma hmax hd k₀ shift waveC Xpar rate Z fixed capGrowth D₀ B₀ B j₀ X K hrate hfixed0 hcapGrowth0 hD₀0 hwaveProfile hZ hBpos hBsum hK0 hCup1 hCup0 hchoice hgammaZ hXgate hlarge hSroot hsigmaProfile0 hsigmaProfileHalf hEexp hEb hE4 hunit hgamma20 hinvSq hgammaGate hgammaHalf hP hP0 hAP0 hAP hG0 hG htailExponent hdepthWave
  obtain ⟨hgainSq, hX0⟩ :=
    @upperWaveTailTraceE12Consumption_comparisonBounds5 (d) (M) (m) (k) (R) (E) (sigma) (hsigma0)
      (hd) (hwaveProfile) (hsigmaProfile0) (hsigmaProfileHalf) (hdepthWave)
  have hXmeas : ∀ n, Measurable (X n) := fun n => by
    let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
    have hcore :=
      (measurable_probeSharpCollarBandMeanLayerCore M R.scale (E : ℝ)
        k₀ n (m - 1) (superposedGradConst d)).comp
        (measurable_translateCutoffSample shift)
    have htail :=
      ((measurable_waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale ell).pow_const
        (2 : ℕ)).comp (measurable_translateCutoffSample shift)
    have hproduct :=
      (hcore.const_mul
        (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
          (5 * (d : ℝ) ^ 2))).mul htail
    convert hproduct using 1
    funext omega
    simp only [X, ell, probeSharpFramedCollarWavePart,
      probeSharpCollarBandMeanLayerCore, Function.comp_apply, Pi.mul_apply]
    ring
  have hterm : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma)) (X n) (B n)  := @upperWaveTailTraceE12Consumption_estimate1 (d) (M) (m) (k) (R) (hR) (E) (sigma) (hsigma0) (hsigma) (hd) (hD₀0) (hwaveProfile) (hSroot) (hsigmaProfile0) (hsigmaProfileHalf) (hEexp) (hEb) (hE4) (hunit) (hgamma20) (hinvSq) (hgammaGate) (hgammaHalf) (hP) (hP0) (hAP0) (hAP) (hG0) (hG) (htailExponent) (hgainSq)
  obtain ⟨hXsumAE, hXsumMeas, hfun, htrace, hcap, hmeanDim, hpoly0⟩ :=
    (show (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => X n omega) ∧ (Measurable (fun omega => ∑' n, X n omega)) ∧ ((fun omega =>
        ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega)) =
      fun omega => (d : ℝ) * ∑' n, X n omega) ∧ (IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3))
      (fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega))
      ((d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)))) ∧ (capGrowth ≤ collarBandMeanTunedCapPrefactor d) ∧ (0
          ≤ probeMeanGoodWaveDimensionConst d) ∧ (0 ≤
      ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z) from
      @upperWaveTailTraceE12Consumption_momentBounds2 (d) (M) (m) (R) (E) (sigma) (hsigma0)
        (hsigma) (hd) (hZ) (hBpos) (hBsum) (hlarge) (hX0) (hXmeas) (hterm))
  obtain ⟨hrawScale, hE0, hsigmaInv0⟩ :=
    (show ((d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)) ≤
      K * (((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2) * Z)) ∧ (0 ≤ (E : ℝ)) ∧ (0 ≤
        sigma⁻¹) from
      @upperWaveTailTraceE12Consumption_comparisonBounds3 (d) (M) (E) (sigma) (hsigma0) (hsigma)
        (hd) (hfixed0) (hcapGrowth0) (hcap) (hmeanDim) (hpoly0))
  have hsigmaInvE : sigma⁻¹ ≤ (E : ℝ) := by
    calc
      sigma⁻¹ ≤ Cup / sigma := by
        rw [div_eq_mul_inv]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hCup1 hsigmaInv0
      _ ≤ Real.exp (Cup / sigma) := by
        linarith only [Real.add_one_le_exp (Cup / sigma)]
      _ ≤ (E : ℝ) := (le_max_left _ _).trans hmax
  have hsigmaInvSqE : sigma⁻¹ ^ 2 ≤ (E : ℝ) ^ 2 :=
    pow_le_pow_left₀ hsigmaInv0 hsigmaInvE 2
  have hXcube : (E : ℝ) ^ 3 ≤ Xpar := by
    dsimp only [Xpar]
    exact Algsuperdiff.Section3.Provider.Percolation.cube_le_invSq_mul_gammaInv
      M E.property hgammaZ
  have hpolyX :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2 ≤ Xpar := by
    calc
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * sigma⁻¹ ^ 2 ≤
          (E : ℝ) * (E : ℝ) ^ 2 :=
        mul_le_mul ((le_max_right _ _).trans hmax) hsigmaInvSqE
          (sq_nonneg sigma⁻¹) hE0
      _ = (E : ℝ) ^ 3 := by ring
      _ ≤ Xpar := hXcube
  obtain ⟨hfinalScale, hliteral0, hliteralMeas, hbridge⟩ :=
    (show ((d : ℝ) * (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (B₀ * (1 - whitneyDecayRatio)⁻¹)) ≤
      (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
        (Real.exp (-(Cup⁻¹ * Xpar))) ^ 8) ∧ (∀ omega,
      0 ≤ ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega)) ∧ (Measurable (fun omega =>
      ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j) (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
          (translateCutoffSample shift omega))) ∧ (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (∑ j : Fin d, ∑' n : ℕ,
            probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
              k₀ n (m - 1) (basisVec j) (superposedGradConst d)
              (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
              (translateCutoffSample shift omega)) =
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
            k₀ n (m - 1) (basisVec j) (superposedGradConst d)
            (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
              (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
            (translateCutoffSample shift omega))) from
      @upperWaveTailTraceE12Consumption_comparisonBounds4 (d) (M) (m) (k) (R) (E) (sigma) (Cup)
        (hd) (hrate) (hK0) (hCup0) (hchoice) (hXgate) (hX0) (hXsumAE) (hXsumMeas) (hfun)
          (hrawScale) (hpolyX))
  exact ⟨htrace, hfinalScale, hliteral0, hliteralMeas, hbridge⟩

/-- The literal named summand 12, summed over the common-depth Whitney family
and the finite coordinate basis, has the frozen upper-profile bound at the
exact terminal scale.  Summability and measurability are derived internally. -/
theorem isBigOWith_upperProfileTarget_collarWaveTailFiniteTrace
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : probeSharpCollarWaveTailTunedOutputConst d ≤ Cup) :
    let trace := fun omega => ∑ j : Fin d, ∑' n : ℕ,
        probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (superposedGradConst d)
          (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
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
              (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma ((1 - sigma) / 3)) trace
        ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
          (Real.exp (-(Cup⁻¹ *
            ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8) := by
  dsimp only
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let k₀ : ℕ := collarBandMeanDepth M (E : ℝ)
  let shift : Vec d := triadicCubeShift R
  let alpha : ℝ := upperProfileBaseSigma sigma /
    ((2 * (M.gamma / 2) + 2 * bfaProfileB) / bfaProfileB)
  let beta : ℝ := upperProfileTailSigma sigma
  let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
    bfaPower M.gamma bfaProfileB
  let G : ℝ := HCPolySupport.Book.Ch04.gammaProductConst alpha beta
  let waveC : ℝ := 4 * waveTailProfileConst d
  let Xpar : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let rate : ℝ := probeSharpWaveTailTunedRate d
  let Z : ℝ := Real.exp (-(rate * Xpar))
  let fixed : ℝ := 4 * superposedGradConst d ^ 2 *
    probeSharpCollarBandMeanMassQuarterConst d *
    (3 : ℝ) ^ (1 / 16 : ℝ)
  let capGrowth : ℝ :=
    probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ))
  let D₀ : ℝ := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
    fixed * capGrowth
  let B₀ : ℝ := D₀ *
    (64 * superposedFluxHsepConst ^ (3 : ℝ) *
      (waveC ^ 2 * sigma⁻¹ ^ 2 * Z))
  let B : ℕ → ℝ := fun n => B₀ * whitneyDecayRatio ^ n
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let X : ℕ → CutoffSample d → ℝ := fun n omega =>
    probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
      k₀ n (m - 1) (basisVec j₀) (superposedGradConst d)
      (fun eta => waveTailTerm M R.scale (E : ℝ) bfaProfileB R.scale
        (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) eta ^ 2)
      (translateCutoffSample shift omega)
  let K : ℝ := 1 +
    (d : ℝ) * upperAfterBandRareTriangleConst *
      probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) * fixed *
      collarBandMeanTunedCapPrefactor d *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) * waveC ^ 2) *
      (1 - whitneyDecayRatio)⁻¹
  have hrate : 0 < rate := by
    dsimp only [rate, probeSharpWaveTailTunedRate]
    have hdR : 0 < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
    exact mul_pos
      (mul_pos (div_pos hdR (by norm_num))
        (lt_trans zero_lt_one one_lt_log_three))
      (collarBandMeanDepthCoeff_pos d)
  have hfixed0 : 0 ≤ fixed := by
    dsimp only [fixed]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (sq_nonneg _))
        (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
      (Real.rpow_nonneg (by norm_num) _)
  obtain ⟨hcapGrowth0, hD₀0, hwaveProfile, hZ, hBpos⟩ :=
    (show (0 ≤ capGrowth) ∧ (0 ≤ D₀) ∧ (0 < waveTailProfileConst d) ∧ (0 < Z) ∧ (∀ n, 0 < B n) from
      @upperWaveTailTraceE12Consumption_comparisonBounds1 (d) (M) (E) (sigma) (hsigma0) (hd)
        (hfixed0))
  have hBsum : Summable B := by
    simpa only [B] using
      (summable_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one).mul_left B₀
  change max (max (profileAuxiliaryConst d)
      (collarBandMeanDepthThreshold d))
      (1 + 2 * (K * (rate / 2)⁻¹ + 8) * rate⁻¹) ≤ Cup at houtput
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans ((le_max_left _ _).trans houtput)
  obtain ⟨hK0, hCup1, hCup0, hchoice, hmaxAux, hexp, hgammaZ, hXgate, hlarge, hSroot,
    hsigmaProfile0, hsigmaProfileHalf, hsigmaProfileEighth, hEexp, hEb⟩ :=
    (show (0 ≤ K) ∧ (1 ≤ Cup) ∧ (0 < Cup) ∧ (K * (rate / 2)⁻¹ + 8 ≤ (rate / 2) * Cup) ∧ (max
      (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ)) ∧ (Real.exp (profileAuxiliaryConst d /
        sigma) ≤ (E : ℝ)) ∧ (M.gamma ≤ (E : ℝ) ^ (-5 : ℤ)) ∧ (Cup ≤ Xpar) ∧
          (collarBandMeanDepthThreshold d ≤ Xpar) ∧ (Algsuperdiff.Frozen.Section3.inductionState
      M (R.scale - 1) E) ∧ (0 < upperProfileSigma sigma) ∧ (upperProfileSigma sigma ≤ 1 / 2) ∧
        (upperProfileSigma sigma ≤ 1 / 8) ∧ (Real.exp
      (badClustersConst d / upperProfileSigma sigma) ≤ (E : ℝ)) ∧ (badClustersConst d /
        bfaProfileB ≤ (E : ℝ)) from
      @upperWaveTailTraceE12Consumption_comparisonBounds2 (d) (M) (m) (k) (R) (hR) (E) (hS)
        (sigma) (Cup) (hsigma0) (hsigma) (hmax) (hEgamma) (hd) (hrate) (hfixed0) (houtput) (haux))
  obtain ⟨hE4, hunit, hgamma20, hinvSq, hgammaGate⟩ :=
    badEventGates_of_profileAuxiliaryMaxGate M E.property hsigma0 hsigma
      hmaxAux hEgamma
  have hgammaProfile :
      M.gamma ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
    hgammaGate.trans
      (zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
        hsigma0 hexp)
  have hgammaHalf : M.gamma / 2 ≤ bfaProfileB * sigma := by
    have hbs : 0 ≤ bfaProfileB * sigma :=
      mul_nonneg bfaProfileB_pos.le hsigma0.le
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact hgammaProfile.trans (by nlinarith only [hbs])
  obtain ⟨hP, hP0, hAP0, hAP, hG0, hG, htailExponent⟩ :=
    @upperWaveTailTraceE12Consumption_momentBounds1 (d) (M) (m) (R) (E) (sigma) (hsigma0) (hsigma)
      (hd) (hSroot) (hsigmaProfile0) (hsigmaProfileHalf) (hsigmaProfileEighth) (hEexp) (hEb) (hE4)
        (hunit) (hgamma20) (hinvSq) (hgammaGate) (hgammaProfile) (hgammaHalf)
  have hdepthWave :
      (3 : ℝ) ^ (-((d : ℝ) / 4) * (k₀ : ℝ)) ≤ Z  := @upperWaveTailTraceE12Consumption_estimate2 (d) (M) (E) (hd)
  obtain ⟨htrace, hfinalScale, hliteral0, hliteralMeas, hbridge⟩ :=
    @upperWaveTailTraceE12Consumption_momentBounds3 (d) (M) (m) (k) (R) (hR) (E) (sigma) (Cup) (hsigma0) (hsigma) (hmax) (hd) (hrate) (hfixed0) (hcapGrowth0) (hD₀0) (hwaveProfile) (hZ) (hBpos) (hBsum) (hK0) (hCup1) (hCup0) (hchoice) (hgammaZ) (hXgate) (hlarge) (hSroot) (hsigmaProfile0) (hsigmaProfileHalf) (hEexp) (hEb) (hE4) (hunit) (hgamma20) (hinvSq) (hgammaGate) (hgammaHalf) (hP) (hP0) (hAP0) (hAP) (hG0) (hG) (htailExponent) (hdepthWave)
  refine ⟨by simpa only [k₀, shift] using hliteral0,
    by simpa only [k₀, shift] using hliteralMeas,
    by simpa only [k₀, shift] using hbridge, ?_⟩
  exact htrace.mono_scale (by simpa only [k₀, shift, Xpar] using hfinalScale)

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
