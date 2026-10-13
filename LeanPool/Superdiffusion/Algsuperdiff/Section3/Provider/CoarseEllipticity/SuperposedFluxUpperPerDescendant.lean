/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.Assembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandOrdinaryProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperBandMeanConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBaseProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperDeepBandTailConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperDeepBandTailOrdinaryLane
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperGoodBaseConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHeadSharpFrozenAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHeadSharpSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperSaturatedBlockProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailE12Consumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailTraceE12Consumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedPotentialProfile

/-!
# SuperposedFluxUpperPerDescendant

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (ae_ofReal_probeSharpFramedCollarDeepTailTraceLane_eq_sum_tsum)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (collar_head_tuned_trace_is_big_o_with_eighth_power)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (exists_tunedDeepBandTail_good_finite_trace_split)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (isBigOWith_upperProfileTarget_collarWaveTailFiniteTrace)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedTraceLane_frozenReserve)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseTraceLane_tuned)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (measurable_probeSharpFramedCollarBandMeanTunedTraceLane)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (measurable_probeSharpFramedCollarBaseTraceLane)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (measurable_probeSharpFramedCollarDeepTailTraceLane)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarBandMeanTunedTraceENNRealLane)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarBandMeanTunedTraceENNRealLane_eq)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarBandMeanTunedTraceLane_nonneg)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarBaseCoordinateENNRealLane)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarBaseCoordinateENNRealLane_eq)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarBaseCoordinateLane_nonneg)
open Algsuperdiff.Section3.Provider.CoarseEllipticity
  (probeSharpFramedCollarDeepTailTraceLane_nonneg)

/-!
# Per-descendant upper split for the superposed flux

This module constructs the twelve analytic lanes controlling the coarse upper block on a
single descendant cube. It packages them into a deterministic contribution, an ordinary
`Gamma_1` contribution, and an exceptional contribution.

The public result `superposedFlux_upper_per_descendant_split` deliberately stops before
the depth and exponent aggregation. Its exceptional scale remains in the raw form produced
by the twelve-lane construction.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory



private abbrev superposedFluxUpperPerDescendant_momentBounds1_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E })
      (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (sigma Clane : ℝ) (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Clane / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : profileAuxiliaryConst d ≤ Clane)
      (_ : collarBandMeanDepthThreshold d ≤ Clane) (k : ℕ) (R : TriadicCube d)
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) (_ : (2 : ℕ) ≤ d)
      (headRare bandRare deepRare afterRare : Cutoff.CutoffSample d → ℝ),
      let laneX : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let laneEps : ℝ := Real.exp (-(Clane⁻¹ * laneX));
      let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ)));
      let rarePerLaneScale : ℝ := depthFactor * laneEps ^ (8 : ℕ);
      let collarBase : Cutoff.CutoffSample d → ℝ :=
        probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ));
      let collarHead : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
        ∑ j : Fin d,
          ∑' (n : ℕ),
            Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
              (collarBandMeanDepth M (↑E : ℝ)) n
              (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
              (fun (eta : Cutoff.CutoffSample d) =>
                Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                    (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                      eta ^
                  (2 : ℕ))
              (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
      let collarBand : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarBandMeanTunedTraceLane M
        m R (↑E : ℝ);
      let collarDeep : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarDeepTailTraceLane M m R
        (↑E : ℝ);
      let collarAfter : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarAfterBandTraceLane M m
        R (↑E : ℝ);
      let collarWave : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
        ∑ j : Fin d,
          ∑' (n : ℕ),
            Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
              (collarBandMeanDepth M (↑E : ℝ)) n
              (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
              (fun (eta : Cutoff.CutoffSample d) =>
                Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                    (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                      eta ^
                  (2 : ℕ))
              (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
      ∀ (waveBounded waveRare : Cutoff.CutoffSample d → ℝ) (_ : (0 : ℝ) < rarePerLaneScale),
        let rareLane : Fin (12 : ℕ) → Cutoff.CutoffSample d → ℝ :=
          ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare, collarBase,
            collarHead, collarBand, collarDeep,
            collarAfter, collarWave];
        let Uexp : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) => ∑ i : Fin
          (12 : ℕ), rareLane i omega;
        ∀
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) Uexp
              (IndependentSums.gammaTriangleConst (((1 : ℝ) - sigma) / (3 : ℝ)) * ∑ _i : Fin (12 :
                ℕ), rarePerLaneScale)),
          let K : ℝ := (12 : ℝ) * upperAfterBandRareTriangleConst;
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) Uexp (K *
                rarePerLaneScale) ∧
            ∑ j : Fin d, ∑' (n : ℕ), ENNReal.ofReal (Multiscale.probeSharpFramedGoodBaseTerm d n
              (basisVec j)) =
                ENNReal.ofReal (Multiscale.probeSharpGoodBaseConst d) ∧
              (∀ (omega : Cutoff.CutoffSample d),
                  ∑ j : Fin d,
                      ∑' (n : ℕ),
                        ENNReal.ofReal
                          (Multiscale.probeSharpFramedCollarBaseTerm M R.scale (↑E : ℝ) bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n (basisVec j)
                              (Affine.superposedGradConst d)
                            (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) =
                    ENNReal.ofReal (collarBase omega)) ∧
                (∀ (omega : Cutoff.CutoffSample d),
                    probeSharpFramedCollarBandMeanTunedTraceENNRealLane M m R (↑E : ℝ) omega =
                      ENNReal.ofReal (collarBand omega)) ∧
                  ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                    (Cutoff.CutoffSample d)),
                    ENNReal.ofReal (collarDeep omega) =
                      ∑ j : Fin d, ∑' (n : ℕ), ENNReal.ofReal (probeSharpFramedCollarDeepTailLayer
                        M m R (↑E : ℝ) j n omega)

private abbrev superposedFluxUpperPerDescendant_momentBounds2_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }) (sigma Clane : ℝ)
      (_ : (0 : ℝ) < sigma) (_ : sigma ≤ (1 / 2 : ℝ)) (k : ℕ) (R : TriadicCube d)
      (headRare : Cutoff.CutoffSample d → ℝ) (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤
        headRare omega)
      (_ : Measurable headRare) (bandRare : Cutoff.CutoffSample d → ℝ)
      (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ bandRare omega)
      (_ : Measurable bandRare) (deepRare : Cutoff.CutoffSample d → ℝ)
      (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ deepRare omega)
      (_ : Measurable deepRare) (afterRare : Cutoff.CutoffSample d → ℝ)
      (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ afterRare omega)
      (_ : Measurable afterRare),
      let laneX : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let laneEps : ℝ := Real.exp (-(Clane⁻¹ * laneX));
      let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ)));
      let rarePerLaneScale : ℝ := depthFactor * laneEps ^ (8 : ℕ);
      let collarBase : Cutoff.CutoffSample d → ℝ :=
        probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ));
      let collarHead : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
        ∑ j : Fin d,
          ∑' (n : ℕ),
            Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
              (collarBandMeanDepth M (↑E : ℝ)) n
              (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
              (fun (eta : Cutoff.CutoffSample d) =>
                Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                    (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                      eta ^
                  (2 : ℕ))
              (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
      let collarBand : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarBandMeanTunedTraceLane M
        m R (↑E : ℝ);
      let collarDeep : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarDeepTailTraceLane M m R
        (↑E : ℝ);
      let collarAfter : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarAfterBandTraceLane M m
        R (↑E : ℝ);
      ∀
        (_ :
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
            (probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)))
            ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
              Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)))
        (_ :
          ∀ (omega : Cutoff.CutoffSample d),
            (0 : ℝ) ≤
              (fun (omega : Cutoff.CutoffSample d) =>
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                          (Affine.superposedGradConst d)
                        (fun (eta : Cutoff.CutoffSample d) =>
                          Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                              (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M
                                (↑E : ℝ)) n) eta ^
                            (2 : ℕ))
                        (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
                omega)
        (_ :
          Measurable fun (omega : Cutoff.CutoffSample d) =>
            ∑ j : Fin d,
              ∑' (n : ℕ),
                Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                  (collarBandMeanDepth M (↑E : ℝ)) n
                  (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
                  (fun (eta : Cutoff.CutoffSample d) =>
                    Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                        (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E :
                          ℝ)) n) eta ^
                      (2 : ℕ))
                  (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
        (_ :
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
            (fun (omega : Cutoff.CutoffSample d) =>
              ∑ j : Fin d,
                ∑' (n : ℕ),
                  Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                    (collarBandMeanDepth M (↑E : ℝ))
                    n (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
                    (fun (eta : Cutoff.CutoffSample d) =>
                      Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                          (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E :
                            ℝ)) n) eta ^
                        (2 : ℕ))
                    (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
            ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
              Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)))
        (_ :
          have eps : ℝ := Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (upperProfileTargetSigma sigma))
            (probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E : ℝ))
            ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (8 : ℕ)))
        (_ :
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
            (probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ))
            ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
              Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)))
        (_ :
          ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ probeSharpFramedCollarAfterBandTraceLane M
            m R (↑E : ℝ) omega)
        (_ : Measurable (probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ)))
        (_ :
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (upperProfileTargetSigma sigma))
            (probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ))
            ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
              Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))),
        let collarWave : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
          ∑ j : Fin d,
            ∑' (n : ℕ),
              Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                (collarBandMeanDepth M (↑E : ℝ)) n
                (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
                (fun (eta : Cutoff.CutoffSample d) =>
                  Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                      (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ))
                        n) eta ^
                    (2 : ℕ))
                (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
        ∀ (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarWave omega)
          (_ : Measurable collarWave)
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) collarWave
              ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
                Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)))
          (waveBounded waveRare : Cutoff.CutoffSample d → ℝ)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ waveBounded omega)
          (_ : Measurable waveBounded)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ waveRare omega)
          (_ : Measurable waveRare) (_ : (0 : ℝ) < rarePerLaneScale)
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) headRare rarePerLaneScale)
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) bandRare rarePerLaneScale)
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) deepRare rarePerLaneScale)
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) afterRare rarePerLaneScale)
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) waveBounded
                rarePerLaneScale)
          (_ :
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) waveRare rarePerLaneScale)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarBase omega)
          (_ : Measurable collarBase)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarBand omega)
          (_ : Measurable collarBand)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarDeep omega)
          (_ : Measurable collarDeep),
          let rareLane : Fin (12 : ℕ) → Cutoff.CutoffSample d → ℝ :=
            ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare, collarBase,
              collarHead, collarBand,
              collarDeep, collarAfter, collarWave];
          let Uexp : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
            ∑ i : Fin (12 : ℕ), rareLane i omega;
          (∀ (i : Fin (12 : ℕ)) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ rareLane i omega) ∧
            (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uexp omega) ∧
              Measurable Uexp ∧
                IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                  (Cutoff.CutoffSample d))
                  (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) Uexp
                  (IndependentSums.gammaTriangleConst (((1 : ℝ) - sigma) / (3 : ℝ)) * ∑ _i : Fin
                    (12 : ℕ), rarePerLaneScale)

private abbrev superposedFluxUpperPerDescendant_comparisonBounds4_statement : Prop :=
  ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E })
   (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (sigma Clane : ℝ) (_ : (0 : ℝ) < sigma)
   (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Clane / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
   (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : (0 : ℝ) < Clane)
   (_ : probeSharpWaveTailTunedOutputConst d ≤ Clane) (_ : profileAuxiliaryConst d ≤ Clane)
   (_ : collarBandMeanDepthThreshold d ≤ Clane) (k : ℕ) (R : TriadicCube d)
   (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) (_ : (2 : ℕ) ≤ d)
   (headOrdinary headRare : Cutoff.CutoffSample d → ℝ) (headOrdinaryScale headRareScale : ℝ)
   (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ headOrdinary omega)
   (_ : Measurable headOrdinary)
   (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ headRare omega)
   (_ : Measurable headRare)
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (1 : ℝ)) headOrdinary headOrdinaryScale)
   (_ : headOrdinaryScale ≤ upperSaturatedPerCubeAmplitude Clane (Disorder.cstar M) M.gamma k)
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) headRare headRareScale)
   (_ : headRareScale ≤ Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))
   (bandRare : Cutoff.CutoffSample d → ℝ) (bandRareScale : ℝ)
   (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ bandRare omega)
   (_ : Measurable bandRare)
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) bandRare bandRareScale)
   (_ : bandRareScale ≤ Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))
   (deepOrdinary deepRare : Cutoff.CutoffSample d → ℝ) (deepOrdinaryScale deepRareScale : ℝ)
   (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ deepOrdinary omega)
   (_ : Measurable deepOrdinary)
   (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ deepRare omega)
   (_ : Measurable deepRare)
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (1 : ℝ)) deepOrdinary deepOrdinaryScale)
   (_ : deepOrdinaryScale ≤ upperSaturatedPerCubeAmplitude Clane (Disorder.cstar M) M.gamma k)
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) deepRare deepRareScale)
   (_ : deepRareScale ≤ Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))
   (afterOrdinary afterRare : Cutoff.CutoffSample d → ℝ) (afterOrdinaryScale afterRareScale : ℝ)
   (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ afterOrdinary omega)
   (_ : Measurable afterOrdinary)
   (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ afterRare omega)
   (_ : Measurable afterRare)
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (1 : ℝ)) afterOrdinary afterOrdinaryScale)
   (_ : afterOrdinaryScale ≤ upperSaturatedPerCubeAmplitude Clane (Disorder.cstar M) M.gamma k)
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) afterRare afterRareScale)
   (_ :
    afterRareScale ≤
     (3 : ℝ) ^ (M.gamma * (↑(k + (1 : ℕ)) : ℝ)) * Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ)
      * M.gamma⁻¹))) ^ (8 : ℕ))
   (_ :
    have laneX : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
    have _ : ℝ := Real.exp (-(Clane⁻¹ * laneX));
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
     (probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)))
     ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
      Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)))
   (_ :
    ∀ (omega : Cutoff.CutoffSample d),
     (0 : ℝ) ≤
      (fun (omega : Cutoff.CutoffSample d) =>
        ∑ j : Fin d,
         ∑' (n : ℕ),
          Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
           (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
            (Affine.superposedGradConst d)
           (fun (eta : Cutoff.CutoffSample d) =>
            Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
              (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E
               : ℝ)) n) eta ^
             (2 : ℕ))
           (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
       omega)
   (_ :
    Measurable fun (omega : Cutoff.CutoffSample d) =>
     ∑ j : Fin d,
      ∑' (n : ℕ),
       Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
        (collarBandMeanDepth M (↑E : ℝ)) n
        (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
        (fun (eta : Cutoff.CutoffSample d) =>
         Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
           (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ))
            n) eta ^
          (2 : ℕ))
        (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
   (_ :
    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
     (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
     (fun (omega : Cutoff.CutoffSample d) =>
      ∑ j : Fin d,
       ∑' (n : ℕ),
        Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
         (collarBandMeanDepth M (↑E : ℝ)) n
         (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
         (fun (eta : Cutoff.CutoffSample d) =>
          Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E :
             ℝ)) n) eta ^
           (2 : ℕ))
         (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
     ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
      Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))),
   let _ : Cutoff.CutoffSample d → ℝ :=
    probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ));
   let _ : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
    ∑ j : Fin d,
     ∑' (n : ℕ),
      Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
       (collarBandMeanDepth M (↑E : ℝ)) n
       (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
       (fun (eta : Cutoff.CutoffSample d) =>
        Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
           eta ^
         (2 : ℕ))
       (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
   let _ : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E
    : ℝ);
   let _ : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ);
   let _ : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ);
   ∀
    (_ :
     have eps : ℝ := Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
     IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
      (IndependentSums.gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E : ℝ))
      ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * eps ^ (8 : ℕ)))
    (_ :
     IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
      (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
      (probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ))
      ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
       Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)))
    (_ :
     ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ probeSharpFramedCollarAfterBandTraceLane M
      m R (↑E : ℝ) omega)
    (_ : Measurable (probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ)))
    (_ :
     IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
      (IndependentSums.gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ))
      ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
       Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))),
    let collarWave : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
     ∑ j : Fin d,
      ∑' (n : ℕ),
       Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
        (collarBandMeanDepth M (↑E : ℝ)) n
        (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
        (fun (eta : Cutoff.CutoffSample d) =>
         Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
           (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ))
            n) eta ^
          (2 : ℕ))
        (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
    ∀
     (_ :
      (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarWave omega) ∧
       Measurable collarWave ∧
        (∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
         (Cutoff.CutoffSample d)),
          ENNReal.ofReal (collarWave omega) =
           ∑ j : Fin d,
            ∑' (n : ℕ),
             ENNReal.ofReal
              (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
               bfaProfileB
               (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                (Affine.superposedGradConst d)
               (fun (eta : Cutoff.CutoffSample d) =>
                Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                  (probeSharpLayerAnchor R.scale bfaProfileB
                   (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                 (2 : ℕ))
               (Cutoff.translateCutoffSample (triadicCubeShift R) omega))) ∧
         IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
          (Cutoff.CutoffSample d))
          (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) collarWave
          ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
           Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))),
     (∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
      (Cutoff.CutoffSample d)),
       ENNReal.ofReal (collarWave omega) =
        ∑ j : Fin d,
         ∑' (n : ℕ),
          ENNReal.ofReal
           (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
            (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
             (Affine.superposedGradConst d)
            (fun (eta : Cutoff.CutoffSample d) =>
             Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
               (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M
                (↑E : ℝ)) n) eta ^
              (2 : ℕ))
            (Cutoff.translateCutoffSample (triadicCubeShift R) omega))) ∧
      ∃ (waveBounded : Cutoff.CutoffSample d → ℝ) (waveRare : Cutoff.CutoffSample d → ℝ),
       (∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
        (Cutoff.CutoffSample d)),
         ∑ j : Fin d,
           ∑' (n : ℕ),
            ENNReal.ofReal
             (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
              (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
              (fun (eta : Cutoff.CutoffSample d) =>
               Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                 (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth
                  M (↑E : ℝ)) n) eta ^
                (2 : ℕ))
              (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) ≤
          ENNReal.ofReal (waveBounded omega) + ENNReal.ofReal (waveRare omega)) ∧
        (∀ (i : Fin (3 : ℕ)) (omega : Cutoff.CutoffSample d),
          (0 : ℝ) ≤ ![headOrdinary, deepOrdinary, afterOrdinary] i omega) ∧
         (∀ (omega : Cutoff.CutoffSample d),
           (0 : ℝ) ≤
            (fun (omega : Cutoff.CutoffSample d) =>
              ∑ i : Fin (3 : ℕ), ![headOrdinary, deepOrdinary, afterOrdinary] i omega)
             omega) ∧
          (Measurable fun (omega : Cutoff.CutoffSample d) =>
            ∑ i : Fin (3 : ℕ), ![headOrdinary, deepOrdinary, afterOrdinary] i omega) ∧
           IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
            (Cutoff.CutoffSample d))
             (IndependentSums.gammaSigma (1 : ℝ))
             (fun (omega : Cutoff.CutoffSample d) =>
              ∑ i : Fin (3 : ℕ), ![headOrdinary, deepOrdinary, afterOrdinary] i omega)
             (upperSaturatedPerCubeAmplitude
              (((12 : ℝ) + (12 : ℝ) * IndependentSums.gammaTriangleConst (1 : ℝ)) *
               Clane) (Disorder.cstar M)
              M.gamma k) ∧
            (∀ (i : Fin (12 : ℕ)) (omega : Cutoff.CutoffSample d),
              (0 : ℝ) ≤
               ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare,
                 probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ)
                  (collarBandMeanDepth M (↑E : ℝ)),
                 fun (omega : Cutoff.CutoffSample d) =>
                 ∑ j : Fin d,
                  ∑' (n : ℕ),
                   Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                    bfaProfileB
                    (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec
                     j)
                    (Affine.superposedGradConst d)
                    (fun (eta : Cutoff.CutoffSample d) =>
                     Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                       (probeSharpLayerAnchor R.scale bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n)
                       eta ^
                      (2 : ℕ))
                    (Cutoff.translateCutoffSample (triadicCubeShift R) omega),
                 probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E : ℝ),
                 probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ),
                 probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ),
                 fun (omega : Cutoff.CutoffSample d) =>
                 ∑ j : Fin d,
                  ∑' (n : ℕ),
                   Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                    bfaProfileB
                    (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec
                     j)
                    (Affine.superposedGradConst d)
                    (fun (eta : Cutoff.CutoffSample d) =>
                     Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB
                      R.scale
                       (probeSharpLayerAnchor R.scale bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n)
                       eta ^
                      (2 : ℕ))
                    (Cutoff.translateCutoffSample (triadicCubeShift R) omega)]
                i omega) ∧
             (∀ (omega : Cutoff.CutoffSample d),
               (0 : ℝ) ≤
                (fun (omega : Cutoff.CutoffSample d) =>
                  ∑ i : Fin (12 : ℕ),
                   ![headRare, bandRare, deepRare, afterRare, waveBounded,
                    waveRare,
                     probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ)
                      (collarBandMeanDepth M (↑E : ℝ)),
                     fun (omega : Cutoff.CutoffSample d) =>
                     ∑ j : Fin d,
                      ∑' (n : ℕ),
                       Multiscale.probeSharpFramedCollarWavePart M R.scale
                        (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
                         (basisVec j)
                        (Affine.superposedGradConst d)
                        (fun (eta : Cutoff.CutoffSample d) =>
                         Multiscale.waveHeadTerm M R.scale (↑E : ℝ)
                          bfaProfileB
                           (probeSharpLayerAnchor R.scale bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n)
                           eta ^
                          (2 : ℕ))
                        (Cutoff.translateCutoffSample (triadicCubeShift R)
                         omega),
                     probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E :
                      ℝ),
                     probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ),
                     probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ),
                     fun (omega : Cutoff.CutoffSample d) =>
                     ∑ j : Fin d,
                      ∑' (n : ℕ),
                       Multiscale.probeSharpFramedCollarWavePart M R.scale
                        (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
                         (basisVec j)
                        (Affine.superposedGradConst d)
                        (fun (eta : Cutoff.CutoffSample d) =>
                         Multiscale.waveTailTerm M R.scale (↑E : ℝ)
                          bfaProfileB R.scale
                           (probeSharpLayerAnchor R.scale bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n)
                           eta ^
                          (2 : ℕ))
                        (Cutoff.translateCutoffSample (triadicCubeShift R)
                         omega)]
                    i omega)
                 omega) ∧
              (Measurable fun (omega : Cutoff.CutoffSample d) =>
                ∑ i : Fin (12 : ℕ),
                 ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare,
                   probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ)
                    (collarBandMeanDepth M (↑E : ℝ)),
                   fun (omega : Cutoff.CutoffSample d) =>
                   ∑ j : Fin d,
                    ∑' (n : ℕ),
                     Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E
                      : ℝ) bfaProfileB
                      (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
                       (basisVec j)
                      (Affine.superposedGradConst d)
                      (fun (eta : Cutoff.CutoffSample d) =>
                       Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                         (probeSharpLayerAnchor R.scale bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n)
                         eta ^
                        (2 : ℕ))
                      (Cutoff.translateCutoffSample (triadicCubeShift R)
                       omega),
                   probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E : ℝ),
                   probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ),
                   probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ),
                   fun (omega : Cutoff.CutoffSample d) =>
                   ∑ j : Fin d,
                    ∑' (n : ℕ),
                     Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E
                      : ℝ) bfaProfileB
                      (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
                       (basisVec j)
                      (Affine.superposedGradConst d)
                      (fun (eta : Cutoff.CutoffSample d) =>
                       Multiscale.waveTailTerm M R.scale (↑E : ℝ)
                        bfaProfileB R.scale
                         (probeSharpLayerAnchor R.scale bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n)
                         eta ^
                        (2 : ℕ))
                      (Cutoff.translateCutoffSample (triadicCubeShift R)
                       omega)]
                  i omega) ∧
               IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                (Cutoff.CutoffSample d))
                 (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
                 (fun (omega : Cutoff.CutoffSample d) =>
                  ∑ i : Fin (12 : ℕ),
                   ![headRare, bandRare, deepRare, afterRare, waveBounded,
                    waveRare,
                     probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ)
                      (collarBandMeanDepth M (↑E : ℝ)),
                     fun (omega : Cutoff.CutoffSample d) =>
                     ∑ j : Fin d,
                      ∑' (n : ℕ),
                       Multiscale.probeSharpFramedCollarWavePart M R.scale
                        (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
                         (basisVec j)
                        (Affine.superposedGradConst d)
                        (fun (eta : Cutoff.CutoffSample d) =>
                         Multiscale.waveHeadTerm M R.scale (↑E : ℝ)
                          bfaProfileB
                           (probeSharpLayerAnchor R.scale bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n)
                           eta ^
                          (2 : ℕ))
                        (Cutoff.translateCutoffSample (triadicCubeShift R)
                         omega),
                     probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E :
                      ℝ),
                     probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ),
                     probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ),
                     fun (omega : Cutoff.CutoffSample d) =>
                     ∑ j : Fin d,
                      ∑' (n : ℕ),
                       Multiscale.probeSharpFramedCollarWavePart M R.scale
                        (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
                         (basisVec j)
                        (Affine.superposedGradConst d)
                        (fun (eta : Cutoff.CutoffSample d) =>
                         Multiscale.waveTailTerm M R.scale (↑E : ℝ)
                          bfaProfileB R.scale
                           (probeSharpLayerAnchor R.scale bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n)
                           eta ^
                          (2 : ℕ))
                        (Cutoff.translateCutoffSample (triadicCubeShift R)
                         omega)]
                    i omega)
                 ((12 : ℝ) * upperAfterBandRareTriangleConst *
                  ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
                   Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^
                    (8 : ℕ))) ∧
                ∑ j : Fin d,
                   ∑' (n : ℕ),
                    ENNReal.ofReal (Multiscale.probeSharpFramedGoodBaseTerm d
                     n (basisVec j)) =
                  ENNReal.ofReal (Multiscale.probeSharpGoodBaseConst d) ∧
                 (∀ (omega : Cutoff.CutoffSample d),
                   ∑ j : Fin d,
                     ∑' (n : ℕ),
                      ENNReal.ofReal
                       (Multiscale.probeSharpFramedCollarBaseTerm M R.scale
                        (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n (basisVec j)
                        (Affine.superposedGradConst d)
                        (Cutoff.translateCutoffSample (triadicCubeShift R)
                         omega)) =
                    ENNReal.ofReal
                     (probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ)
                      (collarBandMeanDepth M (↑E : ℝ))
                      omega)) ∧
                  (∀ (omega : Cutoff.CutoffSample d),
                    probeSharpFramedCollarBandMeanTunedTraceENNRealLane M m R
                     (↑E : ℝ) omega =
                     ENNReal.ofReal
                      (probeSharpFramedCollarBandMeanTunedTraceLane M m R
                       (↑E : ℝ) omega)) ∧
                   (∀ᵐ (omega :
                     Cutoff.CutoffSample
                      d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                       (Cutoff.CutoffSample d)),
                     ENNReal.ofReal (probeSharpFramedCollarDeepTailTraceLane
                      M m R (↑E : ℝ) omega) =
                      ∑ j : Fin d,
                       ∑' (n : ℕ),
                        ENNReal.ofReal
                         (probeSharpFramedCollarDeepTailLayer M m R (↑E :
                          ℝ) j n omega)) ∧
                    (∀ (omega : Cutoff.CutoffSample d),
                      ∑ i : Fin d,
                        ∑' (a : ℕ),
                         ENNReal.ofReal
                          (Multiscale.probeSharpFramedMeanLayerEnvelope
                           M R.scale (↑E : ℝ)
                           bfaProfileB (collarBandMeanDepth M (↑E : ℝ))
                            a (m - (1 : ℤ)) m
                           (Cutoff.translateCutoffSample
                            (triadicCubeShift R) omega) (basisVec i)
                           (Affine.superposedGradConst d)) ≤
                       ∑ i : Fin d,
                        ∑' (a : ℕ),
                         (ENNReal.ofReal
                                     (Multiscale.probeSharpFramedGoodBaseTerm d a
                                      (basisVec i)) +
                                    ENNReal.ofReal
                                     (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                      (↑E : ℝ) bfaProfileB
                                      (collarBandMeanDepth M
                                       (↑E : ℝ)) a (m - (1
                                        : ℤ))
                                      (basisVec i)
                                      (fun (eta :
                                       Cutoff.CutoffSample
                                        d) =>
                                       Multiscale.waveHeadTerm M R.scale (↑E : ℝ)
                                         bfaProfileB
                                         (probeSharpLayerAnchor R.scale bfaProfileB
                                          (collarBandMeanDepth M (↑E : ℝ)) a)
                                         eta ^
                                        (2 : ℕ))
                                      (Cutoff.translateCutoffSample
                                       (triadicCubeShift R)
                                        omega)) +
                                   ENNReal.ofReal
                                    (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                     (↑E : ℝ) bfaProfileB
                                     (collarBandMeanDepth M
                                      (↑E : ℝ)) a (m - (1 :
                                       ℤ))
                                     (basisVec i)
                                     (fun (_eta :
                                      Cutoff.CutoffSample d)
                                       =>
                                      waveBandMean
                                       (probeDeepBandMeanAmplitude d)
                                        M.gamma
                                         (collarBandMeanDepth M (↑E : ℝ)) ^
                                       (2 : ℕ))
                                     (Cutoff.translateCutoffSample (triadicCubeShift R)
                                      omega)) +
                                  ENNReal.ofReal
                                   (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                    (↑E : ℝ) bfaProfileB
                                    (collarBandMeanDepth M (↑E
                                     : ℝ)) a (m - (1 : ℤ))
                                    (basisVec i)
                                    (fun (eta :
                                     Cutoff.CutoffSample d) =>
                                     probeDeepBandGaugedTail
                                      M (originCube d R.scale)
                                       (probeSharpLayerAnchor R.scale bfaProfileB
                                        (collarBandMeanDepth M (↑E : ℝ)) a)
                                       (collarBandMeanDepth
                                        M (↑E : ℝ))
                                       (collarBandMeanDepth
                                        M (↑E : ℝ)) eta ^
                                      (2 : ℕ))
                                    (Cutoff.translateCutoffSample (triadicCubeShift R)
                                     omega)) +
                                 ENNReal.ofReal
                                  (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                   (↑E : ℝ) bfaProfileB
                                    (collarBandMeanDepth M (↑E
                                     : ℝ))
                                   a (m - (1 : ℤ)) (basisVec i)
                                   (fun (eta :
                                    Cutoff.CutoffSample d) =>
                                    probeSharpAfterBandTerm M
                                     R.scale
                                      (probeSharpLayerAnchor
                                       R.scale bfaProfileB
                                       (collarBandMeanDepth
                                        M (↑E : ℝ)) a)
                                      (collarBandMeanDepth M
                                       (↑E : ℝ)) m eta ^
                                     (2 : ℕ))
                                   (Cutoff.translateCutoffSample (triadicCubeShift R)
                                    omega)) +
                                ENNReal.ofReal
                                 (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                  (↑E : ℝ) bfaProfileB
                                   (collarBandMeanDepth M (↑E :
                                    ℝ)) a
                                  (m - (1 : ℤ)) (basisVec i)
                                  (fun (eta :
                                   Cutoff.CutoffSample d) =>
                                   Multiscale.waveTailTerm M
                                    R.scale (↑E : ℝ) bfaProfileB
                                     R.scale
                                     (probeSharpLayerAnchor
                                      R.scale bfaProfileB
                                      (collarBandMeanDepth M
                                       (↑E : ℝ)) a)
                                     eta ^
                                    (2 : ℕ))
                                  (Cutoff.translateCutoffSample
                                   (triadicCubeShift R)
                                   omega)) +
                               ENNReal.ofReal
                                (Multiscale.probeSharpFramedCollarBaseTerm M R.scale
                                 (↑E : ℝ) bfaProfileB
                                  (collarBandMeanDepth M (↑E :
                                   ℝ)) a
                                 (basisVec i)
                                  (Affine.superposedGradConst d)
                                 (Cutoff.translateCutoffSample
                                  (triadicCubeShift R)
                                  omega)) +
                              ENNReal.ofReal
                               (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                                bfaProfileB (collarBandMeanDepth M
                                 (↑E : ℝ)) a (m - (1 : ℤ))
                                (basisVec i)
                                 (Affine.superposedGradConst d)
                                (fun (eta : Cutoff.CutoffSample d)
                                 =>
                                 Multiscale.waveHeadTerm M
                                  R.scale (↑E : ℝ) bfaProfileB
                                   (probeSharpLayerAnchor
                                    R.scale bfaProfileB
                                    (collarBandMeanDepth M (↑E
                                     : ℝ)) a)
                                   eta ^
                                  (2 : ℕ))
                                (Cutoff.translateCutoffSample
                                 (triadicCubeShift R) omega)) +
                             ENNReal.ofReal
                              (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                               bfaProfileB (collarBandMeanDepth M
                                (↑E : ℝ)) a (m - (1 : ℤ))
                               (basisVec i)
                                (Affine.superposedGradConst d)
                               (fun (_eta : Cutoff.CutoffSample d) =>
                                waveBandMean
                                 (probeDeepBandMeanAmplitude d)
                                  M.gamma
                                  (collarBandMeanDepth M (↑E :
                                   ℝ)) ^
                                 (2 : ℕ))
                               (Cutoff.translateCutoffSample
                                (triadicCubeShift R) omega)) +
                            ENNReal.ofReal
                             (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                              bfaProfileB (collarBandMeanDepth M (↑E
                               : ℝ)) a (m - (1 : ℤ))
                              (basisVec i)
                               (Affine.superposedGradConst d)
                              (fun (eta : Cutoff.CutoffSample d) =>
                               probeDeepBandGaugedTail M
                                (originCube d R.scale)
                                 (probeSharpLayerAnchor R.scale
                                  bfaProfileB
                                  (collarBandMeanDepth M (↑E :
                                   ℝ)) a)
                                 (collarBandMeanDepth M (↑E : ℝ))
                                 (collarBandMeanDepth M (↑E : ℝ))
                                  eta ^
                                (2 : ℕ))
                              (Cutoff.translateCutoffSample
                               (triadicCubeShift R) omega)) +
                           ENNReal.ofReal
                            (Multiscale.probeSharpFramedCollarWavePart
                             M R.scale (↑E : ℝ)
                             bfaProfileB (collarBandMeanDepth M (↑E :
                              ℝ)) a (m - (1 : ℤ))
                             (basisVec i) (Affine.superposedGradConst
                              d)
                             (fun (eta : Cutoff.CutoffSample d) =>
                              probeSharpAfterBandTerm M R.scale
                                (probeSharpLayerAnchor R.scale
                                 bfaProfileB
                                 (collarBandMeanDepth M (↑E : ℝ))
                                  a)
                                (collarBandMeanDepth M (↑E : ℝ)) m
                                 eta ^
                               (2 : ℕ))
                             (Cutoff.translateCutoffSample
                              (triadicCubeShift R) omega)) +
                          ENNReal.ofReal
                           (Multiscale.probeSharpFramedCollarWavePart M
                            R.scale (↑E : ℝ)
                            bfaProfileB (collarBandMeanDepth M (↑E :
                             ℝ)) a (m - (1 : ℤ))
                            (basisVec i) (Affine.superposedGradConst d)
                            (fun (eta : Cutoff.CutoffSample d) =>
                             Multiscale.waveTailTerm M R.scale (↑E :
                              ℝ) bfaProfileB R.scale
                               (probeSharpLayerAnchor R.scale
                                bfaProfileB
                                (collarBandMeanDepth M (↑E : ℝ)) a)
                               eta ^
                              (2 : ℕ))
                            (Cutoff.translateCutoffSample
                             (triadicCubeShift R) omega)))) ∧
                     True

private abbrev superposedFluxUpperPerDescendant_comparisonBounds5_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }) (Clane : ℝ),
      let Cblock : ℝ := ((12 : ℝ) + (12 : ℝ) * IndependentSums.gammaTriangleConst (1 : ℝ)) * Clane;
      ∀ (k : ℕ) (R : TriadicCube d) (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) -
        (↑k : ℤ)))
        (_ : (2 : ℕ) ≤ d)
        (_ :
          ∀ (k : ℕ),
            ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
              ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                (Cutoff.CutoffSample d)),
                ENNReal.ofReal (cutoffBBlockFamily M m (↑(Annealed.sigmaBar M (m - (1 : ℤ))) :
                  ℝ)⁻¹ R omega) ≤
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      ENNReal.ofReal
                        (Multiscale.probeSharpFramedMeanLayerEnvelope M R.scale (↑E : ℝ) bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) m
                          (Cutoff.translateCutoffSample (triadicCubeShift R) omega) (basisVec j)
                          (Affine.superposedGradConst d)))
        (headOrdinary headRare : Cutoff.CutoffSample d → ℝ)
        (_ :
          ∀ (omega : Cutoff.CutoffSample d),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
                      (collarBandMeanDepth M (↑E : ℝ))
                      n (m - (1 : ℤ)) (basisVec j)
                      (fun (eta : Cutoff.CutoffSample d) =>
                        Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                            (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E
                              : ℝ)) n) eta ^
                          (2 : ℕ))
                      (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) ≤
              ENNReal.ofReal (headOrdinary omega) + ENNReal.ofReal (headRare omega))
        (bandOrdinary bandRare : Cutoff.CutoffSample d → ℝ)
        (_ :
          ∀ (omega : Cutoff.CutoffSample d),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
                      (collarBandMeanDepth M (↑E : ℝ))
                      n (m - (1 : ℤ)) (basisVec j)
                      (fun (_eta : Cutoff.CutoffSample d) =>
                        waveBandMean (probeDeepBandMeanAmplitude d) M.gamma (collarBandMeanDepth M
                          (↑E : ℝ)) ^ (2 : ℕ))
                      (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) ≤
              ENNReal.ofReal (bandOrdinary omega) + ENNReal.ofReal (bandRare omega))
        (deepOrdinary deepRare : Cutoff.CutoffSample d → ℝ)
        (_ :
          ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
            (Cutoff.CutoffSample d)),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
                      (collarBandMeanDepth M (↑E : ℝ))
                      n (m - (1 : ℤ)) (basisVec j)
                      (fun (eta : Cutoff.CutoffSample d) =>
                        probeDeepBandGaugedTail M (originCube d R.scale)
                            (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E
                              : ℝ)) n)
                            (collarBandMeanDepth M (↑E : ℝ)) (collarBandMeanDepth M (↑E : ℝ)) eta ^
                          (2 : ℕ))
                      (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) ≤
              ENNReal.ofReal (deepOrdinary omega) + ENNReal.ofReal (deepRare omega))
        (afterOrdinary afterRare : Cutoff.CutoffSample d → ℝ)
        (_ :
          ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
            (Cutoff.CutoffSample d)),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
                      (collarBandMeanDepth M (↑E : ℝ))
                      n (m - (1 : ℤ)) (basisVec j)
                      (fun (eta : Cutoff.CutoffSample d) =>
                        probeSharpAfterBandTerm M R.scale
                            (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E
                              : ℝ)) n)
                            (collarBandMeanDepth M (↑E : ℝ)) m eta ^
                          (2 : ℕ))
                      (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) ≤
              ENNReal.ofReal (afterOrdinary omega) + ENNReal.ofReal (afterRare omega))
        (_ :
          ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
            (Cutoff.CutoffSample d)),
            ENNReal.ofReal
                ((fun (omega : Cutoff.CutoffSample d) =>
                    ∑ j : Fin d,
                      ∑' (n : ℕ),
                        Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                            (Affine.superposedGradConst d)
                          (fun (eta : Cutoff.CutoffSample d) =>
                            Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M
                                  (↑E : ℝ)) n) eta ^
                              (2 : ℕ))
                          (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
                  omega) =
              ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                      (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                        (Affine.superposedGradConst d)
                      (fun (eta : Cutoff.CutoffSample d) =>
                        Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                            (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E
                              : ℝ)) n) eta ^
                          (2 : ℕ))
                      (Cutoff.translateCutoffSample (triadicCubeShift R) omega))),
        let collarBase : Cutoff.CutoffSample d → ℝ :=
          probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ));
        let collarHead : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
          ∑ j : Fin d,
            ∑' (n : ℕ),
              Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                (collarBandMeanDepth M (↑E : ℝ)) n
                (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
                (fun (eta : Cutoff.CutoffSample d) =>
                  Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                      (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ))
                        n) eta ^
                    (2 : ℕ))
                (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
        let collarBand : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarBandMeanTunedTraceLane
          M m R (↑E : ℝ);
        let collarDeep : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarDeepTailTraceLane M m
          R (↑E : ℝ);
        let collarAfter : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarAfterBandTraceLane M
          m R (↑E : ℝ);
        ∀
          (_ :
            ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
              (Cutoff.CutoffSample d)),
              ENNReal.ofReal (probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ) omega) =
                ∑ j : Fin d,
                  ∑' (n : ℕ),
                    ENNReal.ofReal
                      (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                          (Affine.superposedGradConst d)
                        (fun (eta : Cutoff.CutoffSample d) =>
                          probeSharpAfterBandTerm M R.scale
                              (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M
                                (↑E : ℝ)) n)
                              (collarBandMeanDepth M (↑E : ℝ)) m eta ^
                            (2 : ℕ))
                        (Cutoff.translateCutoffSample (triadicCubeShift R) omega))),
          let collarWave : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
            ∑ j : Fin d,
              ∑' (n : ℕ),
                Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                  (collarBandMeanDepth M (↑E : ℝ)) n
                  (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
                  (fun (eta : Cutoff.CutoffSample d) =>
                    Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                        (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E :
                          ℝ)) n) eta ^
                      (2 : ℕ))
                  (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
          ∀
            (_ :
              ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                (Cutoff.CutoffSample d)),
                ENNReal.ofReal
                    ((fun (omega : Cutoff.CutoffSample d) =>
                        ∑ j : Fin d,
                          ∑' (n : ℕ),
                            Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                              (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                                (Affine.superposedGradConst d)
                              (fun (eta : Cutoff.CutoffSample d) =>
                                Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                    (probeSharpLayerAnchor R.scale bfaProfileB
                                      (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                                  (2 : ℕ))
                              (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
                      omega) =
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      ENNReal.ofReal
                        (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                            (Affine.superposedGradConst d)
                          (fun (eta : Cutoff.CutoffSample d) =>
                            Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M
                                  (↑E : ℝ)) n) eta ^
                              (2 : ℕ))
                          (Cutoff.translateCutoffSample (triadicCubeShift R) omega)))
            (waveBounded waveRare : Cutoff.CutoffSample d → ℝ)
            (_ :
              ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                (Cutoff.CutoffSample d)),
                ∑ j : Fin d,
                    ∑' (n : ℕ),
                      ENNReal.ofReal
                        (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                          (fun (eta : Cutoff.CutoffSample d) =>
                            Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M
                                  (↑E : ℝ)) n) eta ^
                              (2 : ℕ))
                          (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) ≤
                  ENNReal.ofReal (waveBounded omega) + ENNReal.ofReal (waveRare omega))
            (_ :
              ∀ (i : Fin (3 : ℕ)) (omega : Cutoff.CutoffSample d),
                (0 : ℝ) ≤ ![headOrdinary, deepOrdinary, afterOrdinary] i omega)
            (_ :
              ∀ (omega : Cutoff.CutoffSample d),
                (0 : ℝ) ≤
                  (fun (omega : Cutoff.CutoffSample d) =>
                      ∑ i : Fin (3 : ℕ), ![headOrdinary, deepOrdinary, afterOrdinary] i omega)
                    omega)
            (_ :
              ∀ (i : Fin (12 : ℕ)) (omega : Cutoff.CutoffSample d),
                (0 : ℝ) ≤
                  ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare,
                      probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E
                        : ℝ)),
                      fun (omega : Cutoff.CutoffSample d) =>
                      ∑ j : Fin d,
                        ∑' (n : ℕ),
                          Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                              (Affine.superposedGradConst d)
                            (fun (eta : Cutoff.CutoffSample d) =>
                              Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                                  (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth
                                    M (↑E : ℝ)) n) eta ^
                                (2 : ℕ))
                            (Cutoff.translateCutoffSample (triadicCubeShift R) omega),
                      probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E : ℝ),
                      probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ),
                      probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ), fun (omega :
                        Cutoff.CutoffSample d) =>
                      ∑ j : Fin d,
                        ∑' (n : ℕ),
                          Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                              (Affine.superposedGradConst d)
                            (fun (eta : Cutoff.CutoffSample d) =>
                              Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                  (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth
                                    M (↑E : ℝ)) n) eta ^
                                (2 : ℕ))
                            (Cutoff.translateCutoffSample (triadicCubeShift R) omega)]
                    i omega)
            (_ :
              ∀ (omega : Cutoff.CutoffSample d),
                (0 : ℝ) ≤
                  (fun (omega : Cutoff.CutoffSample d) =>
                      ∑ i : Fin (12 : ℕ),
                        ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare,
                            probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth
                              M (↑E : ℝ)),
                            fun (omega : Cutoff.CutoffSample d) =>
                            ∑ j : Fin d,
                              ∑' (n : ℕ),
                                Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                                  bfaProfileB
                                  (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                                  (Affine.superposedGradConst d)
                                  (fun (eta : Cutoff.CutoffSample d) =>
                                    Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                                        (probeSharpLayerAnchor R.scale bfaProfileB
                                          (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                                      (2 : ℕ))
                                  (Cutoff.translateCutoffSample (triadicCubeShift R) omega),
                            probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E : ℝ),
                            probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ),
                            probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ), fun (omega :
                              Cutoff.CutoffSample d) =>
                            ∑ j : Fin d,
                              ∑' (n : ℕ),
                                Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                                  bfaProfileB
                                  (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                                  (Affine.superposedGradConst d)
                                  (fun (eta : Cutoff.CutoffSample d) =>
                                    Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                        (probeSharpLayerAnchor R.scale bfaProfileB
                                          (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                                      (2 : ℕ))
                                  (Cutoff.translateCutoffSample (triadicCubeShift R) omega)]
                          i omega)
                    omega)
            (_ :
              ∑ j : Fin d, ∑' (n : ℕ), ENNReal.ofReal (Multiscale.probeSharpFramedGoodBaseTerm d n
                (basisVec j)) =
                ENNReal.ofReal (Multiscale.probeSharpGoodBaseConst d))
            (_ :
              ∀ (omega : Cutoff.CutoffSample d),
                ∑ j : Fin d,
                    ∑' (n : ℕ),
                      ENNReal.ofReal
                        (Multiscale.probeSharpFramedCollarBaseTerm M R.scale (↑E : ℝ) bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n (basisVec j)
                            (Affine.superposedGradConst d)
                          (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) =
                  ENNReal.ofReal (probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ)
                    (collarBandMeanDepth M (↑E : ℝ)) omega)),
            let ordinaryLane : Fin (3 : ℕ) → Cutoff.CutoffSample d → ℝ := ![headOrdinary,
              deepOrdinary, afterOrdinary];
            let Uone : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
              ∑ i : Fin (3 : ℕ), ordinaryLane i omega;
            let rareLane : Fin (12 : ℕ) → Cutoff.CutoffSample d → ℝ :=
              ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare, collarBase,
                collarHead, collarBand,
                collarDeep, collarAfter, collarWave];
            let Uexp : Cutoff.CutoffSample d → ℝ := fun (omega : Cutoff.CutoffSample d) =>
              ∑ i : Fin (12 : ℕ), rareLane i omega;
            ∀
              (_ :
                ∀ (omega : Cutoff.CutoffSample d),
                  ∑ i : Fin d,
                      ∑' (a : ℕ),
                        ENNReal.ofReal
                          (Multiscale.probeSharpFramedMeanLayerEnvelope M R.scale (↑E : ℝ)
                            bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ)) m
                            (Cutoff.translateCutoffSample (triadicCubeShift R) omega) (basisVec i)
                            (Affine.superposedGradConst d)) ≤
                    ∑ x : Fin d, ∑' (a : ℕ), ENNReal.ofReal
                      (Multiscale.probeSharpFramedGoodBaseTerm d a (basisVec x)) +
                                          ∑ x : Fin d,
                                            ∑' (a : ℕ),
                                              ENNReal.ofReal
                                                (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                                  (↑E : ℝ) bfaProfileB
                                                  (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ))
                                                    (basisVec x)
                                                  (fun (eta : Cutoff.CutoffSample d) =>
                                                    Multiscale.waveHeadTerm M R.scale (↑E : ℝ)
                                                      bfaProfileB
                                                        (probeSharpLayerAnchor R.scale bfaProfileB
                                                          (collarBandMeanDepth M (↑E : ℝ)) a)
                                                        eta ^
                                                      (2 : ℕ))
                                                  (Cutoff.translateCutoffSample (triadicCubeShift
                                                    R) omega)) +
                                        ∑ x : Fin d,
                                          ∑' (a : ℕ),
                                            ENNReal.ofReal
                                              (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                                (↑E : ℝ) bfaProfileB
                                                (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ))
                                                  (basisVec x)
                                                (fun (_eta : Cutoff.CutoffSample d) =>
                                                  waveBandMean (probeDeepBandMeanAmplitude d)
                                                    M.gamma
                                                      (collarBandMeanDepth M (↑E : ℝ)) ^
                                                    (2 : ℕ))
                                                (Cutoff.translateCutoffSample (triadicCubeShift R)
                                                  omega)) +
                                      ∑ x : Fin d,
                                        ∑' (a : ℕ),
                                          ENNReal.ofReal
                                            (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E
                                              : ℝ) bfaProfileB
                                              (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ))
                                                (basisVec x)
                                              (fun (eta : Cutoff.CutoffSample d) =>
                                                probeDeepBandGaugedTail M (originCube d R.scale)
                                                    (probeSharpLayerAnchor R.scale bfaProfileB
                                                      (collarBandMeanDepth M (↑E : ℝ)) a)
                                                    (collarBandMeanDepth M (↑E : ℝ))
                                                      (collarBandMeanDepth M (↑E : ℝ)) eta ^
                                                  (2 : ℕ))
                                              (Cutoff.translateCutoffSample (triadicCubeShift R)
                                                omega)) +
                                    ∑ x : Fin d,
                                      ∑' (a : ℕ),
                                        ENNReal.ofReal
                                          (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E :
                                            ℝ) bfaProfileB
                                            (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ))
                                              (basisVec x)
                                            (fun (eta : Cutoff.CutoffSample d) =>
                                              probeSharpAfterBandTerm M R.scale
                                                  (probeSharpLayerAnchor R.scale bfaProfileB
                                                    (collarBandMeanDepth M (↑E : ℝ)) a)
                                                  (collarBandMeanDepth M (↑E : ℝ)) m eta ^
                                                (2 : ℕ))
                                            (Cutoff.translateCutoffSample (triadicCubeShift R)
                                              omega)) +
                                  ∑ x : Fin d,
                                    ∑' (a : ℕ),
                                      ENNReal.ofReal
                                        (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E :
                                          ℝ) bfaProfileB
                                          (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ))
                                            (basisVec x)
                                          (fun (eta : Cutoff.CutoffSample d) =>
                                            Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB
                                              R.scale
                                                (probeSharpLayerAnchor R.scale bfaProfileB
                                                  (collarBandMeanDepth M (↑E : ℝ))
                                                  a)
                                                eta ^
                                              (2 : ℕ))
                                          (Cutoff.translateCutoffSample (triadicCubeShift R)
                                            omega)) +
                                ∑ x : Fin d,
                                  ∑' (a : ℕ),
                                    ENNReal.ofReal
                                      (Multiscale.probeSharpFramedCollarBaseTerm M R.scale (↑E :
                                        ℝ) bfaProfileB
                                        (collarBandMeanDepth M (↑E : ℝ)) a (basisVec x)
                                          (Affine.superposedGradConst d)
                                        (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) +
                              ∑ x : Fin d,
                                ∑' (a : ℕ),
                                  ENNReal.ofReal
                                    (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                                      bfaProfileB
                                      (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ)) (basisVec x)
                                      (Affine.superposedGradConst d)
                                      (fun (eta : Cutoff.CutoffSample d) =>
                                        Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                                            (probeSharpLayerAnchor R.scale bfaProfileB
                                              (collarBandMeanDepth M (↑E : ℝ)) a)
                                            eta ^
                                          (2 : ℕ))
                                      (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) +
                            ∑ x : Fin d,
                              ∑' (a : ℕ),
                                ENNReal.ofReal
                                  (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                                    bfaProfileB
                                    (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ)) (basisVec x)
                                    (Affine.superposedGradConst d)
                                    (fun (_eta : Cutoff.CutoffSample d) =>
                                      waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
                                        (collarBandMeanDepth M (↑E : ℝ)) ^
                                        (2 : ℕ))
                                    (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) +
                          ∑ x : Fin d,
                            ∑' (a : ℕ),
                              ENNReal.ofReal
                                (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                                  bfaProfileB
                                  (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ)) (basisVec x)
                                  (Affine.superposedGradConst d)
                                  (fun (eta : Cutoff.CutoffSample d) =>
                                    probeDeepBandGaugedTail M (originCube d R.scale)
                                        (probeSharpLayerAnchor R.scale bfaProfileB
                                          (collarBandMeanDepth M (↑E : ℝ)) a)
                                        (collarBandMeanDepth M (↑E : ℝ)) (collarBandMeanDepth M
                                          (↑E : ℝ)) eta ^
                                      (2 : ℕ))
                                  (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) +
                        ∑ x : Fin d,
                          ∑' (a : ℕ),
                            ENNReal.ofReal
                              (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                                bfaProfileB
                                (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ)) (basisVec x)
                                  (Affine.superposedGradConst d)
                                (fun (eta : Cutoff.CutoffSample d) =>
                                  probeSharpAfterBandTerm M R.scale
                                      (probeSharpLayerAnchor R.scale bfaProfileB
                                        (collarBandMeanDepth M (↑E : ℝ)) a)
                                      (collarBandMeanDepth M (↑E : ℝ)) m eta ^
                                    (2 : ℕ))
                                (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) +
                      ∑ x : Fin d,
                        ∑' (a : ℕ),
                          ENNReal.ofReal
                            (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ)
                              bfaProfileB
                              (collarBandMeanDepth M (↑E : ℝ)) a (m - (1 : ℤ)) (basisVec x)
                                (Affine.superposedGradConst d)
                              (fun (eta : Cutoff.CutoffSample d) =>
                                Multiscale.waveTailTerm M R.scale (↑E : ℝ) bfaProfileB R.scale
                                    (probeSharpLayerAnchor R.scale bfaProfileB
                                      (collarBandMeanDepth M (↑E : ℝ)) a) eta ^
                                  (2 : ℕ))
                              (Cutoff.translateCutoffSample (triadicCubeShift R) omega)))
              (_ :
                ∀ (omega : Cutoff.CutoffSample d),
                  ENNReal.ofReal (Multiscale.probeSharpGoodBaseConst d) + ENNReal.ofReal
                    (bandOrdinary omega) ≤
                    ENNReal.ofReal Cblock)
              (_ : (0 : ℝ) ≤ Cblock)
              (_ :
                ∀ (omega : Cutoff.CutoffSample d),
                  ∑ j : Fin d,
                      ∑' (n : ℕ),
                        ENNReal.ofReal
                          (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                            (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                              (Affine.superposedGradConst d)
                            (fun (_eta : Cutoff.CutoffSample d) =>
                              waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
                                (collarBandMeanDepth M (↑E : ℝ)) ^
                                (2 : ℕ))
                            (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) =
                    ENNReal.ofReal (probeSharpFramedCollarBandMeanTunedTraceLane M m R (↑E : ℝ)
                      omega))
              (_ :
                ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                  (Cutoff.CutoffSample d)),
                  ENNReal.ofReal (probeSharpFramedCollarDeepTailTraceLane M m R (↑E : ℝ) omega) =
                    ∑ j : Fin d,
                      ∑' (n : ℕ),
                        ENNReal.ofReal
                          (have k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
                          Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                            k₀ n (m - (1 : ℤ))
                            (basisVec j) (Affine.superposedGradConst d)
                            (fun (eta : Cutoff.CutoffSample d) =>
                              probeDeepBandGaugedTail M (originCube d R.scale)
                                  (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀ eta ^
                                (2 : ℕ))
                            (Cutoff.translateCutoffSample (triadicCubeShift R) omega))),
              (∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                (Cutoff.CutoffSample d)),
                  cutoffBBlockFamily M m (↑(Annealed.sigmaBar M (m - (1 : ℤ))) : ℝ)⁻¹ R omega ≤
                    Cblock + Uone omega + Uexp omega) ∧
                Measurable fun (omega : Cutoff.CutoffSample d) =>
                  cutoffBBlockFamily M m (↑(Annealed.sigmaBar M (m - (1 : ℤ))) : ℝ)⁻¹ R omega

private abbrev superposedFluxUpperPerDescendant_comparisonBounds3_statement : Prop :=
  ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E })
   (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (sigma Clane : ℝ) (_ : (0
    : ℝ) < sigma)
   (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Clane / sigma))
    (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
   (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : goodHeadTunedOutputConst d ≤
    Clane)
   (_ : probeSharpBandMeanTunedOutputConst d ≤ Clane)
   (_ : probeSharpDeepBandTailTunedOutputConst d ≤ Clane)
   (_ : probeSharpAfterBandTunedOutputConst d ≤ Clane)
   (_ : probeSharpCollarBaseTunedOutputConst d ≤ Clane)
   (_ : collarHeadTunedPerDescendantOutputConst d ≤ Clane)
   (_ : profileAuxiliaryConst d ≤ Clane) (_ : (3 : ℕ) ≤ collarBandMeanDepth M
    (↑E : ℝ)) (k : ℕ)
   (R : TriadicCube d) (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))),
   (∀ (k : ℕ),
     ∀ R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)),
      ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
       (Cutoff.CutoffSample d)),
       ENNReal.ofReal (cutoffBBlockFamily M m (↑(Annealed.sigmaBar M (m - (1 : ℤ))) : ℝ)⁻¹
        R omega) ≤
        ∑ j : Fin d,
         ∑' (n : ℕ),
          ENNReal.ofReal
           (Multiscale.probeSharpFramedMeanLayerEnvelope M R.scale (↑E : ℝ) bfaProfileB
            (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) m
            (Cutoff.translateCutoffSample (triadicCubeShift R) omega) (basisVec j)
            (Affine.superposedGradConst d))) ∧
    ∃ (headOrdinary : Cutoff.CutoffSample d → ℝ) (headRare : Cutoff.CutoffSample d → ℝ)
     (headOrdinaryScale : ℝ)
     (headRareScale : ℝ),
     (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ headOrdinary omega) ∧
      Measurable headOrdinary ∧
       (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ headRare omega) ∧
        Measurable headRare ∧
         (∀ (omega : Cutoff.CutoffSample d),
           ∑ j : Fin d,
             ∑' (n : ℕ),
              ENNReal.ofReal
               (Multiscale.probeSharpFramedGoodWavePart M R.scale (↑E : ℝ)
                bfaProfileB
                (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                (fun (eta : Cutoff.CutoffSample d) =>
                 Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                   (probeSharpLayerAnchor R.scale bfaProfileB
                    (collarBandMeanDepth M (↑E : ℝ)) n) eta ^
                  (2 : ℕ))
                (Cutoff.translateCutoffSample (triadicCubeShift R) omega)) ≤
            ENNReal.ofReal (headOrdinary omega) + ENNReal.ofReal (headRare omega)) ∧
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
           (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (1 : ℝ)) headOrdinary headOrdinaryScale ∧
           headOrdinaryScale ≤ upperSaturatedPerCubeAmplitude Clane (Disorder.cstar M)
            M.gamma k ∧
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
             (Cutoff.CutoffSample d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) headRare
               headRareScale ∧
             headRareScale ≤ Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) *
              M.gamma⁻¹))) ^ (8 : ℕ) ∧
              ∃ (bandOrdinary : Cutoff.CutoffSample d → ℝ) (bandRare :
               Cutoff.CutoffSample d → ℝ)
               (bandRareScale : ℝ),
               (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ bandOrdinary omega) ∧
                (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ bandRare omega) ∧
                 Measurable bandRare ∧
                  (∀ (omega : Cutoff.CutoffSample d),
                    ∑ j : Fin d,
                      ∑' (n : ℕ),
                       ENNReal.ofReal
                        (Multiscale.probeSharpFramedGoodWavePart M R.scale
                         (↑E : ℝ) bfaProfileB
                         (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ))
                          (basisVec j)
                         (fun (_eta : Cutoff.CutoffSample d) =>
                          waveBandMean (probeDeepBandMeanAmplitude d)
                           M.gamma
                            (collarBandMeanDepth M (↑E : ℝ)) ^
                           (2 : ℕ))
                         (Cutoff.translateCutoffSample (triadicCubeShift
                          R) omega)) ≤
                     ENNReal.ofReal (bandOrdinary omega) + ENNReal.ofReal
                      (bandRare omega)) ∧
                   (∀ (omega : Cutoff.CutoffSample d), bandOrdinary omega ≤
                    Clane) ∧
                    IndependentSums.IsBigOWith
                      (↑(Cutoff.cutoffSampleLaw M) : Measure
                       (Cutoff.CutoffSample d))
                      (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 :
                       ℝ))) bandRare
                      bandRareScale ∧
                     bandRareScale ≤
                       Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) *
                        M.gamma⁻¹))) ^ (8 : ℕ) ∧
                      ∃ (deepOrdinary : Cutoff.CutoffSample d → ℝ) (deepRare :
                       Cutoff.CutoffSample d → ℝ) (deepOrdinaryScale : ℝ)
                        (deepRareScale : ℝ),
                       (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤
                        deepOrdinary omega) ∧
                        Measurable deepOrdinary ∧
                         (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤
                          deepRare omega) ∧
                          Measurable deepRare ∧
                           (∀ᵐ (omega :
                             Cutoff.CutoffSample
                              d) ∂(↑(Cutoff.cutoffSampleLaw M) :
                              Measure (Cutoff.CutoffSample d)),
                             ∑ j : Fin d,
                               ∑' (n : ℕ),
                                ENNReal.ofReal
                                 (Multiscale.probeSharpFramedGoodWavePart M R.scale
                                  (↑E : ℝ) bfaProfileB
                                   (collarBandMeanDepth M (↑E :
                                    ℝ)) n
                                  (m - (1 : ℤ)) (basisVec j)
                                  (fun (eta :
                                   Cutoff.CutoffSample d) =>
                                   probeDeepBandGaugedTail M
                                    (originCube d R.scale)
                                     (probeSharpLayerAnchor
                                      R.scale bfaProfileB
                                      (collarBandMeanDepth M
                                       (↑E : ℝ)) n)
                                     (collarBandMeanDepth M
                                      (↑E : ℝ))
                                     (collarBandMeanDepth M
                                      (↑E : ℝ)) eta ^
                                    (2 : ℕ))
                                  (Cutoff.translateCutoffSample
                                   (triadicCubeShift R)
                                   omega)) ≤
                              ENNReal.ofReal (deepOrdinary omega) +
                               ENNReal.ofReal (deepRare omega)) ∧
                            IndependentSums.IsBigOWith
                              (↑(Cutoff.cutoffSampleLaw M) : Measure
                               (Cutoff.CutoffSample d))
                              (IndependentSums.gammaSigma (1 : ℝ))
                               deepOrdinary
                              deepOrdinaryScale ∧
                             deepOrdinaryScale ≤
                               upperSaturatedPerCubeAmplitude Clane
                                (Disorder.cstar M)
                                M.gamma k ∧
                              IndependentSums.IsBigOWith
                                (↑(Cutoff.cutoffSampleLaw M) :
                                 Measure (Cutoff.CutoffSample d))
                                (IndependentSums.gammaSigma (((1 :
                                 ℝ) - sigma) / (3 : ℝ)))
                                deepRare deepRareScale ∧
                               deepRareScale ≤
                                 Real.exp
                                   (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^
                                    (2 : ℕ) * M.gamma⁻¹))) ^
                                  (8 : ℕ) ∧
                                ∃ (afterOrdinary :
                                 Cutoff.CutoffSample d → ℝ)
                                  (afterRare :
                                 Cutoff.CutoffSample d → ℝ)
                                  (afterOrdinaryScale : ℝ)
                                 (afterRareScale : ℝ),
                                 (∀ (omega : Cutoff.CutoffSample
                                  d),
                                   (0 : ℝ) ≤ afterOrdinary
                                    omega) ∧
                                  Measurable afterOrdinary ∧
                                   (∀ (omega :
                                    Cutoff.CutoffSample d),
                                     (0 : ℝ) ≤ afterRare
                                      omega) ∧
                                    Measurable afterRare ∧
                                     (∀ᵐ (omega :
                                       Cutoff.CutoffSample
                                        d)
                                         ∂(↑(Cutoff.cutoffSampleLaw M) :
                                        Measure
                                         (Cutoff.CutoffSample d)),
                                       ∑ j : Fin d,
                                         ∑' (n : ℕ),
                                          ENNReal.ofReal
                                           (Multiscale.probeSharpFramedGoodWavePart
                                            M R.scale
                                             (↑E : ℝ)
                                              bfaProfileB
                                            (collarBandMeanDepth M (↑E : ℝ)) n
                                            (m - (1 :
                                             ℤ))
                                              (basisVec j)
                                            (fun
                                              (eta :
                                               Cutoff.CutoffSample d) =>
                                             probeSharpAfterBandTerm M R.scale
                                               (probeSharpLayerAnchor R.scale
                                                bfaProfileB
                                                (collarBandMeanDepth M
                                                 (↑E : ℝ))
                                                n)
                                               (collarBandMeanDepth M
                                                (↑E : ℝ))
                                               m
                                                eta ^
                                              (2 : ℕ))
                                            (Cutoff.translateCutoffSample
                                             (triadicCubeShift R) omega)) ≤
                                        ENNReal.ofReal
                                         (afterOrdinary
                                          omega) +
                                         ENNReal.ofReal
                                          (afterRare
                                           omega)) ∧
                                      IndependentSums.IsBigOWith
                                        (↑(Cutoff.cutoffSampleLaw M) :
                                         Measure
                                          (Cutoff.CutoffSample d))
                                        (IndependentSums.gammaSigma (1 : ℝ))
                                        afterOrdinary
                                         afterOrdinaryScale ∧
                                       afterOrdinaryScale ≤
                                         upperSaturatedPerCubeAmplitude Clane
                                          (Disorder.cstar M) M.gamma k ∧
                                        IndependentSums.IsBigOWith
                                          (↑(Cutoff.cutoffSampleLaw M) :
                                           Measure
                                            (Cutoff.CutoffSample d))
                                          (IndependentSums.gammaSigma
                                           (((1 : ℝ) -
                                            sigma) /
                                             (3 : ℝ)))
                                          afterRare
                                           afterRareScale ∧
                                         afterRareScale ≤
                                           (3 : ℝ) ^
                                             (M.gamma
                                              * (↑(k
                                               + (1
                                                :
                                                 ℕ)) : ℝ)) *
                                            Real.exp
                                              (-(Clane⁻¹ *
                                                ((↑E : ℝ)⁻¹ ^ (2 : ℕ) *
                                                 M.gamma⁻¹))) ^
                                             (8 : ℕ) ∧
                                          (have laneX :
                                           ℝ :=
                                            (↑E : ℝ)⁻¹
                                             ^ (2 :
                                              ℕ) *
                                               M.gamma⁻¹;
                                           have _
                                            : ℝ :=
                                            Real.exp
                                             (-(Clane⁻¹ * laneX));
                                           IndependentSums.IsBigOWith
                                            (↑(Cutoff.cutoffSampleLaw M) :
                                             Measure
                                              (Cutoff.CutoffSample d))
                                            (IndependentSums.gammaSigma
                                             (((1 :
                                              ℝ) -
                                               sigma) / (3 : ℝ)))
                                            (probeSharpFramedCollarBaseTraceLane
                                             M R (↑E
                                              : ℝ)
                                             (collarBandMeanDepth M (↑E : ℝ)))
                                            ((3 : ℝ) ^
                                              (M.gamma *
                                               ((↑k
                                                :
                                                 ℝ) + (1 : ℝ))) *
                                             Real.exp
                                               (-(Clane⁻¹ *
                                                 ((↑E : ℝ)⁻¹ ^ (2 : ℕ) *
                                                  M.gamma⁻¹))) ^
                                              (8 :
                                               ℕ))) ∧
                                           (∀ (omega :
                                            Cutoff.CutoffSample d),
                                             (0 : ℝ) ≤
                                              (fun
                                                 (omega :
                                                  Cutoff.CutoffSample
                                                   d) =>
                                                ∑
                                                 j : Fin d,
                                                 ∑' (n : ℕ),
                                                  Multiscale.probeSharpFramedCollarWavePart
                                                   M R.scale (↑E : ℝ)
                                                   bfaProfileB
                                                   (collarBandMeanDepth M
                                                    (↑E : ℝ))
                                                   n (m - (1 : ℤ))
                                                   (basisVec j)
                                                   (Affine.superposedGradConst
                                                    d)
                                                   (fun
                                                     (eta :
                                                      Cutoff.CutoffSample
                                                       d) =>
                                                    Multiscale.waveHeadTerm
                                                      M R.scale
                                                      (↑E : ℝ)
                                                      bfaProfileB
                                                      (probeSharpLayerAnchor
                                                       R.scale
                                                       bfaProfileB
                                                       (collarBandMeanDepth
                                                        M (↑E : ℝ))
                                                       n)
                                                      eta ^
                                                     (2 : ℕ))
                                                   (Cutoff.translateCutoffSample
                                                    (triadicCubeShift R)
                                                    omega))
                                               omega) ∧
                                            (Measurable
                                              fun
                                               (omega :
                                                Cutoff.CutoffSample d) =>
                                              ∑ j :
                                               Fin d,
                                               ∑'
                                                (n
                                                 : ℕ),
                                                Multiscale.probeSharpFramedCollarWavePart
                                                 M R.scale (↑E : ℝ)
                                                 bfaProfileB
                                                 (collarBandMeanDepth M
                                                  (↑E : ℝ))
                                                 n (m - (1 : ℤ))
                                                 (basisVec j)
                                                 (Affine.superposedGradConst
                                                  d)
                                                 (fun
                                                   (eta :
                                                    Cutoff.CutoffSample
                                                     d) =>
                                                  Multiscale.waveHeadTerm
                                                    M R.scale (↑E : ℝ)
                                                    bfaProfileB
                                                    (probeSharpLayerAnchor
                                                     R.scale
                                                     bfaProfileB
                                                     (collarBandMeanDepth
                                                      M (↑E : ℝ))
                                                     n)
                                                    eta ^
                                                   (2 : ℕ))
                                                 (Cutoff.translateCutoffSample
                                                  (triadicCubeShift R)
                                                  omega)) ∧
                                             (∀ᵐ
                                              (omega :
                                               Cutoff.CutoffSample
                                                d)
                                                 ∂(↑(Cutoff.cutoffSampleLaw
                                                  M) :
                                                Measure
                                                 (Cutoff.CutoffSample d)),
                                               ENNReal.ofReal
                                                 ((fun
                                                    (omega :
                                                     Cutoff.CutoffSample
                                                      d) =>
                                                   ∑ j : Fin d,
                                                    ∑' (n : ℕ),
                                                     Multiscale.probeSharpFramedCollarWavePart
                                                      M R.scale
                                                      (↑E : ℝ)
                                                      bfaProfileB
                                                      (collarBandMeanDepth
                                                       M (↑E : ℝ))
                                                      n (m - (1 : ℤ))
                                                      (basisVec j)
                                                      (Affine.superposedGradConst
                                                       d)
                                                      (fun
                                                        (eta :
                                                         Cutoff.CutoffSample
                                                          d) =>
                                                       Multiscale.waveHeadTerm
                                                         M R.scale
                                                         (↑E : ℝ)
                                                         bfaProfileB
                                                         (probeSharpLayerAnchor
                                                          R.scale
                                                          bfaProfileB
                                                          (collarBandMeanDepth
                                                           M
                                                           (↑E :
                                                            ℝ))
                                                          n)
                                                         eta ^
                                                        (2 : ℕ))
                                                      (Cutoff.translateCutoffSample
                                                       (triadicCubeShift
                                                        R)
                                                       omega))
                                                  omega) =
                                                ∑
                                                 j : Fin d,
                                                 ∑' (n : ℕ),
                                                  ENNReal.ofReal
                                                   (Multiscale.probeSharpFramedCollarWavePart
                                                    M R.scale (↑E : ℝ)
                                                    bfaProfileB
                                                    (collarBandMeanDepth
                                                     M (↑E : ℝ))
                                                    n (m - (1 : ℤ))
                                                    (basisVec j)
                                                    (Affine.superposedGradConst
                                                     d)
                                                    (fun
                                                      (eta :
                                                       Cutoff.CutoffSample
                                                        d) =>
                                                     Multiscale.waveHeadTerm
                                                       M R.scale
                                                       (↑E : ℝ)
                                                       bfaProfileB
                                                       (probeSharpLayerAnchor
                                                        R.scale
                                                        bfaProfileB
                                                        (collarBandMeanDepth
                                                         M
                                                         (↑E : ℝ))
                                                        n)
                                                       eta ^
                                                      (2 : ℕ))
                                                    (Cutoff.translateCutoffSample
                                                     (triadicCubeShift
                                                      R)
                                                     omega))) ∧
                                              IndependentSums.IsBigOWith
                                                (↑(Cutoff.cutoffSampleLaw
                                                   M) :
                                                 Measure
                                                  (Cutoff.CutoffSample d))
                                                (IndependentSums.gammaSigma
                                                 (((1 : ℝ) - sigma) /
                                                  (3 : ℝ)))
                                                (fun
                                                  (omega :
                                                   Cutoff.CutoffSample
                                                    d) =>
                                                 ∑ j : Fin d,
                                                  ∑' (n : ℕ),
                                                   Multiscale.probeSharpFramedCollarWavePart
                                                    M R.scale (↑E : ℝ)
                                                    bfaProfileB
                                                    (collarBandMeanDepth
                                                     M (↑E : ℝ))
                                                    n (m - (1 : ℤ))
                                                    (basisVec j)
                                                    (Affine.superposedGradConst
                                                     d)
                                                    (fun
                                                      (eta :
                                                       Cutoff.CutoffSample
                                                        d) =>
                                                     Multiscale.waveHeadTerm
                                                       M R.scale
                                                       (↑E : ℝ)
                                                       bfaProfileB
                                                       (probeSharpLayerAnchor
                                                        R.scale
                                                        bfaProfileB
                                                        (collarBandMeanDepth
                                                         M
                                                         (↑E : ℝ))
                                                        n)
                                                       eta ^
                                                      (2 : ℕ))
                                                    (Cutoff.translateCutoffSample
                                                     (triadicCubeShift
                                                      R)
                                                     omega))
                                                ((3 : ℝ) ^
                                                  (M.gamma *
                                                   ((↑k : ℝ) +
                                                    (1 : ℝ))) *
                                                 Real.exp
                                                   (-(Clane⁻¹ *
                                                     ((↑E : ℝ)⁻¹ ^
                                                       (2 : ℕ) *
                                                      M.gamma⁻¹))) ^
                                                  (8 : ℕ)) ∧
                                               True


private theorem named_layer_ennreal_bound
    {d : ℕ} (M : ABKModel d) (m : ℤ) (E : ℝ) (R : TriadicCube d)
    (j : Fin d) (n : ℕ) (omega : Cutoff.CutoffSample d) :
    let ell :=
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
        R.scale Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n
    let headSq := fun eta =>
      Algsuperdiff.Section3.Provider.Multiscale.waveHeadTerm
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB ell eta ^ 2
    let bandSq := fun _eta =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.waveBandMean
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeDeepBandMeanAmplitude d)
        M.gamma
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) ^ 2
    let deepSq := fun eta =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeDeepBandGaugedTail
        M (originCube d R.scale) ell
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ))
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) eta ^ 2
    let afterSq := fun eta =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpAfterBandTerm
        M R.scale ell
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) m eta ^ 2
    let tailSq := fun eta =>
      Algsuperdiff.Section3.Provider.Multiscale.waveTailTerm
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        R.scale ell eta ^ 2
    let translated :=
      Algsuperdiff.Section3.Cutoff.translateCutoffSample (triadicCubeShift R) omega
    ENNReal.ofReal
        (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedMeanLayerEnvelope
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) n (m - 1) m translated (basisVec j)
          (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)) ≤
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodBaseTerm
            d n (basisVec j)) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) headSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) bandSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) deepSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) afterSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) tailSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarBaseTerm
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) headSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) bandSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) deepSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) afterSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) tailSq translated) := by
  dsimp only
  rw [Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedMeanLayerEnvelope_eq_namedSum]
  unfold Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedLayerNamedSum
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  exact ENNReal.ofReal_add_le

private theorem merge_twelve_ennreal_lanes
    {S a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : ENNReal}
    {g ho hr bo br do_ dr ao ar wb wr cb ch cband cd ca cw : ENNReal}
    (hS : S ≤ a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11)
    (h0 : a0 ≤ g) (h1 : a1 ≤ ho + hr) (h2 : a2 ≤ bo + br)
    (h3 : a3 ≤ do_ + dr) (h4 : a4 ≤ ao + ar) (h5 : a5 ≤ wb + wr)
    (h6 : a6 ≤ cb) (h7 : a7 ≤ ch) (h8 : a8 ≤ cband) (h9 : a9 ≤ cd)
    (h10 : a10 ≤ ca) (h11 : a11 ≤ cw) :
    S ≤ (g + bo) + (ho + do_ + ao) +
      (hr + br + dr + ar + wb + wr + cb + ch + cband + cd + ca + cw) := by
  calc
    S ≤ a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 := hS
    _ ≤ g + (ho + hr) + (bo + br) + (do_ + dr) + (ao + ar) + (wb + wr) +
        cb + ch + cband + cd + ca + cw := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (add_le_add
                (add_le_add
                  (add_le_add
                    (add_le_add
                      (add_le_add
                        (add_le_add
                          (add_le_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
    _ = _ := by ring

private theorem pack_twelve_ennreal_lanes
    {g bo ho do_ ao hr br dr ar wb wr cb ch cband cd ca cw C : ENNReal}
    (hdet : g + bo ≤ C) :
    (g + bo) + (ho + do_ + ao) +
        (hr + br + dr + ar + wb + wr + cb + ch + cband + cd + ca + cw) ≤
      C + (∑ i : Fin 3, ![ho, do_, ao] i) +
        (∑ i : Fin 12, ![hr, br, dr, ar, wb, wr, cb, ch, cband, cd, ca, cw] i) := by
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, add_assoc]
  simpa only [add_assoc] using add_le_add hdet
    (le_refl (ho + do_ + ao + hr + br + dr + ar + wb + wr + cb + ch +
      cband + cd + ca + cw))

private theorem real_three_term_of_ennreal
    {x C u v : ℝ} {S : ENNReal}
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : ENNReal.ofReal x ≤ S)
    (hS : S ≤ ENNReal.ofReal C + ENNReal.ofReal u + ENNReal.ofReal v) :
    x ≤ C + u + v := by
  have hsum : ENNReal.ofReal C + ENNReal.ofReal u + ENNReal.ofReal v =
      ENNReal.ofReal (C + u + v) := by
    calc
      _ = ENNReal.ofReal (C + u) + ENNReal.ofReal v :=
        congrArg (fun z => z + ENNReal.ofReal v) (ENNReal.ofReal_add hC hu).symm
      _ = _ := (ENNReal.ofReal_add (add_nonneg hC hu) hv).symm
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (add_nonneg hC hu) hv)).1 ((hx.trans hS).trans_eq hsum)

private theorem ae_twelve_lane_domination
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {X g ho hr bo br do_ dr ao ar wb wr cb ch cband cd ca cw Uone Uexp : Omega → ℝ}
    {C : ℝ} {S a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Omega → ENNReal}
    (hC : 0 ≤ C) (hUone0 : ∀ omega, 0 ≤ Uone omega)
    (hUexp0 : ∀ omega, 0 ≤ Uexp omega)
    (hpotential : ∀ᵐ omega ∂mu, ENNReal.ofReal (X omega) ≤ S omega)
    (hEnvelope : ∀ omega, S omega ≤
      a0 omega + a1 omega + a2 omega + a3 omega + a4 omega + a5 omega +
        a6 omega + a7 omega + a8 omega + a9 omega + a10 omega + a11 omega)
    (h0 : ∀ omega, a0 omega = ENNReal.ofReal (g omega))
    (h1 : ∀ omega, a1 omega ≤ ENNReal.ofReal (ho omega) + ENNReal.ofReal (hr omega))
    (h2 : ∀ omega, a2 omega ≤ ENNReal.ofReal (bo omega) + ENNReal.ofReal (br omega))
    (h3 : ∀ᵐ omega ∂mu, a3 omega ≤ ENNReal.ofReal (do_ omega) + ENNReal.ofReal (dr omega))
    (h4 : ∀ᵐ omega ∂mu, a4 omega ≤ ENNReal.ofReal (ao omega) + ENNReal.ofReal (ar omega))
    (h5 : ∀ᵐ omega ∂mu, a5 omega ≤ ENNReal.ofReal (wb omega) + ENNReal.ofReal (wr omega))
    (h6 : ∀ omega, a6 omega = ENNReal.ofReal (cb omega))
    (h7 : ∀ᵐ omega ∂mu, ENNReal.ofReal (ch omega) = a7 omega)
    (h8 : ∀ omega, a8 omega = ENNReal.ofReal (cband omega))
    (h9 : ∀ᵐ omega ∂mu, ENNReal.ofReal (cd omega) = a9 omega)
    (h10 : ∀ᵐ omega ∂mu, ENNReal.ofReal (ca omega) = a10 omega)
    (h11 : ∀ᵐ omega ∂mu, ENNReal.ofReal (cw omega) = a11 omega)
    (hdet : ∀ omega, ENNReal.ofReal (g omega) + ENNReal.ofReal (bo omega) ≤
      ENNReal.ofReal C)
    (hone : ∀ omega, ENNReal.ofReal (Uone omega) =
      ∑ i : Fin 3, ![ENNReal.ofReal (ho omega), ENNReal.ofReal (do_ omega),
        ENNReal.ofReal (ao omega)] i)
    (hexp : ∀ omega, ENNReal.ofReal (Uexp omega) =
      ∑ i : Fin 12, ![ENNReal.ofReal (hr omega), ENNReal.ofReal (br omega),
        ENNReal.ofReal (dr omega), ENNReal.ofReal (ar omega), ENNReal.ofReal (wb omega),
        ENNReal.ofReal (wr omega), ENNReal.ofReal (cb omega), ENNReal.ofReal (ch omega),
        ENNReal.ofReal (cband omega), ENNReal.ofReal (cd omega), ENNReal.ofReal (ca omega),
        ENNReal.ofReal (cw omega)] i) :
    ∀ᵐ omega ∂mu, X omega ≤ C + Uone omega + Uexp omega := by
  filter_upwards [hpotential, h3, h4, h5, h7, h9, h10, h11] with
    omega hpot h3' h4' h5' h7' h9' h10' h11'
  have hmerged := (merge_twelve_ennreal_lanes
    (hEnvelope omega) (h0 omega).le (h1 omega) (h2 omega) h3' h4' h5'
    (h6 omega).le h7'.symm.le (h8 omega).le h9'.symm.le h10'.symm.le
    h11'.symm.le).trans (pack_twelve_ennreal_lanes (hdet omega))
  rw [← hone omega, ← hexp omega] at hmerged
  exact real_three_term_of_ennreal hC (hUone0 omega) (hUexp0 omega)
    hpot hmerged

private theorem nonnegative_pointwise_repair
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X Uone Uexp : Omega → ℝ} {C Aone Aexp : ℝ} {Ψone Ψexp : ℝ → ℝ}
    (hXmeas : Measurable X)
    (hUone0 : ∀ omega, 0 ≤ Uone omega) (hUoneMeas : Measurable Uone)
    (hUexp0 : ∀ omega, 0 ≤ Uexp omega) (hUexpMeas : Measurable Uexp)
    (hUoneO : HCPolySupport.IndependentSums.IsBigOWith mu Ψone Uone Aone)
    (hUexpO : HCPolySupport.IndependentSums.IsBigOWith mu Ψexp Uexp Aexp)
    (hae : ∀ᵐ omega ∂mu, X omega ≤ C + Uone omega + Uexp omega) :
    ∃ Uone' Uexp' : Omega → ℝ,
      (∀ omega, 0 ≤ Uone' omega) ∧ Measurable Uone' ∧
      (∀ omega, 0 ≤ Uexp' omega) ∧ Measurable Uexp' ∧
      (∀ omega, X omega ≤ C + Uone' omega + Uexp' omega) ∧
      HCPolySupport.IndependentSums.IsBigOWith mu Ψone Uone' Aone ∧
      HCPolySupport.IndependentSums.IsBigOWith mu Ψexp Uexp' Aexp := by
  let Uexp' : Omega → ℝ := fun omega =>
    max (Uexp omega) (X omega - C - Uone omega)
  have hUexp'0 : ∀ omega, 0 ≤ Uexp' omega := fun omega =>
    (hUexp0 omega).trans (le_max_left _ _)
  have hUexp'Meas : Measurable Uexp' :=
    hUexpMeas.max ((hXmeas.sub measurable_const).sub hUoneMeas)
  have hdom : ∀ omega, X omega ≤ C + Uone omega + Uexp' omega := by
    intro omega
    have hmax := le_max_right (Uexp omega) (X omega - C - Uone omega)
    dsimp only [Uexp']
    linarith
  have hAE : Uexp =ᵐ[mu] Uexp' := by
    filter_upwards [hae] with omega homega
    dsimp only [Uexp']
    rw [max_eq_left]
    linarith
  exact ⟨Uone, Uexp', hUone0, hUoneMeas, hUexp'0, hUexp'Meas, hdom,
    hUoneO, Algsuperdiff.Section3.Provider.Tail.isBigOWith_of_ae_eq hAE hUexpO⟩

private theorem superposedFlux_ordinaryContribution :
    ∀ {d : ℕ} (M : ABKModel d) (sigma Clane : ℝ),
      (0 : ℝ) < sigma →
        sigma ≤ (1 / 2 : ℝ) →
          (0 : ℝ) < Clane →
            let Cblock : ℝ := ((12 : ℝ) + (12 : ℝ) * IndependentSums.gammaTriangleConst (1 : ℝ)) *
              Clane;
            ∀ (k : ℕ) (headOrdinary : Cutoff.CutoffSample d → ℝ) (headOrdinaryScale : ℝ),
              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ headOrdinary omega) →
                Measurable headOrdinary →
                  IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                    (Cutoff.CutoffSample d))
                      (IndependentSums.gammaSigma (1 : ℝ)) headOrdinary headOrdinaryScale →
                    headOrdinaryScale ≤ upperSaturatedPerCubeAmplitude Clane (Disorder.cstar M)
                      M.gamma k →
                      ∀ (deepOrdinary : Cutoff.CutoffSample d → ℝ) (deepOrdinaryScale : ℝ),
                        (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ deepOrdinary omega) →
                          Measurable deepOrdinary →
                            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                              (Cutoff.CutoffSample d))
                                (IndependentSums.gammaSigma (1 : ℝ)) deepOrdinary
                                  deepOrdinaryScale →
                              deepOrdinaryScale ≤ upperSaturatedPerCubeAmplitude Clane
                                (Disorder.cstar M) M.gamma k →
                                ∀ (afterOrdinary : Cutoff.CutoffSample d → ℝ) (afterOrdinaryScale
                                  : ℝ),
                                  (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ afterOrdinary
                                    omega) →
                                    Measurable afterOrdinary →
                                      IndependentSums.IsBigOWith
                                          (↑(Cutoff.cutoffSampleLaw M) : Measure
                                            (Cutoff.CutoffSample d))
                                          (IndependentSums.gammaSigma (1 : ℝ)) afterOrdinary
                                            afterOrdinaryScale →
                                        afterOrdinaryScale ≤
                                            upperSaturatedPerCubeAmplitude Clane (Disorder.cstar
                                              M) M.gamma k →
                                          let _ : ℝ :=
                                            upperSaturatedPerCubeAmplitude Clane (Disorder.cstar
                                              M) M.gamma k;
                                          let ordinaryLane : Fin (3 : ℕ) → Cutoff.CutoffSample d →
                                            ℝ :=
                                            ![headOrdinary, deepOrdinary, afterOrdinary];
                                          let Uone : Cutoff.CutoffSample d → ℝ := fun (omega :
                                            Cutoff.CutoffSample d) =>
                                            ∑ i : Fin (3 : ℕ), ordinaryLane i omega;
                                          (∀ (i : Fin (3 : ℕ)) (omega : Cutoff.CutoffSample d),
                                              (0 : ℝ) ≤ ordinaryLane i omega) ∧
                                            (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ Uone
                                              omega) ∧
                                              Measurable Uone ∧
                                                IndependentSums.IsBigOWith
                                                  (↑(Cutoff.cutoffSampleLaw M) : Measure
                                                    (Cutoff.CutoffSample d))
                                                  (IndependentSums.gammaSigma (1 : ℝ)) Uone
                                                  (upperSaturatedPerCubeAmplitude Cblock
                                                    (Disorder.cstar M) M.gamma k) := by
  intro _ M _ Clane _ _ hlanePos Cblock k _ _ hheadOrdinaryNonneg hheadOrdinaryMeasurable
    hheadOrdinaryO hheadOrdinaryScaleLe _ _ hdeepOrdinaryNonneg hdeepOrdinaryMeasurable
      hdeepOrdinaryO hdeepOrdinaryScaleLe _ _ hafterOrdinaryNonneg hafterOrdinaryMeasurable
        hafterOrdinaryO hafterOrdinaryScaleLe perCubeScale ordinaryLane Uone
  have hperCubeScalePos : 0 <
      perCubeScale :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude_pos
      hlanePos (Disorder.cstar_characterization M).1
        M.shellPrefix.gamma_pos k
  have hheadOrdinaryFull :=
    hheadOrdinaryO.mono_scale hheadOrdinaryScaleLe
  have hdeepOrdinaryFull :=
    hdeepOrdinaryO.mono_scale hdeepOrdinaryScaleLe
  have hafterOrdinaryFull :=
    hafterOrdinaryO.mono_scale hafterOrdinaryScaleLe
  have hordinaryLaneNonneg : ∀ i, ∀ omega, 0 ≤ ordinaryLane i omega := by
    intro i
    fin_cases i
    · simpa [ordinaryLane] using hheadOrdinaryNonneg
    · simpa [ordinaryLane] using hdeepOrdinaryNonneg
    · simpa [ordinaryLane] using hafterOrdinaryNonneg
  have hordinaryLaneMeasurable : ∀ i, Measurable (ordinaryLane i) := by
    intro i
    fin_cases i
    · simpa [ordinaryLane] using hheadOrdinaryMeasurable
    · simpa [ordinaryLane] using hdeepOrdinaryMeasurable
    · simpa [ordinaryLane] using hafterOrdinaryMeasurable
  have hordinaryLaneO : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HCPolySupport.IndependentSums.IsBigO
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 1)
        (ordinaryLane i) perCubeScale := by
    intro i _
    apply (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (hordinaryLaneNonneg i)).1
    fin_cases i
    · simpa [ordinaryLane] using hheadOrdinaryFull
    · simpa [ordinaryLane] using hdeepOrdinaryFull
    · simpa [ordinaryLane] using hafterOrdinaryFull
  have hordinarySymmetric :=
    HCPolySupport.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (Finset.univ : Finset (Fin 3)) one_pos
      ⟨0, Finset.mem_univ 0⟩
      (fun _ _ => hperCubeScalePos) hordinaryLaneO
      (fun i _ => hordinaryLaneMeasurable i)
  have hUoneNonneg : ∀ omega, 0 ≤ Uone omega := by
    intro omega
    exact Finset.sum_nonneg fun i _ => hordinaryLaneNonneg i omega
  have hUoneMeasurable : Measurable Uone := by
    exact Finset.measurable_fun_sum Finset.univ fun i _ =>
      hordinaryLaneMeasurable i
  have hUoneRaw :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 1) Uone
        (HCPolySupport.IndependentSums.gammaTriangleConst 1 *
          ∑ _i : Fin 3, perCubeScale) := by
    apply (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      hUoneNonneg).2
    simpa only [Uone] using hordinarySymmetric
  have hUoneScale :
      HCPolySupport.IndependentSums.gammaTriangleConst 1 *
          (∑ _i : Fin 3, perCubeScale) ≤
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
          Cblock (Disorder.cstar M) M.gamma k := by
    let Z : ℝ := (Disorder.cstar M)⁻¹ *
      min 1 (M.gamma * ((k : ℝ) + 1)) *
      (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1))
    have hZ : 0 ≤ Z := by
      dsimp only [Z]
      positivity [M.shellPrefix.gamma_pos,
        (Disorder.cstar_characterization M).1]
    have hcoeff : 3 *
          HCPolySupport.IndependentSums.gammaTriangleConst 1 ≤
        12 + 12 *
          HCPolySupport.IndependentSums.gammaTriangleConst 1 := by
      have htriangle : 0 <
          HCPolySupport.IndependentSums.gammaTriangleConst 1 :=
        HCPolySupport.IndependentSums.gammaTriangleConst_pos
      linarith
    simp only
      [perCubeScale,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    calc
      _ = (3 * HCPolySupport.IndependentSums.gammaTriangleConst 1) *
            (Clane * Z) := by
          dsimp only [Z]
          ring
      _ ≤ (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) *
            (Clane * Z) := by
          exact mul_le_mul_of_nonneg_right hcoeff
            (mul_nonneg hlanePos.le hZ)
      _ = _ := by
          dsimp only [Cblock, Z]
          ring
  have hUone :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 1)
        Uone
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
          Cblock (Disorder.cstar M) M.gamma k) := by
    exact hUoneRaw.mono_scale hUoneScale
  exact ⟨hordinaryLaneNonneg, hUoneNonneg, hUoneMeasurable, hUone⟩

private theorem superposedFluxUpperPerDescendant_estimate1 :
    ∀ {d : ℕ} (M : ABKModel d) (E : { E : ℝ // (1 : ℝ) ≤ E })
      (R : TriadicCube d) (_ : (2 : ℕ) ≤ d),
      let collarBase : Cutoff.CutoffSample d → ℝ :=
        probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ));
      ∀ (omega : Cutoff.CutoffSample d),
        ∑ j : Fin d,
            ∑' (n : ℕ),
              ENNReal.ofReal
                (Multiscale.probeSharpFramedCollarBaseTerm M R.scale (↑E : ℝ) bfaProfileB
                  (collarBandMeanDepth M (↑E : ℝ)) n
                  (basisVec j) (Affine.superposedGradConst d) (Cutoff.translateCutoffSample
                    (triadicCubeShift R) omega)) =
          ENNReal.ofReal (collarBase omega) := by
  intro d M E R hd _ omega
  change (∑ j : Fin d,
      probeSharpFramedCollarBaseCoordinateENNRealLane
        M R (E : ℝ)
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) j omega) =
    ENNReal.ofReal
      (∑ j : Fin d,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseCoordinateLane
          M R (E : ℝ)
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) j omega)
  rw [ENNReal.ofReal_sum_of_nonneg]
  · exact Finset.sum_congr rfl fun j _ =>
      probeSharpFramedCollarBaseCoordinateENNRealLane_eq
        hd M R (E : ℝ)
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) j omega
  · intro j _
    exact
      probeSharpFramedCollarBaseCoordinateLane_nonneg
        hd M R (E : ℝ)
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) j omega

private theorem superposedFluxUpperPerDescendant_momentBounds1 :
  superposedFluxUpperPerDescendant_momentBounds1_statement := by
  intro d M m E hstate sigma _ hsigma0 hsigmaHalf hmaxLane hE2 hprofileAuxLane hdepthThresholdLane
    _ R hR hd _ _ _ _ _ _ _ rarePerLaneScale collarBase _ collarBand collarDeep _ _ _ _
      hrarePerLaneScalePos _ Uexp hUexpRaw K
  have htriangleBound :
      HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) ≤
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst := by
    simpa only
      [Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
      using
        Algsuperdiff.Section3.Provider.CoarseEllipticity.gammaTriangleConst_upperProfileTarget_le
        hsigma0 hsigmaHalf
  have hrawRareScale :
      HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) *
          (∑ _i : Fin 12, rarePerLaneScale) ≤
        K * rarePerLaneScale := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    calc
      HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) *
            (12 * rarePerLaneScale) =
          (12 * HCPolySupport.IndependentSums.gammaTriangleConst
            ((1 - sigma) / 3)) * rarePerLaneScale := by ring
      _ ≤ (12 *
            Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst) *
          rarePerLaneScale :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htriangleBound (by norm_num))
          hrarePerLaneScalePos.le
      _ = K * rarePerLaneScale := by rfl
  have hUexp :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        Uexp
      (K * rarePerLaneScale) := hUexpRaw.mono_scale hrawRareScale
  have hgoodBaseENNReal :
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodBaseTerm
          d n (basisVec j))) =
        ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpGoodBaseConst d) := by
    change
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedGoodBaseTraceENNRealLane d
        = _
    exact
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedGoodBaseTraceENNRealLane_eq
        hd
  have hcollarBaseENNReal (omega : Cutoff.CutoffSample d) :
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarBaseTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) n (basisVec j)
          (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
          (Algsuperdiff.Section3.Cutoff.translateCutoffSample
            (triadicCubeShift R) omega))) = ENNReal.ofReal (collarBase omega)  :=
              @superposedFluxUpperPerDescendant_estimate1 (d) (M) (E) (R) (hd) (omega)
  have hcstarE : (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    (le_max_right _ _).trans hmaxLane
  have hcollarBandENNReal (omega : Cutoff.CutoffSample d) :
      probeSharpFramedCollarBandMeanTunedTraceENNRealLane
          M m R (E : ℝ) omega = ENNReal.ofReal (collarBand omega) := by
    simpa only [collarBand] using
      probeSharpFramedCollarBandMeanTunedTraceENNRealLane_eq
        hd M hR E.property hcstarE hE2 omega
  have hcollarDeepENNReal :
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        ENNReal.ofReal (collarDeep omega) =
          ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailLayer
              M m R (E : ℝ) j n omega) := by
    simpa only [collarDeep] using
      ae_ofReal_probeSharpFramedCollarDeepTailTraceLane_eq_sum_tsum
        M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
          (max_le hprofileAuxLane hdepthThresholdLane)
  exact ⟨hUexp, hgoodBaseENNReal, hcollarBaseENNReal, hcollarBandENNReal, hcollarDeepENNReal⟩

private theorem superposedFluxUpperPerDescendant_momentBounds2 :
  superposedFluxUpperPerDescendant_momentBounds2_statement := by
  intro _ M _ _ sigma _ _ _ _ _ _ hheadRareNonneg hheadRareMeasurable _ hbandRareNonneg
    hbandRareMeasurable _ hdeepRareNonneg hdeepRareMeasurable _ hafterRareNonneg
      hafterRareMeasurable laneX laneEps depthFactor rarePerLaneScale _ _ _ _ _ hcollarBase
        hcollarHeadNonneg hcollarHeadMeasurable hcollarHead hcollarBand hcollarDeep
          hcollarAfterNonneg hcollarAfterMeasurable hcollarAfter _ hcollarWaveNonneg
            hcollarWaveMeasurable hcollarWave _ _ hwaveBoundedNonneg hwaveBoundedMeasurable
              hwaveRareNonneg hwaveRareMeasurable hrarePerLaneScalePos hheadRareFull hbandRareFull
                hdeepRareFull hafterRareFull hwaveBoundedFull hwaveRareFull hcollarBaseNonneg
                  hcollarBaseMeasurable hcollarBandNonneg hcollarBandMeasurable hcollarDeepNonneg
                    hcollarDeepMeasurable rareLane Uexp
  have hrareLaneNonneg : ∀ i, ∀ omega, 0 ≤ rareLane i omega := by
    simp only [rareLane, Fin.forall_fin_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
    exact ⟨hheadRareNonneg, hbandRareNonneg, hdeepRareNonneg,
      hafterRareNonneg, hwaveBoundedNonneg, hwaveRareNonneg,
      hcollarBaseNonneg, hcollarHeadNonneg, hcollarBandNonneg,
      hcollarDeepNonneg, hcollarAfterNonneg, hcollarWaveNonneg⟩
  have hrareLaneMeasurable : ∀ i, Measurable (rareLane i) := by
    simp only [rareLane, Fin.forall_fin_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
    exact ⟨hheadRareMeasurable, hbandRareMeasurable, hdeepRareMeasurable,
      hafterRareMeasurable, hwaveBoundedMeasurable, hwaveRareMeasurable,
      hcollarBaseMeasurable, hcollarHeadMeasurable, hcollarBandMeasurable,
      hcollarDeepMeasurable, hcollarAfterMeasurable, hcollarWaveMeasurable⟩
  have hrareLaneWith : ∀ i,
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        (rareLane i) rarePerLaneScale := by
    simp only [rareLane, Fin.forall_fin_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
    refine ⟨hheadRareFull, hbandRareFull, hdeepRareFull, hafterRareFull,
      hwaveBoundedFull, hwaveRareFull, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarBase
    · simpa only [rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarHead
    · simpa only [rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarBand
    · simpa only [rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarDeep
    · simpa only [rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarAfter
    · simpa only [rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarWave
  have htargetSigmaPos : 0 < (1 - sigma) / 3 := by linarith
  have hrareLaneO : ∀ i ∈ (Finset.univ : Finset (Fin 12)),
      HCPolySupport.IndependentSums.IsBigO
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        (rareLane i) rarePerLaneScale := by
    intro i _
    exact (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (hrareLaneNonneg i)).1 (hrareLaneWith i)
  have hrareSymmetric :=
    HCPolySupport.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (Finset.univ : Finset (Fin 12)) htargetSigmaPos
      ⟨0, Finset.mem_univ 0⟩
      (fun _ _ => hrarePerLaneScalePos) hrareLaneO
      (fun i _ => hrareLaneMeasurable i)
  have hUexpNonneg : ∀ omega, 0 ≤ Uexp omega := by
    intro omega
    exact Finset.sum_nonneg fun i _ => hrareLaneNonneg i omega
  have hUexpMeasurable : Measurable Uexp := by
    exact Finset.measurable_fun_sum Finset.univ fun i _ =>
      hrareLaneMeasurable i
  have hUexpRaw :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        Uexp
        (HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) *
          ∑ _i : Fin 12, rarePerLaneScale) := by
    apply (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      hUexpNonneg).2
    simpa only [Uexp] using hrareSymmetric
  exact ⟨hrareLaneNonneg, hUexpNonneg, hUexpMeasurable, hUexpRaw⟩

private theorem superposedFluxUpperPerDescendant_momentBounds3 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E }) (sigma Clane : ℝ) (k : ℕ)
      (R : TriadicCube d) (_ : (2 : ℕ) ≤ d) (headRare : Cutoff.CutoffSample d → ℝ) (headRareScale
        : ℝ)
      (_ :
        IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
          (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) headRare headRareScale)
      (_ : headRareScale ≤ Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))
      (bandRare : Cutoff.CutoffSample d → ℝ) (bandRareScale : ℝ)
      (_ :
        IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
          (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) bandRare bandRareScale)
      (_ : bandRareScale ≤ Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))
      (deepRare : Cutoff.CutoffSample d → ℝ) (deepRareScale : ℝ)
      (_ :
        IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
          (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) deepRare deepRareScale)
      (_ : deepRareScale ≤ Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))
      (afterRare : Cutoff.CutoffSample d → ℝ) (afterRareScale : ℝ)
      (_ :
        IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
          (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) afterRare afterRareScale)
      (_ :
        afterRareScale ≤
          (3 : ℝ) ^ (M.gamma * (↑(k + (1 : ℕ)) : ℝ)) *
            Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)),
      let laneX : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let laneEps : ℝ := Real.exp (-(Clane⁻¹ * laneX));
      let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ)));
      let rarePerLaneScale : ℝ := depthFactor * laneEps ^ (8 : ℕ);
      let collarBase : Cutoff.CutoffSample d → ℝ :=
        probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ));
      let collarBand : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarBandMeanTunedTraceLane M
        m R (↑E : ℝ);
      let collarDeep : Cutoff.CutoffSample d → ℝ := probeSharpFramedCollarDeepTailTraceLane M m R
        (↑E : ℝ);
      ∀ (waveBounded waveRare : Cutoff.CutoffSample d → ℝ)
        (_ :
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) waveBounded
            (probeSharpWaveTailTunedTraceScale M (↑E : ℝ) sigma))
        (_ :
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
            (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) waveRare
            (probeSharpWaveTailTunedTraceScale M (↑E : ℝ) sigma))
        (_ :
          probeSharpWaveTailTunedTraceScale M (↑E : ℝ) sigma ≤
            Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)),
        (0 : ℝ) < rarePerLaneScale ∧
          IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
              (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) headRare rarePerLaneScale ∧
            IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
              d))
                (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) bandRare
                  rarePerLaneScale ∧
              IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                (Cutoff.CutoffSample d))
                  (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) deepRare
                    rarePerLaneScale ∧
                IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                  (Cutoff.CutoffSample d))
                    (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) afterRare
                      rarePerLaneScale ∧
                  IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                    (Cutoff.CutoffSample d))
                      (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) waveBounded
                        rarePerLaneScale ∧
                    IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                      (Cutoff.CutoffSample d))
                        (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) waveRare
                          rarePerLaneScale ∧
                      (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarBase omega) ∧
                        Measurable collarBase ∧
                          (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarBand omega) ∧
                            Measurable collarBand ∧
                              (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ collarDeep omega) ∧
                                Measurable collarDeep := by
  intro _ M m E sigma _ _ R hd _ _ hheadRareO hheadRareScaleLe _ _ hbandRareO hbandRareScaleLe _ _
    hdeepRareO hdeepRareScaleLe afterRare _ hafterRareO hafterRareScaleLe _ laneEps depthFactor
      rarePerLaneScale collarBase collarBand collarDeep _ _ hwaveBoundedO hwaveRareO hwaveScaleLe
  have hdepthFactorPos : 0 < depthFactor := by
    dsimp only [depthFactor]
    positivity
  have hdepthFactorOne : 1 ≤ depthFactor := by
    dsimp only [depthFactor]
    exact Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have hlaneEpsPos : 0 < laneEps := by
    dsimp only [laneEps]
    positivity
  have hrarePerLaneScalePos : 0 < rarePerLaneScale :=
    mul_pos hdepthFactorPos (pow_pos hlaneEpsPos 8)
  have hlaneEpsEightLe : laneEps ^ 8 ≤ rarePerLaneScale := by
    dsimp only [rarePerLaneScale]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      hdepthFactorOne (pow_nonneg hlaneEpsPos.le 8)
  have hheadRareFull :=
    hheadRareO.mono_scale (hheadRareScaleLe.trans hlaneEpsEightLe)
  have hbandRareFull :=
    hbandRareO.mono_scale (hbandRareScaleLe.trans hlaneEpsEightLe)
  have hdeepRareFull :=
    hdeepRareO.mono_scale (hdeepRareScaleLe.trans hlaneEpsEightLe)
  have hafterRareFull :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        afterRare rarePerLaneScale := by
    exact hafterRareO.mono_scale (hafterRareScaleLe.trans (by
      simpa only [rarePerLaneScale, depthFactor, laneEps,
        Nat.cast_add, Nat.cast_one] using le_rfl))
  have hwaveBoundedFull :=
    hwaveBoundedO.mono_scale (hwaveScaleLe.trans hlaneEpsEightLe)
  have hwaveRareFull :=
    hwaveRareO.mono_scale (hwaveScaleLe.trans hlaneEpsEightLe)
  have hcollarBaseNonneg : ∀ omega, 0 ≤ collarBase omega := by
    intro omega
    simpa only [collarBase] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseTraceLane_nonneg
        hd M R (E : ℝ)
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) omega
  have hcollarBaseMeasurable : Measurable collarBase := by
    simpa only [collarBase] using
      measurable_probeSharpFramedCollarBaseTraceLane
        M R (E : ℝ)
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ))
  have hcollarBandNonneg : ∀ omega, 0 ≤ collarBand omega := by
    intro omega
    simpa only [collarBand] using
      probeSharpFramedCollarBandMeanTunedTraceLane_nonneg
        hd M m R (E : ℝ) omega
  have hcollarBandMeasurable : Measurable collarBand := by
    simpa only [collarBand] using
      measurable_probeSharpFramedCollarBandMeanTunedTraceLane
        M m R (E : ℝ)
  have hcollarDeepNonneg : ∀ omega, 0 ≤ collarDeep omega := by
    intro omega
    simpa only [collarDeep] using
      probeSharpFramedCollarDeepTailTraceLane_nonneg
        M m R (E : ℝ) omega
  have hcollarDeepMeasurable : Measurable collarDeep := by
    simpa only [collarDeep] using
      measurable_probeSharpFramedCollarDeepTailTraceLane
        M m R (E : ℝ)
  exact ⟨hrarePerLaneScalePos, hheadRareFull, hbandRareFull, hdeepRareFull, hafterRareFull,
    hwaveBoundedFull, hwaveRareFull, hcollarBaseNonneg, hcollarBaseMeasurable, hcollarBandNonneg,
      hcollarBandMeasurable, hcollarDeepNonneg, hcollarDeepMeasurable⟩

private theorem superposedFluxUpperPerDescendant_comparisonBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E })
      (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (sigma Clane : ℝ) (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Clane / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : probeSharpCollarBaseTunedOutputConst d ≤ Clane)
      (k : ℕ) (R : TriadicCube d) (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k
        : ℤ))),
      let laneX : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let _ : ℝ := Real.exp (-(Clane⁻¹ * laneX));
      IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
        (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
        (probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)))
        ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) * Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ)
          * M.gamma⁻¹))) ^ (8 : ℕ)) := by
  classical
  intro d M m E hstate _ _ hsigma0 hsigmaHalf hmaxLane hE2 hcollarBaseOutput k R hR _ laneEps
  let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1))
  let rarePerLaneScale : ℝ := depthFactor * laneEps ^ 8
  let collarBase : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseTraceLane
      M R (E : ℝ)
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ))
  let collarHead : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ j : Fin d, ∑' n : ℕ,
      Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n (m - 1) (basisVec j)
        (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
        (fun eta => Algsuperdiff.Section3.Provider.Multiscale.waveHeadTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
            R.scale
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n) eta ^ 2)
        (Algsuperdiff.Section3.Cutoff.translateCutoffSample
          (triadicCubeShift R) omega)
  let collarBand : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceLane
      M m R (E : ℝ)
  let collarDeep : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailTraceLane
      M m R (E : ℝ)
  let collarAfter : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarAfterBandTraceLane
      M m R (E : ℝ)
  have hcollarBase :=
    isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseTraceLane_tuned
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarBaseOutput
  exact hcollarBase

private theorem superposedFluxUpperPerDescendant_comparisonBounds2 :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (E : { E : ℝ // (1 : ℝ) ≤ E })
      (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) (sigma Clane : ℝ) (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Clane / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : probeSharpCollarBaseTunedOutputConst d ≤ Clane)
      (_ : collarHeadTunedPerDescendantOutputConst d ≤ Clane) (k : ℕ) (R : TriadicCube d)
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))),
      (have laneX : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
        have _ : ℝ := Real.exp (-(Clane⁻¹ * laneX));
        IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
          (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ)))
          (probeSharpFramedCollarBaseTraceLane M R (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)))
          ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
            Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ))) ∧
        have trace : (omega : Cutoff.CutoffSample d) → ℝ := fun (omega : Cutoff.CutoffSample d) =>
          ∑ j : Fin d,
            ∑' (n : ℕ),
              Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                (collarBandMeanDepth M (↑E : ℝ)) n
                (m - (1 : ℤ)) (basisVec j) (Affine.superposedGradConst d)
                (fun (eta : Cutoff.CutoffSample d) =>
                  Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                      (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ))
                        n) eta ^
                    (2 : ℕ))
                (Cutoff.translateCutoffSample (triadicCubeShift R) omega);
        (∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ trace omega) ∧
          Measurable trace ∧
            (∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
              (Cutoff.CutoffSample d)),
                ENNReal.ofReal (trace omega) =
                  ∑ j : Fin d,
                    ∑' (n : ℕ),
                      ENNReal.ofReal
                        (Multiscale.probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB
                          (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
                            (Affine.superposedGradConst d)
                          (fun (eta : Cutoff.CutoffSample d) =>
                            Multiscale.waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
                                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M
                                  (↑E : ℝ)) n) eta ^
                              (2 : ℕ))
                          (Cutoff.translateCutoffSample (triadicCubeShift R) omega))) ∧
              IndependentSums.IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure
                (Cutoff.CutoffSample d))
                (IndependentSums.gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) trace
                ((3 : ℝ) ^ (M.gamma * ((↑k : ℝ) + (1 : ℝ))) *
                  Real.exp (-(Clane⁻¹ * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹))) ^ (8 : ℕ)) := by
  classical
  intro d M m E hstate sigma Clane hsigma0 hsigmaHalf hmaxLane hE2 hcollarBaseOutput
    hcollarHeadOutput k R hR
  let laneX : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let laneEps : ℝ := Real.exp (-(Clane⁻¹ * laneX))
  have hcollarBase :=
    @superposedFluxUpperPerDescendant_comparisonBounds1 (d) (M) (m) (E) (hstate) (sigma) (Clane)
      (hsigma0) (hsigmaHalf) (hmaxLane) (hE2) (hcollarBaseOutput) (k) (R) (hR)
  let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1))
  let rarePerLaneScale : ℝ := depthFactor * laneEps ^ 8
  let collarBase : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseTraceLane
      M R (E : ℝ)
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ))
  let collarHead : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ j : Fin d, ∑' n : ℕ,
      Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n (m - 1) (basisVec j)
        (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
        (fun eta => Algsuperdiff.Section3.Provider.Multiscale.waveHeadTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
            R.scale
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n) eta ^ 2)
        (Algsuperdiff.Section3.Cutoff.translateCutoffSample
          (triadicCubeShift R) omega)
  let collarBand : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceLane
      M m R (E : ℝ)
  let collarDeep : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailTraceLane
      M m R (E : ℝ)
  let collarAfter : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarAfterBandTraceLane
      M m R (E : ℝ)
  have hcollarHead :=
    collar_head_tuned_trace_is_big_o_with_eighth_power
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarHeadOutput
  exact ⟨hcollarBase, hcollarHead⟩

private theorem superposedFlux_descendant_measurable :
    ∀ {d : ℕ} (M : ABKModel d) (m : ℤ) (_ : { E : ℝ // (1 : ℝ) ≤ E })
      (R : TriadicCube d) (_ : (2 : ℕ) ≤ d),
      let _ : NeZero d := { out := fun (_ : d = (0 : ℕ)) => (by omega) };
      Measurable fun (omega : Cutoff.CutoffSample d) =>
        cutoffBBlockFamily M m (↑(Annealed.sigmaBar M (m - (1 : ℤ))) : ℝ)⁻¹ R omega := by
  intro d M m _ R _ _
  have hraw : Measurable (fun omega : Cutoff.CutoffSample d =>
      HCPolySupport.Book.Ch02.matrixNorm
        (HCPolySupport.coarseBlockMatrix (cubeSet R)
          (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft) :=
    Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseBMatrixNorm
      (Cutoff.measurable_coefficientCutoff M.nu m)
      (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m) R
  have hcoreEq :
      (fun omega : Cutoff.CutoffSample d =>
        Algsuperdiff.Section3.Provider.CoarseEllipticity.coarseBNormCoeffField R
          (Cutoff.coefficientCutoff M.nu m omega)) =
      (fun omega : Cutoff.CutoffSample d =>
        HCPolySupport.Book.Ch02.matrixNorm
          (HCPolySupport.coarseBlockMatrix (cubeSet R)
            (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft) := by
    funext omega
    rw [Algsuperdiff.Section3.Provider.CoarseEllipticity.coarseBNormCoeffField,
      dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)]
    have hbridge := congrArg
      (fun A : BlockMat d => HCPolySupport.Book.Ch02.matrixNorm A.upperLeft)
      (HCPolySupport.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega) R)
    simpa only [HCPolySupport.Book.Ch02.coarseBMatrixNorm,
      HCPolySupport.Book.Ch02.coarseBlockMatrix_upperLeft] using hbridge.symm
  have hcore : Measurable (fun omega : Cutoff.CutoffSample d =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.coarseBNormCoeffField R
        (Cutoff.coefficientCutoff M.nu m omega)) := by
    rw [hcoreEq]
    exact hraw
  simpa only
    [Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily] using!
      (measurable_const.mul hcore)

private theorem superposedFluxUpperPerDescendant_comparisonBounds3 :
  superposedFluxUpperPerDescendant_comparisonBounds3_statement := by
  classical
  intro d M m E hstate sigma Clane hsigma0 hsigmaHalf hmaxLane hE2 hgoodHeadOutput hgoodBandOutput
    hgoodDeepOutput hgoodAfterOutput hcollarBaseOutput hcollarHeadOutput hprofileAuxLane hk0 k R hR
  have hmaxAux :
      max (Real.exp
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.profileAuxiliaryConst d /
          sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmaxLane)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 hprofileAuxLane)).trans
        ((le_max_left _ _).trans hmaxLane)
  have hpotential : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          ENNReal.ofReal
              (Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
                M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega) ≤
            ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
              (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedMeanLayerEnvelope
                M R.scale (E : ℝ)
                  Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
                  (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
                    M (E : ℝ)) n (m - 1) m
                  (Algsuperdiff.Section3.Cutoff.translateCutoffSample
                    (triadicCubeShift R) omega)
                  (basisVec j)
                  (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)) := by
    intro k R hR
    exact
      Multiscale.descendant_cutoffBlock_le_meanEnvelope_ae_of_profileGate
        M hR hstate hsigma0 hsigmaHalf hmaxAux hE2 hk0 (by omega)
  obtain ⟨headOrdinary, headRare, headOrdinaryScale, headRareScale,
      hhead⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_good_head_tuned_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodHeadOutput
  rcases hhead with
    ⟨hheadOrdinaryNonneg, hheadOrdinaryMeasurable,
      hheadRareNonneg, hheadRareMeasurable, _,
      _, hheadENNRealDom, hheadOrdinaryO,
      _, hheadOrdinaryScaleLe,
      hheadRareO, _, hheadRareScaleLe⟩
  obtain ⟨bandOrdinary, bandRare, bandRareScale, hband⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_good_band_mean_tuned_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodBandOutput
  rcases hband with
    ⟨hbandOrdinaryNonneg, hbandOrdinaryMeasurable,
      hbandRareNonneg, hbandRareMeasurable, _,
      _, hbandENNRealDom, hbandOrdinaryLe,
      hbandRareO, _, hbandRareScaleLe⟩
  obtain ⟨deepOrdinary, deepRare, deepOrdinaryScale, deepRareScale,
      hdeep⟩ :=
    exists_tunedDeepBandTail_good_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
        (max_le hprofileAuxLane hgoodDeepOutput)
  rcases hdeep with
    ⟨hdeepOrdinaryNonneg, hdeepOrdinaryMeasurable,
      hdeepRareNonneg, hdeepRareMeasurable, _,
      _, hdeepENNRealDom,
      hdeepOrdinaryO, _, hdeepOrdinaryScaleLe,
      hdeepRareO, _, hdeepRareScaleLe⟩
  obtain ⟨afterOrdinary, afterRare, afterOrdinaryScale, afterRareScale,
      hafter⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_tunedAfterBand_good_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodAfterOutput
  rcases hafter with
    ⟨hafterOrdinaryNonneg, hafterOrdinaryMeasurable,
      hafterRareNonneg, hafterRareMeasurable, _,
      _, hafterENNRealDom, hafterOrdinaryO,
      _, hafterOrdinaryScaleLe,
      hafterRareO, _, hafterRareScaleLe⟩
  obtain ⟨hcollarBase, hcollarHead⟩ :=
    @superposedFluxUpperPerDescendant_comparisonBounds2 (d) (M) (m) (E) (hstate) (sigma) (Clane)
      (hsigma0) (hsigmaHalf) (hmaxLane) (hE2) (hcollarBaseOutput) (hcollarHeadOutput) (k) (R) (hR)
  let laneX : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let laneEps : ℝ := Real.exp (-(Clane⁻¹ * laneX))
  let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1))
  let rarePerLaneScale : ℝ := depthFactor * laneEps ^ 8
  let collarBase : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseTraceLane
      M R (E : ℝ)
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ))
  let collarHead : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ j : Fin d, ∑' n : ℕ,
      Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n (m - 1) (basisVec j)
        (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
        (fun eta => Algsuperdiff.Section3.Provider.Multiscale.waveHeadTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
            R.scale
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n) eta ^ 2)
        (Algsuperdiff.Section3.Cutoff.translateCutoffSample
          (triadicCubeShift R) omega)
  let collarBand : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceLane
      M m R (E : ℝ)
  let collarDeep : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailTraceLane
      M m R (E : ℝ)
  let collarAfter : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarAfterBandTraceLane
      M m R (E : ℝ)
  rcases hcollarHead with
    ⟨hcollarHeadNonneg, hcollarHeadMeasurable,
      hcollarHeadENNRealEq, hcollarHead⟩
  exact ⟨hpotential, headOrdinary, headRare, headOrdinaryScale, headRareScale,
    hheadOrdinaryNonneg, hheadOrdinaryMeasurable, hheadRareNonneg, hheadRareMeasurable,
      hheadENNRealDom, hheadOrdinaryO, hheadOrdinaryScaleLe, hheadRareO, hheadRareScaleLe,
        bandOrdinary, bandRare, bandRareScale, hbandOrdinaryNonneg, hbandRareNonneg,
          hbandRareMeasurable, hbandENNRealDom, hbandOrdinaryLe, hbandRareO, hbandRareScaleLe,
            deepOrdinary, deepRare, deepOrdinaryScale, deepRareScale, hdeepOrdinaryNonneg,
              hdeepOrdinaryMeasurable, hdeepRareNonneg, hdeepRareMeasurable, hdeepENNRealDom,
                hdeepOrdinaryO, hdeepOrdinaryScaleLe, hdeepRareO, hdeepRareScaleLe, afterOrdinary,
                  afterRare, afterOrdinaryScale, afterRareScale, hafterOrdinaryNonneg,
                    hafterOrdinaryMeasurable, hafterRareNonneg, hafterRareMeasurable,
                      hafterENNRealDom, hafterOrdinaryO, hafterOrdinaryScaleLe, hafterRareO,
                        hafterRareScaleLe, hcollarBase, hcollarHeadNonneg, hcollarHeadMeasurable,
                          hcollarHeadENNRealEq, hcollarHead, True.intro⟩

private theorem superposedFluxUpperPerDescendant_comparisonBounds4 :
  superposedFluxUpperPerDescendant_comparisonBounds4_statement := by
  classical
  intro d M m E hstate sigma Clane hsigma0 hsigmaHalf hmaxLane hE2 hlanePos hgoodWaveOutput
    hprofileAuxLane hdepthThresholdLane k R hR hd headOrdinary headRare headOrdinaryScale
      headRareScale hheadOrdinaryNonneg hheadOrdinaryMeasurable hheadRareNonneg
        hheadRareMeasurable hheadOrdinaryO hheadOrdinaryScaleLe hheadRareO hheadRareScaleLe
          bandRare bandRareScale hbandRareNonneg hbandRareMeasurable hbandRareO hbandRareScaleLe
            deepOrdinary deepRare deepOrdinaryScale deepRareScale hdeepOrdinaryNonneg
              hdeepOrdinaryMeasurable hdeepRareNonneg hdeepRareMeasurable hdeepOrdinaryO
                hdeepOrdinaryScaleLe hdeepRareO hdeepRareScaleLe afterOrdinary afterRare
                  afterOrdinaryScale afterRareScale hafterOrdinaryNonneg hafterOrdinaryMeasurable
                    hafterRareNonneg hafterRareMeasurable hafterOrdinaryO hafterOrdinaryScaleLe
                      hafterRareO hafterRareScaleLe hcollarBase hcollarHeadNonneg
                        hcollarHeadMeasurable hcollarHead collarBase collarHead collarBand
                          collarDeep collarAfter hcollarBand hcollarDeep hcollarAfterNonneg
                            hcollarAfterMeasurable hcollarAfter collarWave hcollarWaveRaw
  rcases hcollarWaveRaw with
    ⟨hcollarWaveNonneg, hcollarWaveMeasurable,
      hcollarWaveENNRealEq, hcollarWave⟩
  obtain ⟨waveBounded, waveRare, hwave⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_good_wave_tail_tuned_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodWaveOutput
  rcases hwave with
    ⟨hwaveBoundedNonneg, hwaveBoundedMeasurable,
      hwaveRareNonneg, hwaveRareMeasurable, _,
      _, hwaveENNRealDom,
      hwaveBoundedO, hwaveRareO, _, hwaveScaleLe⟩
  let perCubeScale : ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
      Clane (Disorder.cstar M) M.gamma k
  let ordinaryLane : Fin 3 → Cutoff.CutoffSample d → ℝ :=
    ![headOrdinary, deepOrdinary, afterOrdinary]
  let Uone : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ i : Fin 3, ordinaryLane i omega
  obtain ⟨hordinaryLaneNonneg, hUoneNonneg, hUoneMeasurable, hUone⟩ :=
    @superposedFlux_ordinaryContribution (d) (M) (sigma) (Clane) (hsigma0) (hsigmaHalf) (hlanePos)
      (k) (headOrdinary) (headOrdinaryScale) (hheadOrdinaryNonneg) (hheadOrdinaryMeasurable)
        (hheadOrdinaryO) (hheadOrdinaryScaleLe) (deepOrdinary) (deepOrdinaryScale)
          (hdeepOrdinaryNonneg) (hdeepOrdinaryMeasurable) (hdeepOrdinaryO) (hdeepOrdinaryScaleLe)
            (afterOrdinary) (afterOrdinaryScale) (hafterOrdinaryNonneg) (hafterOrdinaryMeasurable)
              (hafterOrdinaryO) (hafterOrdinaryScaleLe)
  obtain ⟨hrarePerLaneScalePos, hheadRareFull, hbandRareFull, hdeepRareFull, hafterRareFull,
    hwaveBoundedFull, hwaveRareFull, hcollarBaseNonneg, hcollarBaseMeasurable, hcollarBandNonneg,
      hcollarBandMeasurable, hcollarDeepNonneg, hcollarDeepMeasurable⟩ :=
    @superposedFluxUpperPerDescendant_momentBounds3 (d) (M) (m) (E) (sigma) (Clane) (k) (R) (hd)
      (headRare) (headRareScale) (hheadRareO) (hheadRareScaleLe) (bandRare) (bandRareScale)
        (hbandRareO) (hbandRareScaleLe) (deepRare) (deepRareScale) (hdeepRareO) (hdeepRareScaleLe)
          (afterRare) (afterRareScale) (hafterRareO) (hafterRareScaleLe) (waveBounded) (waveRare)
            (hwaveBoundedO) (hwaveRareO) (hwaveScaleLe)
  let rareLane : Fin 12 → Cutoff.CutoffSample d → ℝ :=
    ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare,
      collarBase, collarHead, collarBand, collarDeep, collarAfter, collarWave]
  let Uexp : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ i : Fin 12, rareLane i omega
  obtain ⟨hrareLaneNonneg, hUexpNonneg, hUexpMeasurable, hUexpRaw⟩ :=
    @superposedFluxUpperPerDescendant_momentBounds2 (d) (M) (m) (E) (sigma) (Clane) (hsigma0)
      (hsigmaHalf) (k) (R) (headRare) (hheadRareNonneg) (hheadRareMeasurable) (bandRare)
        (hbandRareNonneg) (hbandRareMeasurable) (deepRare) (hdeepRareNonneg) (hdeepRareMeasurable)
          (afterRare) (hafterRareNonneg) (hafterRareMeasurable) (hcollarBase) (hcollarHeadNonneg)
            (hcollarHeadMeasurable) (hcollarHead) (hcollarBand) (hcollarDeep) (hcollarAfterNonneg)
              (hcollarAfterMeasurable) (hcollarAfter) (hcollarWaveNonneg) (hcollarWaveMeasurable)
                (hcollarWave) (waveBounded) (waveRare) (hwaveBoundedNonneg)
                  (hwaveBoundedMeasurable) (hwaveRareNonneg) (hwaveRareMeasurable)
                    (hrarePerLaneScalePos) (hheadRareFull) (hbandRareFull) (hdeepRareFull)
                      (hafterRareFull) (hwaveBoundedFull) (hwaveRareFull) (hcollarBaseNonneg)
                        (hcollarBaseMeasurable) (hcollarBandNonneg) (hcollarBandMeasurable)
                          (hcollarDeepNonneg) (hcollarDeepMeasurable)
  let K : ℝ := 12 *
    Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst
  have htriangleBarNonneg : 0 ≤
      Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst := by
    rw [Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst]
    positivity
  have hKNonneg : 0 ≤ K := by
    dsimp only [K]
    positivity
  obtain ⟨hUexp, hgoodBaseENNReal, hcollarBaseENNReal, hcollarBandENNReal, hcollarDeepENNReal⟩ :=
    @superposedFluxUpperPerDescendant_momentBounds1 (d) (M) (m) (E) (hstate) (sigma) (Clane)
      (hsigma0) (hsigmaHalf) (hmaxLane) (hE2) (hprofileAuxLane) (hdepthThresholdLane) (k) (R) (hR)
        (hd) (headRare) (bandRare) (deepRare) (afterRare) (waveBounded) (waveRare)
          (hrarePerLaneScalePos) (hUexpRaw)
  have hEnvelope (omega : Cutoff.CutoffSample d) :=
    Finset.sum_le_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin d))) =>
      ENNReal.tsum_le_tsum fun n =>
        named_layer_ennreal_bound M m (E : ℝ) R j n omega
  exact ⟨hcollarWaveENNRealEq, waveBounded, waveRare, hwaveENNRealDom, hordinaryLaneNonneg,
    hUoneNonneg, hUoneMeasurable, hUone, hrareLaneNonneg, hUexpNonneg, hUexpMeasurable, hUexp,
      hgoodBaseENNReal, hcollarBaseENNReal, hcollarBandENNReal, hcollarDeepENNReal, hEnvelope,
        True.intro⟩

private theorem superposedFluxUpperPerDescendant_comparisonBounds5 :
  superposedFluxUpperPerDescendant_comparisonBounds5_statement := by
  classical
  intro d M m E _ Cblock k R hR hd hpotential headOrdinary headRare hheadENNRealDom _ bandRare
    hbandENNRealDom deepOrdinary deepRare hdeepENNRealDom afterOrdinary afterRare hafterENNRealDom
      hcollarHeadENNRealEq collarBase collarHead collarBand collarDeep collarAfter
        hcollarAfterENNRealEq collarWave hcollarWaveENNRealEq waveBounded waveRare hwaveENNRealDom
          hordinaryLaneNonneg hUoneNonneg hrareLaneNonneg hUexpNonneg hgoodBaseENNReal
            hcollarBaseENNReal ordinaryLane Uone rareLane Uexp hEnvelope hdetENNReal hCblockNonneg
              hcollarBandRaw hcollarDeepRaw
  have hUoneOfReal (omega : Cutoff.CutoffSample d) :
      ENNReal.ofReal (Uone omega) =
        ∑ i : Fin 3, ![ENNReal.ofReal (headOrdinary omega),
          ENNReal.ofReal (deepOrdinary omega), ENNReal.ofReal (afterOrdinary omega)] i := by
    change ENNReal.ofReal (∑ i : Fin 3, ordinaryLane i omega) = _
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hordinaryLaneNonneg i omega)]
    rfl
  have hUexpOfReal (omega : Cutoff.CutoffSample d) :
      ENNReal.ofReal (Uexp omega) =
        ∑ i : Fin 12, ![ENNReal.ofReal (headRare omega), ENNReal.ofReal (bandRare omega),
          ENNReal.ofReal (deepRare omega), ENNReal.ofReal (afterRare omega),
          ENNReal.ofReal (waveBounded omega), ENNReal.ofReal (waveRare omega),
          ENNReal.ofReal (collarBase omega), ENNReal.ofReal (collarHead omega),
          ENNReal.ofReal (collarBand omega), ENNReal.ofReal (collarDeep omega),
          ENNReal.ofReal (collarAfter omega), ENNReal.ofReal (collarWave omega)] i := by
    change ENNReal.ofReal (∑ i : Fin 12, rareLane i omega) = _
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hrareLaneNonneg i omega)]
    rfl
  have hae : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
          M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega ≤
        Cblock + Uone omega + Uexp omega := by
    exact ae_twelve_lane_domination
      (Cutoff.cutoffSampleLaw M).toMeasure hCblockNonneg hUoneNonneg hUexpNonneg
      (hpotential k R hR) hEnvelope (fun _ => hgoodBaseENNReal)
      hheadENNRealDom hbandENNRealDom hdeepENNRealDom hafterENNRealDom hwaveENNRealDom
      hcollarBaseENNReal hcollarHeadENNRealEq hcollarBandRaw hcollarDeepRaw
      hcollarAfterENNRealEq hcollarWaveENNRealEq hdetENNReal hUoneOfReal hUexpOfReal
  have hblockMeas : Measurable (fun omega : Cutoff.CutoffSample d =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
        M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega)  := @superposedFlux_descendant_measurable
          (d) (M) (m) (E) (R) (hd)
  exact ⟨hae, hblockMeas⟩

/-- Constructs the pointwise deterministic, ordinary, and exceptional split for every
single descendant cube. The exceptional scale is left in its raw twelve-lane form for
the upper-leg aggregation layer to normalize. -/
theorem superposedFlux_upper_per_descendant_split
    {d : ℕ}
    (M : ABKModel d) (m : ℤ)
    (E : {E : ℝ // 1 ≤ E})
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    (sigma Clane : ℝ)
    (hsigma0 : 0 < sigma)
    (hsigmaHalf : sigma ≤ 1 / 2)
    (hmaxLane : max (Real.exp (Clane / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hE2 : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hlanePos : 0 < Clane)
    (hgoodBaseOutput :
      Multiscale.probeSharpGoodBaseConst d ≤ Clane)
    (hgoodHeadOutput :
      goodHeadTunedOutputConst d ≤ Clane)
    (hgoodBandOutput :
      probeSharpBandMeanTunedOutputConst d ≤ Clane)
    (hgoodDeepOutput :
      probeSharpDeepBandTailTunedOutputConst d ≤
        Clane)
    (hgoodAfterOutput :
      probeSharpAfterBandTunedOutputConst d ≤
        Clane)
    (hgoodWaveOutput :
      probeSharpWaveTailTunedOutputConst d ≤ Clane)
    (hcollarBaseOutput :
      probeSharpCollarBaseTunedOutputConst d ≤
        Clane)
    (hcollarHeadOutput :
      collarHeadTunedPerDescendantOutputConst d ≤
        Clane)
    (hcollarBandOutput :
      collarBandMeanTunedOutputConst d ≤ Clane)
    (hcollarDeepOutput :
      collarDeepTailTunedOutputConst d ≤ Clane)
    (hcollarAfterOutput :
      collarAfterBandTunedOutputConst d ≤ Clane)
    (hcollarWaveOutput :
      probeSharpCollarWaveTailTunedOutputConst d
        ≤ Clane)
    (hprofileAuxLane :
      profileAuxiliaryConst d ≤ Clane)
    (hdepthThresholdLane :
      collarBandMeanDepthThreshold d ≤ Clane)
    (hk0 : 3 ≤
      collarBandMeanDepth
        M (E : ℝ)) :
    let Cblock : ℝ :=
      (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) * Clane
    ∀ (k : ℕ) (R : TriadicCube d),
              R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
                ∃ Uone Uexp : Cutoff.CutoffSample d → ℝ,
                  (∀ omega, 0 ≤ Uone omega) ∧
                  Measurable Uone ∧
                  (∀ omega, 0 ≤ Uexp omega) ∧
                  Measurable Uexp ∧
                  (∀ omega,
                      cutoffBBlockFamily
                          M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega ≤
                      Cblock + Uone omega + Uexp omega) ∧
                  HCPolySupport.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (HCPolySupport.IndependentSums.gammaSigma 1) Uone
                    (upperSaturatedPerCubeAmplitude
                      Cblock (Disorder.cstar M) M.gamma k) ∧
                  HCPolySupport.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3)) Uexp
                    ((12 *
                        upperAfterBandRareTriangleConst) *
                      ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
                        (Real.exp
                          (-(Clane⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8)) := by
  let Cblock : ℝ :=
    (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) * Clane
  dsimp only
  intro k R hR
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hpotential, headOrdinary, headRare, headOrdinaryScale, headRareScale,
    hheadOrdinaryNonneg, hheadOrdinaryMeasurable, hheadRareNonneg, hheadRareMeasurable,
      hheadENNRealDom, hheadOrdinaryO, hheadOrdinaryScaleLe, hheadRareO, hheadRareScaleLe,
        bandOrdinary, bandRare, bandRareScale, hbandOrdinaryNonneg, hbandRareNonneg,
          hbandRareMeasurable, hbandENNRealDom, hbandOrdinaryLe, hbandRareO, hbandRareScaleLe,
            deepOrdinary, deepRare, deepOrdinaryScale, deepRareScale, hdeepOrdinaryNonneg,
              hdeepOrdinaryMeasurable, hdeepRareNonneg, hdeepRareMeasurable, hdeepENNRealDom,
                hdeepOrdinaryO, hdeepOrdinaryScaleLe, hdeepRareO, hdeepRareScaleLe, afterOrdinary,
                  afterRare, afterOrdinaryScale, afterRareScale, hafterOrdinaryNonneg,
                    hafterOrdinaryMeasurable, hafterRareNonneg, hafterRareMeasurable,
                      hafterENNRealDom, hafterOrdinaryO, hafterOrdinaryScaleLe, hafterRareO,
                        hafterRareScaleLe, hcollarBase, hcollarHeadNonneg, hcollarHeadMeasurable,
                          hcollarHeadENNRealEq, hcollarHead, _⟩ :=
    @superposedFluxUpperPerDescendant_comparisonBounds3 (d) (M) (m) (E) (hstate) (sigma) (Clane)
      (hsigma0) (hsigmaHalf) (hmaxLane) (hE2) (hgoodHeadOutput) (hgoodBandOutput)
        (hgoodDeepOutput) (hgoodAfterOutput) (hcollarBaseOutput) (hcollarHeadOutput)
          (hprofileAuxLane) (hk0) (k) (R) (hR)
  let laneX : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let laneEps : ℝ := Real.exp (-(Clane⁻¹ * laneX))
  let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1))
  let rarePerLaneScale : ℝ := depthFactor * laneEps ^ 8
  let collarBase : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseTraceLane
      M R (E : ℝ)
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ))
  let collarHead : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ j : Fin d, ∑' n : ℕ,
      Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n (m - 1) (basisVec j)
        (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
        (fun eta => Algsuperdiff.Section3.Provider.Multiscale.waveHeadTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
            R.scale
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n) eta ^ 2)
        (Algsuperdiff.Section3.Cutoff.translateCutoffSample
          (triadicCubeShift R) omega)
  let collarBand : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceLane
      M m R (E : ℝ)
  let collarDeep : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailTraceLane
      M m R (E : ℝ)
  let collarAfter : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarAfterBandTraceLane
      M m R (E : ℝ)
  have hcollarBand :=
    isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedTraceLane_frozenReserve
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
        (max_le hprofileAuxLane hcollarBandOutput)
  have hcollarDeep :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.collarDeepTail_trace_isBigOWith_frozenReserve
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarDeepOutput
  have hcollarAfter :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.collar_afterBand_trace_isBigOWith_frozenReserve
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
        (max_le hprofileAuxLane hcollarAfterOutput)
  rcases hcollarAfter with
    ⟨hcollarAfterNonneg, hcollarAfterMeasurable,
      hcollarAfterENNRealEq, hcollarAfter⟩
  let collarWave : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ j : Fin d, ∑' n : ℕ,
      Multiscale.probeSharpFramedCollarWavePart
        M R.scale (E : ℝ)
        bfaProfileB
        (collarBandMeanDepth
          M (E : ℝ)) n (m - 1) (basisVec j)
        (Affine.superposedGradConst d)
        (fun eta => Multiscale.waveTailTerm
          M R.scale (E : ℝ)
          bfaProfileB R.scale
          (probeSharpLayerAnchor
            R.scale
            bfaProfileB
            (collarBandMeanDepth
              M (E : ℝ)) n) eta ^ 2)
        (Cutoff.translateCutoffSample
          (triadicCubeShift R) omega)
  have hcollarWaveRaw :=
    isBigOWith_upperProfileTarget_collarWaveTailFiniteTrace
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarWaveOutput
  change (∀ omega, 0 ≤ collarWave omega) ∧ Measurable collarWave ∧ _ ∧ _ at hcollarWaveRaw
  obtain ⟨hcollarWaveENNRealEq, waveBounded, waveRare, hwaveENNRealDom, hordinaryLaneNonneg,
    hUoneNonneg, hUoneMeasurable, hUone, hrareLaneNonneg, hUexpNonneg, hUexpMeasurable, hUexp,
      hgoodBaseENNReal, hcollarBaseENNReal, hcollarBandENNReal, hcollarDeepENNReal, hEnvelope, _⟩ :=
    @superposedFluxUpperPerDescendant_comparisonBounds4 (d) (M) (m) (E) (hstate) (sigma) (Clane)
      (hsigma0) (hsigmaHalf) (hmaxLane) (hE2) (hlanePos) (hgoodWaveOutput) (hprofileAuxLane)
        (hdepthThresholdLane) (k) (R) (hR) (hd) (headOrdinary) (headRare) (headOrdinaryScale)
          (headRareScale) (hheadOrdinaryNonneg) (hheadOrdinaryMeasurable) (hheadRareNonneg)
            (hheadRareMeasurable) (hheadOrdinaryO) (hheadOrdinaryScaleLe) (hheadRareO)
              (hheadRareScaleLe) (bandRare) (bandRareScale) (hbandRareNonneg)
                (hbandRareMeasurable) (hbandRareO) (hbandRareScaleLe) (deepOrdinary) (deepRare)
                  (deepOrdinaryScale) (deepRareScale) (hdeepOrdinaryNonneg)
                    (hdeepOrdinaryMeasurable) (hdeepRareNonneg) (hdeepRareMeasurable)
                      (hdeepOrdinaryO) (hdeepOrdinaryScaleLe) (hdeepRareO) (hdeepRareScaleLe)
                        (afterOrdinary) (afterRare) (afterOrdinaryScale) (afterRareScale)
                          (hafterOrdinaryNonneg) (hafterOrdinaryMeasurable) (hafterRareNonneg)
                            (hafterRareMeasurable) (hafterOrdinaryO) (hafterOrdinaryScaleLe)
                              (hafterRareO) (hafterRareScaleLe) (hcollarBase) (hcollarHeadNonneg)
                                (hcollarHeadMeasurable) (hcollarHead) (hcollarBand) (hcollarDeep)
                                  (hcollarAfterNonneg) (hcollarAfterMeasurable) (hcollarAfter)
                                    (hcollarWaveRaw)
  let ordinaryLane : Fin 3 → Cutoff.CutoffSample d → ℝ :=
    ![headOrdinary, deepOrdinary, afterOrdinary]
  let Uone : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ i : Fin 3, ordinaryLane i omega
  let rareLane : Fin 12 → Cutoff.CutoffSample d → ℝ :=
    ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare,
      collarBase, collarHead, collarBand, collarDeep, collarAfter, collarWave]
  let Uexp : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ i : Fin 12, rareLane i omega
  let K : ℝ := 12 *
    upperAfterBandRareTriangleConst
  simp only [ENNReal.tsum_add, Finset.sum_add_distrib] at hEnvelope
  have hblockCoeff : (12 : ℝ) ≤
      12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1 :=
    le_add_of_nonneg_right (mul_nonneg (by norm_num)
      HCPolySupport.IndependentSums.gammaTriangleConst_pos.le)
  have htwoLane : Clane + Clane ≤ Cblock := by
    calc
      Clane + Clane = 2 * Clane := by ring
      _ ≤ 12 * Clane :=
        mul_le_mul_of_nonneg_right (by norm_num) hlanePos.le
      _ ≤ (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) *
          Clane := mul_le_mul_of_nonneg_right hblockCoeff hlanePos.le
      _ = Cblock := by rfl
  have hdetENNReal (omega : Cutoff.CutoffSample d) :
      ENNReal.ofReal
          (Multiscale.probeSharpGoodBaseConst d) +
        ENNReal.ofReal (bandOrdinary omega) ≤ ENNReal.ofReal Cblock := by
    rw [← ENNReal.ofReal_add
      (Multiscale.probeSharpGoodBaseConst_nonneg hd)
      (hbandOrdinaryNonneg omega)]
    apply ENNReal.ofReal_le_ofReal
    exact (add_le_add hgoodBaseOutput (hbandOrdinaryLe omega)).trans htwoLane
  have hCblockNonneg : 0 ≤ Cblock :=
    (add_nonneg hlanePos.le hlanePos.le).trans htwoLane
  have hcollarBandRaw (omega : Cutoff.CutoffSample d) := hcollarBandENNReal omega
  unfold
    probeSharpFramedCollarBandMeanTunedTraceENNRealLane
    probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane
    at hcollarBandRaw
  have hcollarDeepRaw := hcollarDeepENNReal
  unfold
    probeSharpFramedCollarDeepTailLayer
    at hcollarDeepRaw
  obtain ⟨hae, hblockMeas⟩ :=
    @superposedFluxUpperPerDescendant_comparisonBounds5 (d) (M) (m) (E) (Clane) (k) (R) (hR)
        (hd) (hpotential) (headOrdinary) (headRare) (hheadENNRealDom) (bandOrdinary) (bandRare)
          (hbandENNRealDom) (deepOrdinary) (deepRare) (hdeepENNRealDom) (afterOrdinary)
            (afterRare) (hafterENNRealDom) (hcollarHeadENNRealEq) (hcollarAfterENNRealEq)
              (hcollarWaveENNRealEq) (waveBounded) (waveRare) (hwaveENNRealDom)
                (hordinaryLaneNonneg) (hUoneNonneg) (hrareLaneNonneg) (hUexpNonneg)
                  (hgoodBaseENNReal) (hcollarBaseENNReal) (hEnvelope) (hdetENNReal)
                    (hCblockNonneg) (hcollarBandRaw) (hcollarDeepRaw)
  simpa only [K, rarePerLaneScale, depthFactor, laneEps, laneX] using
    (nonnegative_pointwise_repair hblockMeas hUoneNonneg
      hUoneMeasurable hUexpNonneg hUexpMeasurable hUone hUexp hae)


end Algsuperdiff.Section3.Provider.CoarseEllipticity
