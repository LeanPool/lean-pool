/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.BlockPayload
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCommonEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperDeepBandTailRareProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperOrdinaryBlockProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedDeepBandTailProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedDeepBandTailOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# UpperDeepBandTailOrdinaryLane

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The ordinary centered deep-band tail on the actual descendant carrier

This file constructs the random ordinary branch of the centered deep-band
tail, rather than only its deterministic profile.  The Whitney layers are
summed at a strictly positive geometric majorant, so their `Gamma_1` estimates
give both the countable weak-Orlicz bound and almost-everywhere summability.
The centered sum is then evaluated at the translated cutoff sample belonging
to each descendant cube.

The resulting per-cube estimate has the exact `cstar⁻¹ * gamma` dependence and
the source depth growth expected by the joint grid/depth maximum.  The final
part of the file also treats the literal good-cell centered-tail named summand
at the tuned collar-band depth, including its ordinary/rare finite-coordinate
split.  Other named lanes and the complete cutoff observable remain separate.
-/
namespace Algsuperdiff.Section3.Provider.CoarseEllipticity
open MeasureTheory HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Multiscale Algsuperdiff.Section3.Provider.Percolation
noncomputable section
variable {d : ℕ}
/-- A strictly positive enlargement of the deterministic ordinary layer
constant.  The added one is used only to make every summability scale positive;
it is absorbed into a dimension-only constant. -/
def probeSharpDeepBandTailOrdinaryAnalyticLayerConst (d : ℕ) : ℝ :=
  1 + probeSharpDeepBandTailOrdinaryLayerConst d
/-- The geometric positive scale used for one ordinary Whitney layer. -/
def probeSharpDeepBandTailOrdinaryAnalyticLayerScale
    (M : ABKModel d) (n : ℕ) : ℝ :=
  probeSharpDeepBandTailOrdinaryAnalyticLayerConst d *
    ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * M.gamma
/-- The exact geometric-series constant for the enlarged ordinary scales. -/
def probeSharpDeepBandTailOrdinaryAnalyticSumConst (d : ℕ) : ℝ :=
  probeSharpDeepBandTailOrdinaryAnalyticLayerConst d *
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹
/-- The dimension-only per-cube constant after the Whitney `Gamma_1` triangle
inequality and the literal outer mean coefficient are restored. -/
def probeSharpDeepBandTailOrdinaryAnalyticPerCubeConst (d : ℕ) : ℝ :=
  (1920 * simplexCrudeConst d (1 / 4) *
      probeSimplexMeanSensitivityConst d) *
    (gammaTriangleConst 1 *
      probeSharpDeepBandTailOrdinaryAnalyticSumConst d)
/-- The dimension-only per-cube constant after the finite coordinate trace. -/
def probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst (d : ℕ) : ℝ :=
  (d : ℝ) * probeSharpDeepBandTailOrdinaryAnalyticPerCubeConst d
/-- The unframed centered-tail square with an explicit band depth.  This is
the common carrier used by both sides of the separation split. -/
def probeSharpDeepBandTailTunedBaseTerm
    (M : ABKModel d) (root : ℤ) (k₀ k n : ℕ)
    (omega : CutoffSample d) : ℝ :=
  probeSharpDeepBandTailGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
          (k₀ : ℝ)))) *
    probeDeepBandGaugedTail M (originCube d root)
      (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ k₀ omega ^ 2
/-- The exact Gamma-one scale of the explicit-depth centered-tail carrier. -/
def probeSharpDeepBandTailTunedBaseScale
    (M : ABKModel d) (root : ℤ) (k₀ k n : ℕ) : ℝ :=
  probeSharpDeepBandTailGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
          (k₀ : ℝ)))) *
    probeDeepBandGaugedFluct M
      (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀
      (probeSharpLayerGap bfaProfileB n) ^ 2
/-- Dimension-only trace prefactor for the tuned rare good centered-tail lane. -/
def probeSharpDeepBandTailTunedRareTracePrefactor (d : ℕ) : ℝ :=
  (d : ℝ) * upperAfterBandRareTriangleConst *
    probeMeanGoodWaveDimensionConst d *
    probeSharpDeepBandTailRareSumConst d
/-- Dimension-only threshold paying the tuned depth, ordinary trace constant,
and the eighth-power exceptional reserve. -/
def probeSharpDeepBandTailTunedOutputConst (d : ℕ) : ℝ :=
  max (collarBandMeanDepthThreshold d)
    (1 + max (probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d)
      ((probeSharpDeepBandTailTunedRareTracePrefactor d + 8) *
        upperHsepResidualRate⁻¹))
private abbrev upperDeepBandTailOrdinaryLane_momentBounds1_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) {sigma Cup : ℝ} (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let B : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (eta : CutoffSample d) =>
        probeSharpDeepBandTailTunedBaseTerm M R.scale k₀ k n eta;
      let Q : CutoffSample d → ℝ := probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ);
      let O : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        (2 : ℝ) * B n (translateCutoffSample shift omega);
      let V : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        Q (translateCutoffSample shift omega) * B n (translateCutoffSample shift omega);
      let X : Fin d → ℕ → CutoffSample d → ℝ := fun (j : Fin d) (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
          (fun (eta : CutoffSample d) =>
            probeDeepBandGaugedTail M (originCube d R.scale) (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀ eta ^
              (2 : ℕ))
          (translateCutoffSample shift omega);
      let AO : ℝ := gammaTriangleConst (1 : ℝ) * (probeSharpDeepBandTailOrdinaryAnalyticSumConst d * M.gamma);
      let Z : ℝ := Real.exp (-(upperHsepResidualRate * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
      let AV : ℝ :=
        gammaTriangleConst (upperProfileTargetSigma sigma) * (probeSharpDeepBandTailRareSumConst d * M.gamma * Z);
      ∀ (_ : probeSharpDeepBandTailTunedOutputConst d ≤ Cup) (_ : (0 : ℝ) < Cup)
        (_ : max (Real.exp (profileAuxiliaryConst d / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ)),
        Cup ≤ (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹ ∧
          (∀ (n : ℕ) (omega : CutoffSample d), (0 : ℝ) ≤ O n omega) ∧
            (∀ (n : ℕ) (omega : CutoffSample d), (0 : ℝ) ≤ V n omega) ∧
              (∀ (n : ℕ), Measurable (O n)) ∧
                (∀ (n : ℕ), Measurable (V n)) ∧
                  (∀ (n : ℕ),
                      IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
                        (gammaSigma (upperProfileTargetSigma sigma)) (V n)
                        (probeSharpDeepBandTailRareGoodMassLayerBound M (↑E : ℝ) n)) ∧
                    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (1 : ℝ))
                        (fun (omega : CutoffSample d) => ∑' (n : ℕ), O n omega) AO ∧
                      IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
                          (gammaSigma (upperProfileTargetSigma sigma))
                          (fun (omega : CutoffSample d) => ∑' (n : ℕ), V n omega) AV ∧
                        ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                          Summable fun (n : ℕ) => O n omega

private abbrev upperDeepBandTailOrdinaryLane_momentBounds2_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma Cup : ℝ}
      (_ : (0 : ℝ) < sigma) (_ : sigma ≤ (1 / 2 : ℝ)) (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
      (_ : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let B : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (eta : CutoffSample d) =>
        probeSharpDeepBandTailTunedBaseTerm M R.scale k₀ k n eta;
      let Q : CutoffSample d → ℝ := probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ);
      let O : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        (2 : ℝ) * B n (translateCutoffSample shift omega);
      let V : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        Q (translateCutoffSample shift omega) * B n (translateCutoffSample shift omega);
      let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀);
      let ordinary : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), O n omega);
      let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), V n omega);
      let X : Fin d → ℕ → CutoffSample d → ℝ := fun (j : Fin d) (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
          (fun (eta : CutoffSample d) =>
            probeDeepBandGaugedTail M (originCube d R.scale) (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀ eta ^
              (2 : ℕ))
          (translateCutoffSample shift omega);
      let AO : ℝ := gammaTriangleConst (1 : ℝ) * (probeSharpDeepBandTailOrdinaryAnalyticSumConst d * M.gamma);
      let Z : ℝ := Real.exp (-(upperHsepResidualRate * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
      let AV : ℝ :=
        gammaTriangleConst (upperProfileTargetSigma sigma) * (probeSharpDeepBandTailRareSumConst d * M.gamma * Z);
      let ordinaryScale : ℝ := (↑d : ℝ) * (C * AO);
      let rareScale : ℝ := (↑d : ℝ) * (C * AV);
      ∀ (_ : probeSharpDeepBandTailTunedOutputConst d ≤ Cup) (_ : (0 : ℝ) < Cup)
        (_ :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (1 : ℝ))
            (fun (omega : CutoffSample d) => ∑' (n : ℕ), O n omega) AO)
        (_ :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma))
            (fun (omega : CutoffSample d) => ∑' (n : ℕ), V n omega) AV)
        (_ : (0 : ℝ) ≤ C) (_ : ∀ (omega : CutoffSample d), (0 : ℝ) ≤ ordinary omega)
        (_ : ∀ (omega : CutoffSample d), (0 : ℝ) ≤ rare omega)
        (_ :
          ∀ᵐ (x : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  (fun (j : Fin d) (n : ℕ) (omega : CutoffSample d) =>
                      probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                        (m - (1 : ℤ)) (basisVec j)
                        (fun (eta : CutoffSample d) =>
                          probeDeepBandGaugedTail M (originCube d R.scale)
                              (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                              (collarBandMeanDepth M (↑E : ℝ)) (collarBandMeanDepth M (↑E : ℝ)) eta ^
                            (2 : ℕ))
                        (translateCutoffSample (triadicCubeShift R) omega))
                    j n x ≤
              (fun (omega : CutoffSample d) =>
                    (↑d : ℝ) *
                      (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
                        ∑' (n : ℕ),
                          (fun (n : ℕ) (omega : CutoffSample d) =>
                              (2 : ℝ) *
                                (fun (n : ℕ) (eta : CutoffSample d) =>
                                    probeSharpDeepBandTailTunedBaseTerm M R.scale (collarBandMeanDepth M (↑E : ℝ)) k n eta)
                                  n (translateCutoffSample (triadicCubeShift R) omega))
                            n omega))
                  x +
                (fun (omega : CutoffSample d) =>
                    (↑d : ℝ) *
                      (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
                        ∑' (n : ℕ),
                          (fun (n : ℕ) (omega : CutoffSample d) =>
                              probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ)
                                  (translateCutoffSample (triadicCubeShift R) omega) *
                                (fun (n : ℕ) (eta : CutoffSample d) =>
                                    probeSharpDeepBandTailTunedBaseTerm M R.scale (collarBandMeanDepth M (↑E : ℝ)) k n eta)
                                  n (translateCutoffSample (triadicCubeShift R) omega))
                            n omega))
                  x)
        (_ :
          ∀ᵐ (x : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    ((fun (j : Fin d) (n : ℕ) (omega : CutoffSample d) =>
                        probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                          (m - (1 : ℤ)) (basisVec j)
                          (fun (eta : CutoffSample d) =>
                            probeDeepBandGaugedTail M (originCube d R.scale)
                                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                                (collarBandMeanDepth M (↑E : ℝ)) (collarBandMeanDepth M (↑E : ℝ)) eta ^
                              (2 : ℕ))
                          (translateCutoffSample (triadicCubeShift R) omega))
                      j n x) =
              ENNReal.ofReal
                (∑ j : Fin d,
                  ∑' (n : ℕ),
                    (fun (j : Fin d) (n : ℕ) (omega : CutoffSample d) =>
                        probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                          (m - (1 : ℤ)) (basisVec j)
                          (fun (eta : CutoffSample d) =>
                            probeDeepBandGaugedTail M (originCube d R.scale)
                                (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                                (collarBandMeanDepth M (↑E : ℝ)) (collarBandMeanDepth M (↑E : ℝ)) eta ^
                              (2 : ℕ))
                          (translateCutoffSample (triadicCubeShift R) omega))
                      j n x)),
        (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ∑ j : Fin d, ∑' (n : ℕ), ENNReal.ofReal (X j n omega) ≤
              ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega)) ∧
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (1 : ℝ)) ordinary ordinaryScale ∧
            IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) rare
                rareScale ∧
              (0 : ℝ) ≤ ordinaryScale ∧
                (0 : ℝ) ≤ rareScale ∧
                  (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ ∧
                    ordinaryScale ≤ upperSaturatedPerCubeAmplitude Cup (Disorder.cstar M) M.gamma k

private theorem three_rpow_neg_half_nonneg_ordinaryLane :
    0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_nonneg (by norm_num) _
private theorem three_rpow_neg_half_pos_ordinaryLane :
    0 < (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_pos_of_pos (by norm_num) _
private theorem three_rpow_neg_half_lt_one_ordinaryLane :
    (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
theorem probeSharpDeepBandTailOrdinaryAnalyticLayerConst_pos (d : ℕ) :
    0 < probeSharpDeepBandTailOrdinaryAnalyticLayerConst d := by
  rw [probeSharpDeepBandTailOrdinaryAnalyticLayerConst]
  linarith [probeSharpDeepBandTailOrdinaryLayerConst_nonneg d]
theorem probeSharpDeepBandTailOrdinaryAnalyticLayerScale_pos
    (M : ABKModel d) (n : ℕ) :
    0 < probeSharpDeepBandTailOrdinaryAnalyticLayerScale M n := by
  rw [probeSharpDeepBandTailOrdinaryAnalyticLayerScale]
  exact mul_pos
    (mul_pos (probeSharpDeepBandTailOrdinaryAnalyticLayerConst_pos d)
      (pow_pos three_rpow_neg_half_pos_ordinaryLane n))
    M.shellPrefix.gamma_pos
theorem probeSharpDeepBandTailOrdinaryAnalyticSumConst_pos (d : ℕ) :
    0 < probeSharpDeepBandTailOrdinaryAnalyticSumConst d := by
  rw [probeSharpDeepBandTailOrdinaryAnalyticSumConst]
  exact mul_pos (probeSharpDeepBandTailOrdinaryAnalyticLayerConst_pos d)
    (inv_pos.mpr (sub_pos.mpr three_rpow_neg_half_lt_one_ordinaryLane))
theorem summable_probeSharpDeepBandTailOrdinaryAnalyticLayerScale
    (M : ABKModel d) :
    Summable fun n => probeSharpDeepBandTailOrdinaryAnalyticLayerScale M n := by
  rw [show (fun n => probeSharpDeepBandTailOrdinaryAnalyticLayerScale M n) =
      fun n => probeSharpDeepBandTailOrdinaryAnalyticLayerConst d *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * M.gamma by
    funext n
    rfl]
  exact ((summable_geometric_of_lt_one
    three_rpow_neg_half_nonneg_ordinaryLane
    three_rpow_neg_half_lt_one_ordinaryLane).mul_left
      (probeSharpDeepBandTailOrdinaryAnalyticLayerConst d)).mul_right M.gamma
theorem tsum_probeSharpDeepBandTailOrdinaryAnalyticLayerScale_eq
    (M : ABKModel d) :
    ∑' n, probeSharpDeepBandTailOrdinaryAnalyticLayerScale M n =
      probeSharpDeepBandTailOrdinaryAnalyticSumConst d * M.gamma := by
  rw [show (fun n => probeSharpDeepBandTailOrdinaryAnalyticLayerScale M n) =
      fun n => probeSharpDeepBandTailOrdinaryAnalyticLayerConst d *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * M.gamma by
    funext n
    rfl]
  rw [tsum_mul_right, tsum_mul_left,
    tsum_geometric_of_lt_one three_rpow_neg_half_nonneg_ordinaryLane
      three_rpow_neg_half_lt_one_ordinaryLane]
  rfl
/-! ## Literal good centered-tail lane at the tuned collar depth -/
private theorem probeSharpDeepBandTailTunedBaseTerm_nonneg
    (M : ABKModel d) (root : ℤ) (k₀ k n : ℕ)
    (omega : CutoffSample d) :
    0 ≤ probeSharpDeepBandTailTunedBaseTerm M root k₀ k n omega := by
  rw [probeSharpDeepBandTailTunedBaseTerm]
  exact mul_nonneg
    (mul_nonneg (probeSharpDeepBandTailGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _))
    (sq_nonneg _)
private theorem measurable_probeSharpDeepBandTailTunedBaseTerm
    (M : ABKModel d) (root : ℤ) (k₀ k n : ℕ) :
    Measurable (probeSharpDeepBandTailTunedBaseTerm M root k₀ k n) := by
  have htail : Measurable
      (probeDeepBandGaugedTail M (originCube d root)
        (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ k₀) := by
    change Measurable (fun omega =>
      Real.sqrt M.gamma *
        (3 : ℝ) ^ (-(M.gamma *
          (probeSharpLayerAnchor root bfaProfileB k₀ n : ℝ))) *
        probeDeepBandTail M (originCube d root)
          (probeSharpLayerAnchor root bfaProfileB k₀ n + (k₀ : ℤ))
          k₀ k₀ omega)
    exact measurable_const.mul
      (probeDeepBandTail_measurable M (originCube d root)
        (probeSharpLayerAnchor root bfaProfileB k₀ n + (k₀ : ℤ))
        k₀ k₀)
  unfold probeSharpDeepBandTailTunedBaseTerm
  exact measurable_const.mul (htail.pow_const (2 : ℕ))
private theorem probeSharpDeepBandTailTunedBaseScale_nonneg
    (M : ABKModel d) (root : ℤ) (k₀ k n : ℕ) :
    0 ≤ probeSharpDeepBandTailTunedBaseScale M root k₀ k n := by
  rw [probeSharpDeepBandTailTunedBaseScale]
  exact mul_nonneg
    (mul_nonneg (probeSharpDeepBandTailGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _))
    (sq_nonneg _)
/-- The explicit-depth base carrier has its exact Gamma-one certificate. -/
private theorem isBigOWith_gammaSigma_one_probeSharpDeepBandTailTunedBaseTerm
    (M : ABKModel d) (root : ℤ) (k₀ k n : ℕ)
    (hk₀ : 2 ≤ k₀) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (probeSharpDeepBandTailTunedBaseTerm M root k₀ k n)
      (probeSharpDeepBandTailTunedBaseScale M root k₀ k n) := by
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  have htail := isBigOWith_gammaSigma_one_probeDeepBandGaugedTail_origin_sq
    M root ell hk₀ (probeSharpLayerAnchor_scale_eq root bfaProfileB k₀ n)
  have hc : 0 ≤ probeSharpDeepBandTailGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
          (k₀ : ℝ)))) :=
    mul_nonneg (probeSharpDeepBandTailGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _)
  unfold probeSharpDeepBandTailTunedBaseTerm probeSharpDeepBandTailTunedBaseScale
  exact htail.const_mul hc
/-- At a strict descendant, the literal good centered-tail summand is the
outer coefficient times the separated hsep factor and explicit-depth base. -/
private theorem probeSharpFramedGoodWavePart_deepBandTail_tuned_eq
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (k₀ n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedGoodWavePart M R.scale E bfaProfileB k₀ n (m - 1)
        (basisVec j)
        (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
          (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀ eta ^ 2)
        omega =
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j)) *
        (probeSharpAfterBandHsepFactor M R.scale E omega *
          probeSharpDeepBandTailTunedBaseTerm
            M R.scale k₀ k n omega) := by
  let D : ℝ := (k : ℝ) + (n : ℝ) +
    (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ)
  let C : ℝ := probeSharpDeepBandTailGoodMassCoeff d n
  let T : ℝ := probeDeepBandGaugedTail M (originCube d R.scale)
    (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀ omega ^ 2
  have hframe := probeSharpFramedAfterBandMultiplier_descendant_eq
    M hR E bfaProfileB k₀ n omega
  have hpow :
      (3 : ℝ) ^ (M.gamma *
          (hsep M R.scale E bfaProfileB omega : ℝ)) *
        (3 : ℝ) ^ (-(M.gamma * D)) =
      (3 : ℝ) ^ (M.gamma *
        ((hsep M R.scale E bfaProfileB omega : ℝ) - D)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [probeSharpFramedGoodWavePart,
    probeSharpDeepBandTailTunedBaseTerm,
    probeSharpAfterBandHsepFactor]
  change
    probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        Real.sqrt (probeSharpLayerMassEnvelope d n) *
        probeSharpFramedAfterBandMultiplier M R.scale E bfaProfileB
          k₀ n (m - 1) omega * (5 * (d : ℝ) ^ 2 * T) =
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j)) *
        ((3 : ℝ) ^ (M.gamma *
          (hsep M R.scale E bfaProfileB omega : ℝ)) *
          (C * (3 : ℝ) ^ (-(M.gamma * D)) * T))
  rw [hframe]
  change _ * (3 : ℝ) ^ (M.gamma *
      ((hsep M R.scale E bfaProfileB omega : ℝ) - D)) * _ =
    _ * ((3 : ℝ) ^ (M.gamma *
      (hsep M R.scale E bfaProfileB omega : ℝ)) *
      (C * (3 : ℝ) ^ (-(M.gamma * D)) * T))
  rw [← hpow]
  dsimp only [C]
  rw [probeSharpDeepBandTailGoodMassCoeff]
  ring
/-- Uniform tuned-depth bound for the squared grouped-tail scale. -/
private theorem probeDeepBandGaugedFluct_sq_le_tuned
    (M : ABKModel d) (root : ℤ) {E : ℝ} (hE : 1 ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) (n : ℕ) :
    let k₀ := collarBandMeanDepth M E
    probeDeepBandGaugedFluct M
        (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀
        (probeSharpLayerGap bfaProfileB n) ^ 2 ≤
      probeSharpDeepBandTailAmplitude d ^ 2 * M.gamma * 81 := by
  dsimp only
  let c := collarBandMeanDepthCoeff d
  let k₀ := collarBandMeanDepth M E
  let g₀ := probeSharpLayerGap bfaProfileB n
  let q := probeBandUnitGain d
  let A := probeSharpDeepBandTailAmplitude d
  have ht : 0 ≤ c * (E ^ 2)⁻¹ * M.gamma⁻¹ := by
    exact mul_nonneg
      (mul_nonneg (collarBandMeanDepthCoeff_pos d).le
        (inv_nonneg.mpr (sq_nonneg E)))
      (inv_nonneg.mpr M.shellPrefix.gamma_pos.le)
  have hdepth := waveBandDepth_spec
    (c := c) (E := E) M.shellPrefix.gamma_pos ht
  have hEinvSq : (E ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [hE])
  have hgamma1 : M.gamma ≤ 1 :=
    gamma_le_one_of_le_rpow_neg_fifth hE M.shellPrefix.gamma_pos hEgamma
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    exact collarBandMeanDepthCoeff_le_one d
  have hcEinv : c * (E ^ 2)⁻¹ ≤ 1 := by
    exact (mul_le_mul hc1 hEinvSq
      (inv_nonneg.mpr (sq_nonneg E)) (by norm_num)).trans_eq (one_mul 1)
  have hgk : M.gamma * (k₀ : ℝ) ≤ 2 := by
    dsimp only [k₀, collarBandMeanDepth] at ⊢
    nlinarith
  have hband : (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) ≤ 81 := by
    calc
      _ ≤ (3 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 81 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        norm_num
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact probeBandUnitGain_nonneg d
  have hq1 : q ≤ 1 :=
    (probeBandUnitGain_le M.shellPrefix.dimension).trans (by norm_num)
  have hqSq : (q ^ g₀) ^ 2 ≤ 1 := by
    have hqpow : q ^ g₀ ≤ 1 := pow_le_one₀ hq0 hq1
    nlinarith [pow_nonneg hq0 g₀]
  have hA0 : 0 ≤ A ^ 2 * M.gamma :=
    mul_nonneg (sq_nonneg A) M.shellPrefix.gamma_pos.le
  rw [probeDeepBandGaugedFluct_sq_eq_closed]
  change A ^ 2 * M.gamma * (q ^ g₀) ^ 2 *
      (3 : ℝ) ^ (2 * (M.gamma * (k₀ : ℝ))) ≤
    A ^ 2 * M.gamma * 81
  calc
    _ ≤ A ^ 2 * M.gamma * 1 * 81 := by gcongr
    _ = A ^ 2 * M.gamma * 81 := by ring
/-- Twice the tuned base scale has the same geometric ordinary majorant used
by the original depth-one lane. -/
private theorem two_mul_probeSharpDeepBandTailTunedBaseScale_le
    (M : ABKModel d) (root : ℤ) {E : ℝ} (hE : 1 ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) (k n : ℕ) :
    2 * probeSharpDeepBandTailTunedBaseScale M root
        (collarBandMeanDepth M E) k n ≤
      probeSharpDeepBandTailOrdinaryLayerConst d *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * M.gamma := by
  let k₀ := collarBandMeanDepth M E
  let A := probeSharpDeepBandTailAmplitude d
  let r : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  have hfluct := probeDeepBandGaugedFluct_sq_le_tuned
    M root hE hEgamma n
  have hD : 0 ≤ (k : ℝ) + (n : ℝ) +
      (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ) := by positivity
  have hframe : (3 : ℝ) ^ (-(M.gamma *
      ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
        (k₀ : ℝ)))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg M.shellPrefix.gamma_pos.le hD))
  have hcoeff0 : 0 ≤
      2 * probeSharpDeepBandTailGoodMassCoeff d n := by
    exact mul_nonneg (by norm_num)
      (probeSharpDeepBandTailGoodMassCoeff_nonneg d n)
  have hfluct0 : 0 ≤ probeDeepBandGaugedFluct M
      (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀
      (probeSharpLayerGap bfaProfileB n) ^ 2 := sq_nonneg _
  rw [probeSharpDeepBandTailTunedBaseScale]
  change 2 * (probeSharpDeepBandTailGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
          (k₀ : ℝ)))) *
      probeDeepBandGaugedFluct M
        (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀
        (probeSharpLayerGap bfaProfileB n) ^ 2) ≤ _
  calc
    _ = (2 * probeSharpDeepBandTailGoodMassCoeff d n) *
        (3 : ℝ) ^ (-(M.gamma *
          ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
            (k₀ : ℝ)))) *
        probeDeepBandGaugedFluct M
          (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀
          (probeSharpLayerGap bfaProfileB n) ^ 2 := by ring
    _ ≤ (2 * probeSharpDeepBandTailGoodMassCoeff d n) * 1 *
        probeDeepBandGaugedFluct M
          (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀
          (probeSharpLayerGap bfaProfileB n) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hframe hcoeff0) hfluct0
    _ ≤ 2 * probeSharpDeepBandTailGoodMassCoeff d n * 1 *
        (A ^ 2 * M.gamma * 81) :=
      mul_le_mul_of_nonneg_left (by simpa only [k₀, A] using hfluct)
        (mul_nonneg hcoeff0 (by norm_num))
    _ = probeSharpDeepBandTailOrdinaryLayerConst d * r ^ n *
        M.gamma := by
      rw [probeSharpDeepBandTailGoodMassCoeff,
        probeSharpDeepBandTailOrdinaryLayerConst,
        sqrt_probeSharpLayerMassEnvelope_eq]
      dsimp only [A, r]
      rw [show (3 : ℝ) ^ (-(n : ℝ) / 2) =
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n by
          rw [show -(n : ℝ) / 2 = (-(1 / 2 : ℝ)) * (n : ℝ) by ring,
            Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
            Real.rpow_natCast]]
      ring
private theorem probeSharpDeepBandTailTunedBaseScale_le_half_layer
    (M : ABKModel d) (root : ℤ) {E : ℝ} (hE : 1 ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) (k n : ℕ) :
    probeSharpDeepBandTailTunedBaseScale M root
        (collarBandMeanDepth M E) k n ≤
      (1 / 2 : ℝ) * (probeSharpDeepBandTailOrdinaryLayerConst d *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * M.gamma) := by
  have htwo := two_mul_probeSharpDeepBandTailTunedBaseScale_le
    M root hE hEgamma k n
  linarith
private theorem probeSharpDeepBandTailTunedRareScale_le_layerBound
    (M : ABKModel d) (root : ℤ) {E sigma : ℝ} (hE : 1 ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (k n : ℕ) :
    HCPolySupport.Book.Ch04.gammaProductConst
        (upperProfileHsepTau sigma) 1 *
      upperHsepResidualScale sigma M.gamma *
      probeSharpDeepBandTailTunedBaseScale M root
        (collarBandMeanDepth M E) k n ≤
      probeSharpDeepBandTailRareGoodMassLayerBound M E n := by
  let G : ℝ := HCPolySupport.Book.Ch04.gammaProductConst
    (upperProfileHsepTau sigma) 1
  let AR : ℝ := upperHsepResidualScale sigma M.gamma
  let AX : ℝ := probeSharpDeepBandTailTunedBaseScale M root
    (collarBandMeanDepth M E) k n
  let r : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  let Z : ℝ := Real.exp
    (-(upperHsepResidualRate * (E⁻¹ ^ 2 * M.gamma⁻¹)))
  have hG : G ≤ 64 :=
    gammaProductConst_upperProfileHsepTau_one_le_sixty_four hsigma0 hsigma
  have hAR : AR ≤ upperHsepResidualConst * Z := by
    exact upperHsepResidualScale_le_exp hsigma0 hsigma hE
      M.shellPrefix.gamma_pos
  have hAX : AX ≤ (1 / 2 : ℝ) *
      (probeSharpDeepBandTailOrdinaryLayerConst d * r ^ n *
        M.gamma) := by
    simpa only [AX, r] using
      probeSharpDeepBandTailTunedBaseScale_le_half_layer
        M root hE hEgamma k n
  have hAR0 : 0 ≤ AR := (upperHsepResidualScale_pos sigma M.gamma).le
  have hAX0 : 0 ≤ AX := by
    dsimp only [AX]
    exact probeSharpDeepBandTailTunedBaseScale_nonneg M root
      (collarBandMeanDepth M E) k n
  have hZ0 : 0 ≤ Z := by dsimp only [Z]; exact (Real.exp_pos _).le
  have hres0 : 0 ≤ upperHsepResidualConst * Z :=
    mul_nonneg upperHsepResidualConst_pos.le hZ0
  have hprod :
      G * AR * AX ≤
        (64 * (upperHsepResidualConst * Z)) *
          ((1 / 2 : ℝ) *
            (probeSharpDeepBandTailOrdinaryLayerConst d * r ^ n *
              M.gamma)) :=
    mul_le_mul
      (mul_le_mul hG hAR hAR0 (by norm_num)) hAX hAX0
      (mul_nonneg (by norm_num) hres0)
  have hcoef0 : 0 ≤ 32 * upperHsepResidualConst *
      probeSharpDeepBandTailOrdinaryLayerConst d :=
    mul_nonneg
      (mul_nonneg (by norm_num) upperHsepResidualConst_pos.le)
      (probeSharpDeepBandTailOrdinaryLayerConst_nonneg d)
  have hcoef : 32 * upperHsepResidualConst *
        probeSharpDeepBandTailOrdinaryLayerConst d ≤
      probeSharpDeepBandTailRareLayerConst d := by
    rw [probeSharpDeepBandTailRareLayerConst]
    linarith
  change G * AR * AX ≤
    probeSharpDeepBandTailRareLayerConst d * r ^ n * M.gamma * Z
  calc
    _ ≤ (64 * (upperHsepResidualConst * Z)) *
          ((1 / 2 : ℝ) *
            (probeSharpDeepBandTailOrdinaryLayerConst d * r ^ n *
              M.gamma)) := hprod
    _ = (32 * upperHsepResidualConst *
          probeSharpDeepBandTailOrdinaryLayerConst d) *
        r ^ n * M.gamma * Z := by ring
    _ ≤ probeSharpDeepBandTailRareLayerConst d * r ^ n * M.gamma * Z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef
            (pow_nonneg (Real.rpow_nonneg (by norm_num) _) n))
          M.shellPrefix.gamma_pos.le) hZ0
private theorem isBigOWith_gammaSigma_one_tunedDeepTailOrdinaryLayer
    (M : ABKModel d) (root : ℤ) {E : ℝ} (hE : 1 ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hk₀ : 2 ≤ collarBandMeanDepth M E) (k n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (fun omega => 2 * probeSharpDeepBandTailTunedBaseTerm M root
        (collarBandMeanDepth M E) k n omega)
      (probeSharpDeepBandTailOrdinaryAnalyticLayerScale M n) := by
  have hbase :=
    (isBigOWith_gammaSigma_one_probeSharpDeepBandTailTunedBaseTerm
      M root (collarBandMeanDepth M E) k n hk₀).const_mul
        (by norm_num : (0 : ℝ) ≤ 2)
  refine hbase.mono_scale ?_
  have hraw := two_mul_probeSharpDeepBandTailTunedBaseScale_le
    M root hE hEgamma k n
  have hconst : probeSharpDeepBandTailOrdinaryLayerConst d ≤
      probeSharpDeepBandTailOrdinaryAnalyticLayerConst d := by
    rw [probeSharpDeepBandTailOrdinaryAnalyticLayerConst]
    linarith
  rw [probeSharpDeepBandTailOrdinaryAnalyticLayerScale]
  exact hraw.trans <| mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconst
      (pow_nonneg three_rpow_neg_half_nonneg_ordinaryLane n))
    M.shellPrefix.gamma_pos.le
private theorem isBigOWith_upperProfileTarget_tunedDeepTailRareLayer
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hk₀ : 2 ≤ collarBandMeanDepth M (E : ℝ)) (n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega =>
        probeSharpAfterBandHsepResidual M R.scale (E : ℝ) omega *
          probeSharpDeepBandTailTunedBaseTerm M R.scale
            (collarBandMeanDepth M (E : ℝ)) k n omega)
      (probeSharpDeepBandTailRareGoodMassLayerBound M (E : ℝ) n) := by
  obtain ⟨_hpoint, hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hS hsigma0 hsigma hmax hEgamma
  have hbase :=
    isBigOWith_gammaSigma_one_probeSharpDeepBandTailTunedBaseTerm
      M R.scale (collarBandMeanDepth M (E : ℝ)) k n hk₀
  have hproduct := isBigOWith_upperProfileTarget_hsep_mul_one
    hsigma0 hsigma (upperHsepResidualScale_pos sigma M.gamma).le
    (probeSharpDeepBandTailTunedBaseScale_nonneg M R.scale
      (collarBandMeanDepth M (E : ℝ)) k n)
    (probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ))
    (probeSharpDeepBandTailTunedBaseTerm_nonneg M R.scale
      (collarBandMeanDepth M (E : ℝ)) k n)
    hresidual hbase
  exact hproduct.mono_scale
    (probeSharpDeepBandTailTunedRareScale_le_layerBound
      M R.scale E.property hEgamma hsigma0 hsigma k n)
theorem probeSharpDeepBandTailTunedOutputConst_pos (d : ℕ) :
    0 < probeSharpDeepBandTailTunedOutputConst d :=
  (collarBandMeanDepthThreshold_pos d).trans_le (le_max_left _ _)
private theorem probeSharpDeepBandTailTunedRareTracePrefactor_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpDeepBandTailTunedRareTracePrefactor d := by
  rw [probeSharpDeepBandTailTunedRareTracePrefactor]
  have hT : 0 ≤ upperAfterBandRareTriangleConst := by
    rw [upperAfterBandRareTriangleConst]
    positivity
  have hW : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hT) hW)
    (probeSharpDeepBandTailRareSumConst_pos d).le
private theorem probeSharpDeepBandTailTuned_output_choice
    {Cup : ℝ} (hCup : probeSharpDeepBandTailTunedOutputConst d ≤ Cup) :
    probeSharpDeepBandTailTunedRareTracePrefactor d + 8 ≤
      upperHsepResidualRate * Cup := by
  have hbranch :
      (probeSharpDeepBandTailTunedRareTracePrefactor d + 8) *
          upperHsepResidualRate⁻¹ ≤ Cup := by
    calc
      _ ≤ 1 + max
          (probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d)
          ((probeSharpDeepBandTailTunedRareTracePrefactor d + 8) *
            upperHsepResidualRate⁻¹) := by
        linarith [le_max_right
          (probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d)
          ((probeSharpDeepBandTailTunedRareTracePrefactor d + 8) *
            upperHsepResidualRate⁻¹)]
      _ ≤ probeSharpDeepBandTailTunedOutputConst d := le_max_right _ _
      _ ≤ Cup := hCup
  have hmul := mul_le_mul_of_nonneg_left hbranch
    upperHsepResidualRate_pos.le
  have hcancel : upperHsepResidualRate *
      ((probeSharpDeepBandTailTunedRareTracePrefactor d + 8) *
        upperHsepResidualRate⁻¹) =
      probeSharpDeepBandTailTunedRareTracePrefactor d + 8 := by
    field_simp [ne_of_gt upperHsepResidualRate_pos]
  rwa [hcancel] at hmul
private theorem deepBandTailTrace_seriesIdentity :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d},
      R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) →
        ∀ {E : { E : ℝ // (1 : ℝ) ≤ E }},
          (2 : ℕ) ≤ d →
            let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
            let shift : Vec d := triadicCubeShift R;
            ∀ (j₀ : Fin d),
              let B : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (eta : CutoffSample d) =>
                probeSharpDeepBandTailTunedBaseTerm M R.scale k₀ k n eta;
              let Q : CutoffSample d → ℝ := probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ);
              let O : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
                (2 : ℝ) * B n (translateCutoffSample shift omega);
              let V : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
                Q (translateCutoffSample shift omega) * B n (translateCutoffSample shift omega);
              let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀);
              let ordinary : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), O n omega);
              let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), V n omega);
              let X : Fin d → ℕ → CutoffSample d → ℝ := fun (j : Fin d) (n : ℕ) (omega : CutoffSample d) =>
                probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                  (fun (eta : CutoffSample d) =>
                    probeDeepBandGaugedTail M (originCube d R.scale) (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀
                        eta ^
                      (2 : ℕ))
                  (translateCutoffSample shift omega);
              (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                  Summable fun (n : ℕ) => O n omega) →
                (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                    Summable fun (n : ℕ) => V n omega) →
                  (∀ (omega : CutoffSample d),
                      probeSharpAfterBandHsepFactor M R.scale (↑E : ℝ) omega ≤
                        (2 : ℝ) + probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) omega) →
                    ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                      ∑ j : Fin d, ∑' (n : ℕ), X j n omega ≤ ordinary omega + rare omega ∧
                        ∑ j : Fin d, ∑' (n : ℕ), ENNReal.ofReal (X j n omega) =
                          ENNReal.ofReal (∑ j : Fin d, ∑' (n : ℕ), X j n omega) := by
  intro d M m k R hR E hd k₀ shift _ B Q O V C ordinary rare X hOsumAE hVsumAE hsepPoint
  filter_upwards [hOsumAE, hVsumAE] with omega hOsum hVsum
  let eta := translateCutoffSample shift omega
  have hX0 (j : Fin d) : ∀ n, 0 ≤ X j n omega := fun n => by
    simpa only [X, eta] using
      probeSharpFramedGoodWavePart_nonneg hd M R.scale (E : ℝ)
        bfaProfileB k₀ n (m - 1) (basisVec j) (fun _ => sq_nonneg _) eta
  have hcoord (j : Fin d) : Summable (fun n => X j n omega) ∧
      (∑' n, X j n omega) ≤
      C * (∑' n, O n omega) + C * (∑' n, V n omega) := by
    let Cj : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
    let Oj : ℕ → ℝ := fun n => Cj * O n omega
    let Vj : ℕ → ℝ := fun n => Cj * V n omega
    have hCj : 0 ≤ Cj := mul_nonneg
      (probeMeanGoodWaveConst_nonneg hd M)
      (vecNormSq_nonneg (basisVec j))
    have hOj : Summable Oj := hOsum.mul_left Cj
    have hVj : Summable Vj := hVsum.mul_left Cj
    have hXle : ∀ n, X j n omega ≤ Oj n + Vj n := by
      intro n
      simp only [X]
      rw [probeSharpFramedGoodWavePart_deepBandTail_tuned_eq
        M hR (E : ℝ) k₀ n j eta]
      have hB0 := probeSharpDeepBandTailTunedBaseTerm_nonneg
        M R.scale k₀ k n eta
      calc
        Cj * (probeSharpAfterBandHsepFactor M R.scale (E : ℝ) eta *
            B n eta) ≤
          Cj * ((2 + Q eta) * B n eta) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hsepPoint eta) hB0) hCj
        _ = Oj n + Vj n := by
          simp only [Oj, Vj, O, V, B, Q, eta, Cj]
          ring
    have hXsum : Summable (fun n => X j n omega) :=
      Summable.of_nonneg_of_le (hX0 j) hXle (hOj.add hVj)
    refine ⟨hXsum, ?_⟩
    calc
      ∑' n, X j n omega ≤ ∑' n, (Oj n + Vj n) :=
        Summable.tsum_le_tsum hXle hXsum (hOj.add hVj)
      _ = (∑' n, Oj n) + ∑' n, Vj n := hOj.tsum_add hVj
      _ = C * (∑' n, O n omega) + C * (∑' n, V n omega) := by
        simp only [Oj, Vj, tsum_mul_left]
        rw [show Cj = C by
          simp only [Cj, C, vecNormSq_basisVec]]
  constructor
  · calc
    (∑ j : Fin d, ∑' n : ℕ, X j n omega) ≤
        ∑ _j : Fin d,
          (C * (∑' n, O n omega) + C * (∑' n, V n omega)) :=
      Finset.sum_le_sum fun j _ => (hcoord j).2
    _ = ordinary omega + rare omega := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ordinary, rare]
      ring
  · rw [ENNReal.ofReal_sum_of_nonneg
      (fun j _ => tsum_nonneg fun n => hX0 j n)]
    exact Finset.sum_congr rfl fun j _ =>
      (ENNReal.ofReal_tsum_of_nonneg (hX0 j) (hcoord j).1).symm

private theorem upperDeepBandTailOrdinaryLane_momentBounds1 : upperDeepBandTailOrdinaryLane_momentBounds1_statement := by
  intro d M _ k R hR E hS sigma Cup hsigma0 hsigma hmax hEgamma k₀ shift B _ O V X AO Z AV hout hCup0 hmaxAux
  have hgammaZ : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹ :=
    outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgammaZ
  have hdepth : collarBandMeanDepthThreshold d ≤ Cup :=
    (le_max_left _ _).trans hout
  have hk₀ : 2 ≤ k₀ := by
    have hthree : 3 ≤ collarBandMeanDepth M (E : ℝ) :=
      three_le_waveBandDepth_collarBandMeanDepthCoeff
        (lt_of_lt_of_le zero_lt_one E.property)
        M.shellPrefix.gamma_pos rfl (hdepth.trans hX)
    simpa only [k₀] using (show 2 ≤ collarBandMeanDepth M (E : ℝ) by omega)
  have hO0 : ∀ n omega, 0 ≤ O n omega := by
    intro n omega
    exact mul_nonneg (by norm_num)
      (probeSharpDeepBandTailTunedBaseTerm_nonneg M R.scale k₀ k n _)
  have hV0 : ∀ n omega, 0 ≤ V n omega := by
    intro n omega
    exact mul_nonneg
      (probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ) _)
      (probeSharpDeepBandTailTunedBaseTerm_nonneg M R.scale k₀ k n _)
  have hOmeas : ∀ n, Measurable (O n) := by
    intro n
    exact ((measurable_probeSharpDeepBandTailTunedBaseTerm
      M R.scale k₀ k n).comp
        (measurable_translateCutoffSample shift)).const_mul 2
  have hVmeas : ∀ n, Measurable (V n) := by
    intro n
    exact ((measurable_probeSharpAfterBandHsepResidual
      M R.scale (E : ℝ)).comp
        (measurable_translateCutoffSample shift)).mul
      ((measurable_probeSharpDeepBandTailTunedBaseTerm
        M R.scale k₀ k n).comp
          (measurable_translateCutoffSample shift))
  have hOterm : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (O n)
      (probeSharpDeepBandTailOrdinaryAnalyticLayerScale M n) := by
    intro n
    have hcenter :=
      isBigOWith_gammaSigma_one_tunedDeepTailOrdinaryLayer
        M R.scale E.property hEgamma hk₀ k n
    exact Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift
      (measurable_probeSharpDeepBandTailTunedBaseTerm
        M R.scale k₀ k n |>.const_mul 2)
      (by simpa only [O, B, k₀, shift] using hcenter)
  have hVterm : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma)) (V n)
      (probeSharpDeepBandTailRareGoodMassLayerBound M (E : ℝ) n) := by
    intro n
    have hcenter := isBigOWith_upperProfileTarget_tunedDeepTailRareLayer
      M hR hS hsigma0 hsigma hmaxAux hEgamma hk₀ n
    exact Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift
      ((measurable_probeSharpAfterBandHsepResidual M R.scale (E : ℝ)).mul
        (measurable_probeSharpDeepBandTailTunedBaseTerm
          M R.scale k₀ k n))
      (show IsBigOWith (cutoffSampleLaw M).toMeasure
          (gammaSigma (upperProfileTargetSigma sigma))
          (fun omega => probeSharpAfterBandHsepResidual M R.scale (E : ℝ) omega *
            probeSharpDeepBandTailTunedBaseTerm M R.scale k₀ k n omega)
          (probeSharpDeepBandTailRareGoodMassLayerBound M (E : ℝ) n) from
        hcenter)
  have hObig : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (fun omega => ∑' n, O n omega) AO := by
    have h := Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
      (μ := (cutoffSampleLaw M).toMeasure) (σ := 1)
      (X := O) (a := probeSharpDeepBandTailOrdinaryAnalyticLayerScale M)
      one_pos hO0 hOmeas
      (probeSharpDeepBandTailOrdinaryAnalyticLayerScale_pos M)
      (summable_probeSharpDeepBandTailOrdinaryAnalyticLayerScale M)
      hOterm
      (by rw [tsum_probeSharpDeepBandTailOrdinaryAnalyticLayerScale_eq])
    simpa only [AO] using h
  have hVbig : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => ∑' n, V n omega) AV := by
    have h := Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
      (μ := (cutoffSampleLaw M).toMeasure)
      (σ := upperProfileTargetSigma sigma)
      (X := V) (a := probeSharpDeepBandTailRareGoodMassLayerBound M (E : ℝ))
      (upperProfileTargetSigma_pos hsigma0 hsigma) hV0 hVmeas
      (probeSharpDeepBandTailRareGoodMassLayerBound_pos M (E : ℝ))
      (summable_probeSharpDeepBandTailRareGoodMassLayerBound M (E : ℝ))
      hVterm
      (by rw [tsum_probeSharpDeepBandTailRareGoodMassLayerBound_eq])
    simpa only [AV, Z] using h
  have hOsumAE : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => O n omega :=
    Algsuperdiff.Section3.Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      one_pos hO0 (fun n => (hOmeas n).aemeasurable)
      (probeSharpDeepBandTailOrdinaryAnalyticLayerScale_pos M)
      (summable_probeSharpDeepBandTailOrdinaryAnalyticLayerScale M) hOterm
  exact ⟨hX, hO0, hV0, hOmeas, hVmeas, hVterm, hObig, hVbig, hOsumAE⟩

private theorem upperDeepBandTailOrdinaryLane_momentBounds2 : upperDeepBandTailOrdinaryLane_momentBounds2_statement := by
  intro d M _ k _ E sigma Cup _ _ hEgamma _ _ _ _ _ _ _ _ C ordinary rare X AO Z AV ordinaryScale rareScale hout hCup0 hObig hVbig hC0 hordinary0 hrare0 hpoint hENNRealEq
  have hENNRealDom : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal (X j n omega)) ≤
        ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega) := by
    filter_upwards [hpoint, hENNRealEq] with omega hpointOmega hEqOmega
    rw [hEqOmega, ← ENNReal.ofReal_add (hordinary0 omega) (hrare0 omega)]
    exact ENNReal.ofReal_le_ofReal hpointOmega
  have hordinaryOrlicz : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) ordinary ordinaryScale := by
    simpa only [ordinary, ordinaryScale] using
      (hObig.const_mul hC0).const_mul (Nat.cast_nonneg d)
  have hrareOrlicz : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3)) rare rareScale := by
    simpa only [ordinary, rare, rareScale, upperProfileTargetSigma] using
      (hVbig.const_mul hC0).const_mul (Nat.cast_nonneg d)
  have hordinaryScale0 : 0 ≤ ordinaryScale := by
    dsimp only [ordinaryScale, AO]
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg hC0
        (mul_nonneg gammaTriangleConst_pos.le
          (mul_nonneg
            (probeSharpDeepBandTailOrdinaryAnalyticSumConst_pos d).le
            M.shellPrefix.gamma_pos.le)))
  have hrareScale0 : 0 ≤ rareScale := by
    dsimp only [rareScale, AV, Z]
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg hC0
        (mul_nonneg gammaTriangleConst_pos.le
          (mul_nonneg
            (mul_nonneg (probeSharpDeepBandTailRareSumConst_pos d).le
              M.shellPrefix.gamma_pos.le)
            (Real.exp_pos _).le)))
  have hordinaryConst :
      probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d ≤ Cup := by
    have hsecond : 1 + max
        (probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d)
        ((probeSharpDeepBandTailTunedRareTracePrefactor d + 8) *
          upperHsepResidualRate⁻¹) ≤ Cup :=
      (le_max_right _ _).trans hout
    linarith [le_max_left
      (probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d)
      ((probeSharpDeepBandTailTunedRareTracePrefactor d + 8) *
        upperHsepResidualRate⁻¹)]
  have hcstar0 : 0 ≤
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1).le
  have hgamma1 : M.gamma ≤ 1 :=
    gamma_le_one_of_le_rpow_neg_fifth E.property
      M.shellPrefix.gamma_pos hEgamma
  have hordinaryRaw : ordinaryScale =
      probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma := by
    dsimp only [ordinaryScale, C, AO]
    rw [vecNormSq_basisVec, mul_one, probeMeanGoodWaveConst,
      probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst,
      probeSharpDeepBandTailOrdinaryAnalyticPerCubeConst]
    ring
  have hordinaryScale : ordinaryScale ≤
      upperSaturatedPerCubeAmplitude Cup
        (Algsuperdiff.Section3.Disorder.cstar M) M.gamma k := by
    rw [hordinaryRaw]
    have hbase : probeSharpDeepBandTailOrdinaryAnalyticTracePerCubeConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma ≤
      Cup * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hordinaryConst hcstar0)
        M.shellPrefix.gamma_pos.le
    have hpow : 1 ≤ (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) :=
      Real.one_le_rpow (by norm_num)
        (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
    exact hbase.trans <| (by
      calc
        Cup * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma ≤
            Cup * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
              (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg hCup0.le hcstar0)
              M.shellPrefix.gamma_pos.le)
        _ ≤ upperSaturatedPerCubeAmplitude Cup
              (Algsuperdiff.Section3.Disorder.cstar M) M.gamma k :=
          plainGammaPerCubeAmplitude_le_upperSaturated hCup0.le hcstar0
            M.shellPrefix.gamma_pos.le hgamma1 k)
  exact ⟨hENNRealDom, hordinaryOrlicz, hrareOrlicz, hordinaryScale0, hrareScale0, hcstar0,
    hordinaryScale⟩

/-- Finite-coordinate split for literal summand four of the named sharp
envelope at the tuned collar-band depth.  The pointwise comparison is stated
on the full-measure set where the nonnegative deep-tail Whitney series are
summable. -/
theorem exists_tunedDeepBandTail_good_finite_trace_split
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : max (profileAuxiliaryConst d)
      (probeSharpDeepBandTailTunedOutputConst d) ≤ Cup) :
    ∃ ordinary rare : CutoffSample d → ℝ,
      ∃ ordinaryScale rareScale : ℝ,
        (∀ omega, 0 ≤ ordinary omega) ∧
        Measurable ordinary ∧
        (∀ omega, 0 ≤ rare omega) ∧
        Measurable rare ∧
        (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
          (∑ j : Fin d, ∑' n : ℕ,
            probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => probeDeepBandGaugedTail M
                (originCube d R.scale)
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n)
                (collarBandMeanDepth M (E : ℝ))
                (collarBandMeanDepth M (E : ℝ)) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega)) ≤
            ordinary omega + rare omega) ∧
        (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n)
                (collarBandMeanDepth M (E : ℝ))
                (collarBandMeanDepth M (E : ℝ)) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) =
            ENNReal.ofReal (∑ j : Fin d, ∑' n : ℕ,
              probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
                (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
                (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
                  (probeSharpLayerAnchor R.scale bfaProfileB
                    (collarBandMeanDepth M (E : ℝ)) n)
                  (collarBandMeanDepth M (E : ℝ))
                  (collarBandMeanDepth M (E : ℝ)) eta ^ 2)
                (translateCutoffSample (triadicCubeShift R) omega))) ∧
        (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n)
                (collarBandMeanDepth M (E : ℝ))
                (collarBandMeanDepth M (E : ℝ)) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) ≤
            ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega)) ∧
        IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
          ordinary ordinaryScale ∧
        0 ≤ ordinaryScale ∧
        ordinaryScale ≤ upperSaturatedPerCubeAmplitude Cup
          (Algsuperdiff.Section3.Disorder.cstar M) M.gamma k ∧
        IsBigOWith (cutoffSampleLaw M).toMeasure
          (gammaSigma ((1 - sigma) / 3)) rare rareScale ∧
        0 ≤ rareScale ∧
        rareScale ≤
          (Real.exp (-(Cup⁻¹ *
            ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) ^ 8) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let shift : Vec d := triadicCubeShift R
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let B : ℕ → CutoffSample d → ℝ := fun n eta =>
    probeSharpDeepBandTailTunedBaseTerm M R.scale k₀ k n eta
  let Q : CutoffSample d → ℝ :=
    probeSharpAfterBandHsepResidual M R.scale (E : ℝ)
  let O : ℕ → CutoffSample d → ℝ := fun n omega => 2 * B n
    (translateCutoffSample shift omega)
  let V : ℕ → CutoffSample d → ℝ := fun n omega =>
    Q (translateCutoffSample shift omega) *
      B n (translateCutoffSample shift omega)
  let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀)
  let ordinary : CutoffSample d → ℝ := fun omega =>
    (d : ℝ) * (C * ∑' n : ℕ, O n omega)
  let rare : CutoffSample d → ℝ := fun omega =>
    (d : ℝ) * (C * ∑' n : ℕ, V n omega)
  let X : Fin d → ℕ → CutoffSample d → ℝ := fun j n omega =>
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
      k₀ n (m - 1) (basisVec j)
      (fun eta => probeDeepBandGaugedTail M (originCube d R.scale)
        (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ k₀ eta ^ 2)
      (translateCutoffSample shift omega)
  let AO : ℝ := gammaTriangleConst 1 *
    (probeSharpDeepBandTailOrdinaryAnalyticSumConst d * M.gamma)
  let Z : ℝ := Real.exp (-(upperHsepResidualRate *
    ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))
  let AV : ℝ := gammaTriangleConst (upperProfileTargetSigma sigma) *
    (probeSharpDeepBandTailRareSumConst d * M.gamma * Z)
  let ordinaryScale : ℝ := (d : ℝ) * (C * AO)
  let rareScale : ℝ := (d : ℝ) * (C * AV)
  have hout : probeSharpDeepBandTailTunedOutputConst d ≤ Cup :=
    (le_max_right _ _).trans houtput
  have haux : profileAuxiliaryConst d ≤ Cup := (le_max_left _ _).trans houtput
  have hCup0 : 0 < Cup := (probeSharpDeepBandTailTunedOutputConst_pos d).trans_le hout
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  obtain ⟨hX, hO0, hV0, hOmeas, hVmeas, hVterm, hObig, hVbig, hOsumAE⟩ :=
    (show (Cup ≤ (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹) ∧ (∀ n omega, 0 ≤ O n omega) ∧ (∀ n omega, 0 ≤ V n
      omega) ∧ (∀ n, Measurable (O n)) ∧ (∀ n, Measurable (V n)) ∧ (∀ n, IsBigOWith
        (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma)) (V n)
      (probeSharpDeepBandTailRareGoodMassLayerBound M (E : ℝ) n)) ∧ (IsBigOWith (cutoffSampleLaw
        M).toMeasure
      (gammaSigma 1) (fun omega => ∑' n, O n omega) AO) ∧ (IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => ∑' n, V n omega) AV) ∧ (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => O n omega) from
      @upperDeepBandTailOrdinaryLane_momentBounds1 (d) (M) (m) (k) (R) (hR) (E) (hS) (sigma) (Cup)
        (hsigma0) (hsigma) (hmax) (hEgamma) (hout) (hCup0) (hmaxAux))
  have hVsumAE : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => V n omega :=
    Algsuperdiff.Section3.Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      (upperProfileTargetSigma_pos hsigma0 hsigma) hV0
      (fun n => (hVmeas n).aemeasurable)
      (probeSharpDeepBandTailRareGoodMassLayerBound_pos M (E : ℝ))
      (summable_probeSharpDeepBandTailRareGoodMassLayerBound M (E : ℝ)) hVterm
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (probeMeanGoodWaveConst_nonneg hd M)
      (vecNormSq_nonneg (basisVec j₀))
  have hordinary0 : ∀ omega, 0 ≤ ordinary omega := by
    intro omega
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg hC0 (tsum_nonneg fun n => hO0 n omega))
  have hrare0 : ∀ omega, 0 ≤ rare omega := by
    intro omega
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg hC0 (tsum_nonneg fun n => hV0 n omega))
  have hOsumMeas : Measurable (fun omega => ∑' n, O n omega) := by
    have hnn := (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (hOmeas n).real_toNNReal).coe_nnreal_real
    convert hnn using 1
    funext omega
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by
      rw [Real.toNNReal_of_nonneg (hO0 n omega)]
      rfl
  have hVsumMeas : Measurable (fun omega => ∑' n, V n omega) := by
    have hnn := (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (hVmeas n).real_toNNReal).coe_nnreal_real
    convert hnn using 1
    funext omega
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by
      rw [Real.toNNReal_of_nonneg (hV0 n omega)]
      rfl
  have hordinaryMeas : Measurable ordinary :=
    (hOsumMeas.const_mul C).const_mul d
  have hrareMeas : Measurable rare :=
    (hVsumMeas.const_mul C).const_mul d
  obtain ⟨hsepPoint, _⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hS hsigma0 hsigma hmaxAux hEgamma
  have hpointEq := @deepBandTailTrace_seriesIdentity (d) (M) (m) (k) (R) (hR) (E) (hd) (j₀)
    (hOsumAE) (hVsumAE) (hsepPoint)
  have hpoint := hpointEq.mono fun _ h => h.1
  have hENNRealEq := hpointEq.mono fun _ h => h.2
  obtain ⟨hENNRealDom, hordinaryOrlicz, hrareOrlicz, hordinaryScale0, hrareScale0, hcstar0,
    hordinaryScale⟩ :=
    (show (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal (X j n omega)) ≤
        ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega)) ∧ (IsBigOWith
          (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) ordinary ordinaryScale) ∧ (IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3)) rare rareScale) ∧ (0 ≤ ordinaryScale) ∧ (0 ≤ rareScale) ∧ (0 ≤
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) ∧ (ordinaryScale ≤
      upperSaturatedPerCubeAmplitude Cup
        (Algsuperdiff.Section3.Disorder.cstar M) M.gamma k) from
      @upperDeepBandTailOrdinaryLane_momentBounds2 (d) (M) (m) (k) (R) (E) (sigma) (Cup) (hsigma0)
        (hsigma) (hEgamma) (hd) (hout) (hCup0) (hObig) (hVbig) (hC0) (hordinary0) (hrare0)
          (hpoint) (hENNRealEq))
  let K : ℝ := probeSharpDeepBandTailTunedRareTracePrefactor d
  have hT : gammaTriangleConst (upperProfileTargetSigma sigma) ≤
      upperAfterBandRareTriangleConst :=
    gammaTriangleConst_upperProfileTarget_le hsigma0 hsigma
  have hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤
      (E : ℝ) := (le_max_right _ _).trans hmax
  have hcstarGamma :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcstarE M.shellPrefix.gamma_pos.le).trans
      (mul_gamma_le_one_of_le_rpow_neg_fifth E.property
        M.shellPrefix.gamma_pos hEgamma)
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact probeSharpDeepBandTailTunedRareTracePrefactor_nonneg hd
  have hrareRaw : rareScale ≤ K * Z := by
    dsimp only [rareScale, C, AV, K]
    rw [vecNormSq_basisVec, mul_one,
      probeMeanGoodWaveConst_eq_dimension_mul_cstarInv,
      probeSharpDeepBandTailTunedRareTracePrefactor]
    have hT0 : 0 ≤ gammaTriangleConst (upperProfileTargetSigma sigma) :=
      gammaTriangleConst_pos.le
    have hW0 : 0 ≤ probeMeanGoodWaveDimensionConst d := by
      rw [probeMeanGoodWaveDimensionConst]
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
        (probeSimplexMeanSensitivityConst_nonneg hd)
    have hR0 : 0 ≤ probeSharpDeepBandTailRareSumConst d :=
      (probeSharpDeepBandTailRareSumConst_pos d).le
    have hZ0 : 0 ≤ Z := by dsimp only [Z]; exact (Real.exp_pos _).le
    have hcstarGamma0 : 0 ≤
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma :=
      mul_nonneg hcstar0 M.shellPrefix.gamma_pos.le
    calc
      (d : ℝ) *
          (probeMeanGoodWaveDimensionConst d *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
            (gammaTriangleConst (upperProfileTargetSigma sigma) *
              (probeSharpDeepBandTailRareSumConst d * M.gamma * Z))) =
        ((d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
          probeMeanGoodWaveDimensionConst d *
          probeSharpDeepBandTailRareSumConst d) *
          ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma) * Z := by ring
      _ ≤ ((d : ℝ) * upperAfterBandRareTriangleConst *
          probeMeanGoodWaveDimensionConst d *
          probeSharpDeepBandTailRareSumConst d) * 1 * Z := by
        gcongr
      _ = _ := by ring
  have hchoice : K + 8 ≤ upperHsepResidualRate * Cup := by
    simpa only [K] using probeSharpDeepBandTailTuned_output_choice hout
  have hrareScale : rareScale ≤
      (Real.exp (-(Cup⁻¹ *
        ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) ^ 8) := by
    refine hrareRaw.trans ?_
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hchoice
  exact ⟨ordinary, rare, ordinaryScale, rareScale,
    hordinary0, hordinaryMeas, hrare0, hrareMeas,
    by simpa only [X, k₀, shift] using hpoint,
    by simpa only [X, k₀, shift] using hENNRealEq,
    by simpa only [X, k₀, shift] using hENNRealDom,
    hordinaryOrlicz, hordinaryScale0, hordinaryScale,
    hrareOrlicz, hrareScale0, hrareScale⟩
end
end Algsuperdiff.Section3.Provider.CoarseEllipticity
