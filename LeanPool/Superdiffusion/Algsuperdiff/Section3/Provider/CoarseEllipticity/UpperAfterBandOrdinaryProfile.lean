/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperSaturatedBlockProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandLayerProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability

/-!
# UpperAfterBandOrdinaryProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Outer coefficient for the ordinary after-band profile

This file restores the exact outer mean coefficient and the squared norm of a
coordinate vector to the normalized deterministic `2` branch of the framed
after-band estimate.  It shows that the resulting strict-descendant layer sum
has the algebraic amplitude consumed by `UpperSaturatedBlockProfile`.

The complementary random `hsep` branch, the depth-zero/root row, and every
other wave, collar, base, and deep-band lane are absent.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney
open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums

noncomputable section

variable {d : ℕ}

/-- Dimension-only coefficient left after extracting the exact
`cstar M⁻¹` factor from `probeMeanGoodWaveConst M`.  This definition does
not assert an estimate for any omitted lane. -/
def probeSharpAfterBandOrdinaryPerCubeConst (d : ℕ) : ℝ :=
  (1920 * simplexCrudeConst d (1 / 4) *
      probeSimplexMeanSensitivityConst d) *
    probeSharpAfterBandOrdinarySumConst d

/-- The unframed after-band carrier at the common collar-band depth. -/
def probeSharpAfterBandTunedBaseTerm
    (M : ABKModel d) (root m : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) : ℝ :=
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  probeSharpAfterBandGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
          (k₀ : ℝ)))) *
    probeSharpAfterBandTerm M root ell k₀ m omega ^ 2

/-- The exact `Gamma_1` scale of the common-depth carrier. -/
def probeSharpAfterBandTunedBaseScale
    (M : ABKModel d) (root m : ℤ) (E : ℝ) (k n : ℕ) : ℝ :=
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  probeSharpAfterBandGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
          (k₀ : ℝ)))) *
    probeSharpAfterBandExactScale M ell k₀ m ^ 2

/-- Dimension-only coefficient of the common-depth ordinary trace scale. -/
def probeSharpAfterBandTunedOrdinaryTracePerCubeConst (d : ℕ) : ℝ :=
  (d : ℝ) * gammaTriangleConst 1 *
    probeSharpAfterBandOrdinaryPerCubeConst d

/-- Dimension-only prefactor of the common-depth rare trace scale. -/
def probeSharpAfterBandTunedRareTracePrefactor (d : ℕ) : ℝ :=
  (d : ℝ) * upperAfterBandRareTriangleConst *
    probeMeanGoodWaveDimensionConst d *
    probeSharpAfterBandRareSumConst d

/-- A single dimension-only gate for the common-depth good after-band split. -/
def probeSharpAfterBandTunedOutputConst (d : ℕ) : ℝ :=
  max (profileAuxiliaryConst d)
    (max (1 + probeSharpAfterBandTunedOrdinaryTracePerCubeConst d)
      (1 + 2 * (probeSharpAfterBandTunedRareTracePrefactor d + 8) *
        upperHsepResidualRate⁻¹))

private abbrev upperAfterBandOrdinaryProfile_momentBounds1_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (_ : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) {sigma : ℝ} (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) (_ : (2 : ℕ) ≤ d),
      let shift : Vec d := triadicCubeShift R;
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let B : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (eta : CutoffSample d) =>
        probeSharpAfterBandTunedBaseTerm M R.scale m (↑E : ℝ) k n eta;
      let Q : CutoffSample d → ℝ := fun (eta : CutoffSample d) => probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) eta;
      let O : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        (2 : ℝ) * B n (translateCutoffSample shift omega);
      let V : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        Q (translateCutoffSample shift omega) * B n (translateCutoffSample shift omega);
      let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀);
      let target : ℝ := min (1 : ℝ) (M.gamma * (↑(k + (1 : ℕ)) : ℝ)) * (3 : ℝ) ^ (M.gamma * (↑(k + (1 : ℕ)) : ℝ));
      let ordinary : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), O n omega);
      let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), V n omega);
      let AO : ℝ := gammaTriangleConst (1 : ℝ) * (probeSharpAfterBandOrdinarySumConst d * target);
      let Z : ℝ := Real.exp (-(upperHsepResidualRate * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
      let AV : ℝ := gammaTriangleConst (upperProfileTargetSigma sigma) * (probeSharpAfterBandRareSumConst d * target * Z);
      ∀ (_ : max (Real.exp (profileAuxiliaryConst d / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
        (_ : M.gamma ≤ (1 / 20 : ℝ)) (_ : ∀ (n : ℕ) (omega : CutoffSample d), (0 : ℝ) ≤ O n omega)
        (_ : ∀ (n : ℕ) (omega : CutoffSample d), (0 : ℝ) ≤ V n omega) (_ : ∀ (n : ℕ), Measurable (O n))
        (_ : ∀ (n : ℕ), Measurable (V n)),
        IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (1 : ℝ))
            (fun (omega : CutoffSample d) => ∑' (n : ℕ), O n omega) AO ∧
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma))
              (fun (omega : CutoffSample d) => ∑' (n : ℕ), V n omega) AV ∧
            (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                Summable fun (n : ℕ) => O n omega) ∧
              (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                  Summable fun (n : ℕ) => V n omega) ∧
                (0 : ℝ) ≤ C ∧
                  (∀ (omega : CutoffSample d), (0 : ℝ) ≤ ordinary omega) ∧
                    (∀ (omega : CutoffSample d), (0 : ℝ) ≤ rare omega) ∧
                      Measurable fun (omega : CutoffSample d) => ∑' (n : ℕ), O n omega

private abbrev upperAfterBandOrdinaryProfile_momentBounds2_statement : Prop :=
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ}
      (_ : (2 : ℕ) ≤ d),
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let shift : Vec d := triadicCubeShift R;
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let B : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (eta : CutoffSample d) =>
        probeSharpAfterBandTunedBaseTerm M R.scale m (↑E : ℝ) k n eta;
      let Q : CutoffSample d → ℝ := fun (eta : CutoffSample d) => probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) eta;
      let O : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        (2 : ℝ) * B n (translateCutoffSample shift omega);
      let V : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        Q (translateCutoffSample shift omega) * B n (translateCutoffSample shift omega);
      let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀);
      let target : ℝ := min (1 : ℝ) (M.gamma * (↑(k + (1 : ℕ)) : ℝ)) * (3 : ℝ) ^ (M.gamma * (↑(k + (1 : ℕ)) : ℝ));
      let ordinary : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), O n omega);
      let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), V n omega);
      let AO : ℝ := gammaTriangleConst (1 : ℝ) * (probeSharpAfterBandOrdinarySumConst d * target);
      let Z : ℝ := Real.exp (-(upperHsepResidualRate * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
      let AV : ℝ := gammaTriangleConst (upperProfileTargetSigma sigma) * (probeSharpAfterBandRareSumConst d * target * Z);
      let ordinaryScale : ℝ := (↑d : ℝ) * (C * AO);
      let rareScale : ℝ := (↑d : ℝ) * (C * AV);
      ∀
        (_ :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (1 : ℝ))
            (fun (omega : CutoffSample d) => ∑' (n : ℕ), O n omega) AO)
        (_ :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma))
            (fun (omega : CutoffSample d) => ∑' (n : ℕ), V n omega) AV)
        (_ :
          ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)), Summable fun (n : ℕ) => O n omega)
        (_ :
          ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)), Summable fun (n : ℕ) => V n omega)
        (_ : (0 : ℝ) ≤ C) (_ : ∀ (omega : CutoffSample d), (0 : ℝ) ≤ ordinary omega)
        (_ : ∀ (omega : CutoffSample d), (0 : ℝ) ≤ rare omega)
        (_ :
          ∀ (omega : CutoffSample d),
            probeSharpAfterBandHsepFactor M R.scale (↑E : ℝ) omega ≤
              (2 : ℝ) + probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) omega)
        (_ :
          ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n
                    (m - (1 : ℤ)) (basisVec j)
                    (fun (eta : CutoffSample d) =>
                      probeSharpAfterBandTerm M R.scale
                          (probeSharpLayerAnchor R.scale bfaProfileB (collarBandMeanDepth M (↑E : ℝ)) n)
                          (collarBandMeanDepth M (↑E : ℝ)) m eta ^
                        (2 : ℕ))
                    (translateCutoffSample (triadicCubeShift R) omega) ≤
              (fun (omega : CutoffSample d) =>
                    (↑d : ℝ) *
                      (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
                        ∑' (n : ℕ),
                          (fun (n : ℕ) (omega : CutoffSample d) =>
                              (2 : ℝ) *
                                (fun (n : ℕ) (eta : CutoffSample d) =>
                                    probeSharpAfterBandTunedBaseTerm M R.scale m (↑E : ℝ) k n eta)
                                  n (translateCutoffSample (triadicCubeShift R) omega))
                            n omega))
                  omega +
                (fun (omega : CutoffSample d) =>
                    (↑d : ℝ) *
                      (probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
                        ∑' (n : ℕ),
                          (fun (n : ℕ) (omega : CutoffSample d) =>
                              (fun (eta : CutoffSample d) => probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) eta)
                                  (translateCutoffSample (triadicCubeShift R) omega) *
                                (fun (n : ℕ) (eta : CutoffSample d) =>
                                    probeSharpAfterBandTunedBaseTerm M R.scale m (↑E : ℝ) k n eta)
                                  n (translateCutoffSample (triadicCubeShift R) omega))
                            n omega))
                  omega),
        (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    (probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                      (fun (eta : CutoffSample d) =>
                        probeSharpAfterBandTerm M R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ m eta ^
                          (2 : ℕ))
                      (translateCutoffSample shift omega)) =
              ENNReal.ofReal
                (∑ j : Fin d,
                  ∑' (n : ℕ),
                    probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                      (fun (eta : CutoffSample d) =>
                        probeSharpAfterBandTerm M R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ m eta ^
                          (2 : ℕ))
                      (translateCutoffSample shift omega))) ∧
          (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
              ∑ j : Fin d,
                  ∑' (n : ℕ),
                    ENNReal.ofReal
                      (probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                        (fun (eta : CutoffSample d) =>
                          probeSharpAfterBandTerm M R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ m eta ^
                            (2 : ℕ))
                        (translateCutoffSample shift omega)) ≤
                ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega)) ∧
            IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (1 : ℝ)) ordinary ordinaryScale ∧
              IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (((1 : ℝ) - sigma) / (3 : ℝ))) rare
                  rareScale ∧
                (0 : ℝ) ≤ target ∧ (0 : ℝ) ≤ ordinaryScale

theorem probeSharpAfterBandOrdinaryPerCubeConst_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpAfterBandOrdinaryPerCubeConst d := by
  rw [probeSharpAfterBandOrdinaryPerCubeConst]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd))
    (by
      rw [probeSharpAfterBandOrdinarySumConst]
      exact div_nonneg
        (probeSharpAfterBandOrdinaryLayerConst_nonneg d)
        (sq_nonneg _))


/-! ## The literal good after-band lane at the common tuned depth -/

private theorem probeSharpAfterBandTunedBaseTerm_nonneg
    (M : ABKModel d) (root m : ℤ) (E : ℝ) (k n : ℕ)
    (omega : CutoffSample d) :
    0 ≤ probeSharpAfterBandTunedBaseTerm M root m E k n omega := by
  rw [probeSharpAfterBandTunedBaseTerm]
  exact mul_nonneg
    (mul_nonneg (probeSharpAfterBandGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _))
    (sq_nonneg _)

private theorem measurable_probeSharpAfterBandTunedBaseTerm
    (M : ABKModel d) (root m : ℤ) (E : ℝ) (k n : ℕ) :
    Measurable (probeSharpAfterBandTunedBaseTerm M root m E k n) := by
  let k₀ := collarBandMeanDepth M E
  have hterm := measurable_probeSharpAfterBandTerm_exactScale M root
    (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ m
  unfold probeSharpAfterBandTunedBaseTerm
  exact measurable_const.mul (hterm.pow_const (2 : ℕ))

private theorem probeSharpAfterBandTunedBaseScale_nonneg
    (M : ABKModel d) (root m : ℤ) (E : ℝ) (k n : ℕ) :
    0 ≤ probeSharpAfterBandTunedBaseScale M root m E k n := by
  rw [probeSharpAfterBandTunedBaseScale]
  exact mul_nonneg
    (mul_nonneg (probeSharpAfterBandGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _))
    (sq_nonneg _)

private theorem collarBandMeanDepth_le_waveBandDepth_one
    (M : ABKModel d) (E : ℝ) :
    collarBandMeanDepth M E ≤ waveBandDepth 1 E M.gamma := by
  rw [collarBandMeanDepth, waveBandDepth, waveBandDepth]
  apply Nat.ceil_mono
  have hA : 0 ≤ (E ^ 2)⁻¹ * M.gamma⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (sq_nonneg E))
      (inv_nonneg.mpr M.shellPrefix.gamma_pos.le)
  calc
    collarBandMeanDepthCoeff d * (E ^ 2)⁻¹ * M.gamma⁻¹ =
        collarBandMeanDepthCoeff d * ((E ^ 2)⁻¹ * M.gamma⁻¹) := by ring
    _ ≤ 1 * ((E ^ 2)⁻¹ * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_right (collarBandMeanDepthCoeff_le_one d) hA
    _ = 1 * (E ^ 2)⁻¹ * M.gamma⁻¹ := by ring

/-- Exact normalization of the common-depth base scale. -/
private theorem probeSharpAfterBandTunedBaseScale_eq_profileHalf
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) :
    probeSharpAfterBandTunedBaseScale M R.scale m E k n =
      5 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
        Real.sqrt (probeSharpLayerMassEnvelope d n) *
        min 1 (M.gamma *
          (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) *
        (3 : ℝ) ^ (M.gamma *
          (2 + (k : ℝ) + (n : ℝ) +
            (bfaAfterBandLayerCeil n : ℝ) +
            (collarBandMeanDepth M E : ℝ))) := by
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let a := bfaAfterBandLayerCeil n
  let D : ℝ := (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ)
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hL : ell + (k₀ : ℤ) < m := by
    dsimp only [ell]
    rw [probeSharpLayerAnchor, hscale]
    omega
  have hgap :
      (m : ℝ) - (((ell + (k₀ : ℤ) : ℤ) : ℝ)) =
        1 + (k : ℝ) + (n : ℝ) + (a : ℝ) := by
    dsimp only [ell, a, bfaAfterBandLayerCeil]
    rw [probeSharpLayerAnchor, hscale]
    push_cast
    ring
  have hheight :
      (m : ℝ) - (ell : ℝ) =
        1 + (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ) := by
    dsimp only [ell, a, bfaAfterBandLayerCeil]
    rw [probeSharpLayerAnchor, hscale]
    push_cast
    ring
  have hpow :
      (3 : ℝ) ^ (-(M.gamma * D)) *
          (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ))) =
        (3 : ℝ) ^ (M.gamma *
          (2 + (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hheight]
    congr 1
    dsimp only [D]
    ring
  rw [probeSharpAfterBandTunedBaseScale,
    probeSharpAfterBandExactScale_sq_eq_min M hL]
  change
    probeSharpAfterBandGoodMassCoeff d n * (3 : ℝ) ^ (-(M.gamma * D)) *
        (waveSharpUpperConst d ^ 2 *
          min 1
            (M.gamma * ((m : ℝ) - (((ell + (k₀ : ℤ) : ℤ) : ℝ)))) *
          (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ)))) = _
  rw [hgap]
  calc
    _ = probeSharpAfterBandGoodMassCoeff d n * waveSharpUpperConst d ^ 2 *
          min 1 (M.gamma *
            (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
          ((3 : ℝ) ^ (-(M.gamma * D)) *
            (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ)))) := by ring
    _ = probeSharpAfterBandGoodMassCoeff d n * waveSharpUpperConst d ^ 2 *
          min 1 (M.gamma *
            (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
          (3 : ℝ) ^ (M.gamma *
            (2 + (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) := by
      rw [hpow]
    _ = _ := by
      rw [probeSharpAfterBandGoodMassCoeff]
      dsimp only [a, k₀]
      ring

private theorem probeSharpAfterBandTunedBaseScale_le_old
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) :
    probeSharpAfterBandTunedBaseScale M R.scale m E k n ≤
      probeSharpAfterBandBaseGoodMassScale M R.scale m E k n := by
  rw [probeSharpAfterBandTunedBaseScale_eq_profileHalf M hR,
    probeSharpAfterBandBaseGoodMassScale_eq_profileHalf M hR]
  let A : ℝ := 5 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
    Real.sqrt (probeSharpLayerMassEnvelope d n) *
    min 1 (M.gamma *
      (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)))
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hgap : 0 ≤
        1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) := by
      positivity
    have hmin : 0 ≤ min 1 (M.gamma *
        (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) :=
      le_min zero_le_one (mul_nonneg M.shellPrefix.gamma_pos.le hgap)
    positivity
  have hk₀ : (collarBandMeanDepth M E : ℝ) ≤
      (waveBandDepth 1 E M.gamma : ℝ) := by
    exact_mod_cast collarBandMeanDepth_le_waveBandDepth_one M E
  have hexponent : M.gamma *
        (2 + (k : ℝ) + (n : ℝ) +
          (bfaAfterBandLayerCeil n : ℝ) +
          (collarBandMeanDepth M E : ℝ)) ≤
      M.gamma *
        (2 + (k : ℝ) + (n : ℝ) +
          (bfaAfterBandLayerCeil n : ℝ) +
          (waveBandDepth 1 E M.gamma : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) M.shellPrefix.gamma_pos.le
  change A * (3 : ℝ) ^ _ ≤ A * (3 : ℝ) ^ _
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hA

private theorem two_mul_probeSharpAfterBandTunedBaseScale_le
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) :
    2 * probeSharpAfterBandTunedBaseScale M R.scale m E k n ≤
      probeSharpAfterBandOrdinaryGoodMassLayer M E k n := by
  calc
    2 * probeSharpAfterBandTunedBaseScale M R.scale m E k n ≤
        2 * probeSharpAfterBandBaseGoodMassScale M R.scale m E k n :=
      mul_le_mul_of_nonneg_left
        (probeSharpAfterBandTunedBaseScale_le_old M hR E n) (by norm_num)
    _ = probeSharpAfterBandOrdinaryGoodMassLayer M E k n :=
      two_mul_probeSharpAfterBandBaseGoodMassScale_eq_ordinary M hR E n

private theorem isBigOWith_gammaSigma_one_probeSharpAfterBandTunedBaseTerm
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (probeSharpAfterBandTunedBaseTerm M R.scale m E k n)
      (probeSharpAfterBandTunedBaseScale M R.scale m E k n) := by
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hL : ell + (k₀ : ℤ) < m := by
    dsimp only [ell]
    rw [probeSharpLayerAnchor, hscale]
    omega
  have hc : 0 ≤ probeSharpAfterBandGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
          (k₀ : ℝ)))) :=
    mul_nonneg (probeSharpAfterBandGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _)
  have hbase :=
    (isBigOWith_gammaSigma_one_probeSharpAfterBandTerm_sq_exactScale
      (m := R.scale) (ell := ell) (L := m) (k₀ := k₀) M hL).const_mul hc
  unfold probeSharpAfterBandTunedBaseTerm probeSharpAfterBandTunedBaseScale
  exact hbase

/-- The literal common-depth good after-band summand equals its outer
coefficient times the separated hsep factor and tuned base carrier. -/
private theorem probeSharpFramedGoodWavePart_afterBand_tuned_eq
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedGoodWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1) (basisVec j)
        (fun eta => probeSharpAfterBandTerm M R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M E) n)
          (collarBandMeanDepth M E) m eta ^ 2) omega =
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j)) *
        (probeSharpAfterBandHsepFactor M R.scale E omega *
          probeSharpAfterBandTunedBaseTerm M R.scale m E k n omega) := by
  let k₀ := collarBandMeanDepth M E
  let D : ℝ := (k : ℝ) + (n : ℝ) +
    (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ)
  let C : ℝ := probeSharpAfterBandGoodMassCoeff d n
  let T : ℝ := probeSharpAfterBandTerm M R.scale
    (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ m omega ^ 2
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
  rw [probeSharpFramedGoodWavePart, probeSharpAfterBandTunedBaseTerm,
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
  rw [probeSharpAfterBandGoodMassCoeff]
  ring

private theorem probeSharpAfterBandOrdinaryGoodMassLayer_pos_tuned
    (M : ABKModel d) (E : ℝ) (k n : ℕ) :
    0 < probeSharpAfterBandOrdinaryGoodMassLayer M E k n := by
  have hd : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) M.shellPrefix.dimension
  have hmass : 0 < probeSharpLayerMassEnvelope d n := by
    rw [probeSharpLayerMassEnvelope]
    positivity
  have hwave : 0 < waveSharpUpperConst d := by
    have hexp : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
    have hmoment : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
    have htriangle : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    have hgeom : 0 <
        Algsuperdiff.Section3.Provider.Stream.geometricConcentrationConst :=
      Algsuperdiff.Section3.Provider.Stream.geometricConcentrationConst_pos
    have hdsq : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos hd
    rw [waveSharpUpperConst]
    positivity
  have hgap : 0 <
      1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) := by
    positivity
  have hmin : 0 < min 1 (M.gamma *
      (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) :=
    lt_min zero_lt_one (mul_pos M.shellPrefix.gamma_pos hgap)
  rw [probeSharpAfterBandOrdinaryGoodMassLayer]
  positivity

private theorem summable_probeSharpAfterBandOrdinaryGoodMassLayer_tuned
    (M : ABKModel d) {E : ℝ} (hE : 1 ≤ E)
    (hgamma20 : M.gamma ≤ 1 / 20) (k : ℕ) :
    Summable fun n : ℕ =>
      probeSharpAfterBandOrdinaryGoodMassLayer M E k n := by
  let target : ℝ := min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
    (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))
  let C : ℝ := probeSharpAfterBandOrdinaryLayerConst d
  have hterm : ∀ n : ℕ,
      probeSharpAfterBandOrdinaryGoodMassLayer M E k n ≤
        C * (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) * target := by
    intro n
    exact probeSharpAfterBandOrdinaryGoodMassLayer_le M hE hgamma20 k n
  have hright : Summable fun n : ℕ =>
      C * (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) * target :=
    (summable_succ_mul_whitneyDecayRatio.mul_left C).mul_right target
  exact Summable.of_nonneg_of_le
    (fun n => probeSharpAfterBandOrdinaryGoodMassLayer_nonneg M E k n)
    hterm hright

private theorem isBigOWith_gammaSigma_one_tunedAfterBandOrdinaryLayer
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (fun omega =>
        2 * probeSharpAfterBandTunedBaseTerm M R.scale m E k n omega)
      (probeSharpAfterBandOrdinaryGoodMassLayer M E k n) := by
  have hbase :=
    (isBigOWith_gammaSigma_one_probeSharpAfterBandTunedBaseTerm
      M hR E n).const_mul (by norm_num : (0 : ℝ) ≤ 2)
  exact hbase.mono_scale
    (two_mul_probeSharpAfterBandTunedBaseScale_le M hR E n)

private theorem isBigOWith_upperProfileTarget_tunedAfterBandRareLayer
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hgamma20 : M.gamma ≤ 1 / 20) (n : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega =>
        probeSharpAfterBandHsepResidual M R.scale (E : ℝ) omega *
          probeSharpAfterBandTunedBaseTerm
            M R.scale m (E : ℝ) k n omega)
      (probeSharpAfterBandRareGoodMassLayerBound M (E : ℝ) k n) := by
  obtain ⟨_hpoint, hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hS hsigma0 hsigma hmax hEgamma
  have hbase :=
    isBigOWith_gammaSigma_one_probeSharpAfterBandTunedBaseTerm
      M hR (E : ℝ) n
  have hproduct := isBigOWith_upperProfileTarget_hsep_mul_one
    hsigma0 hsigma (upperHsepResidualScale_pos sigma M.gamma).le
    (probeSharpAfterBandTunedBaseScale_nonneg
      M R.scale m (E : ℝ) k n)
    (probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ))
    (probeSharpAfterBandTunedBaseTerm_nonneg
      M R.scale m (E : ℝ) k n)
    (by simpa only [upperHsepResidualScale] using hresidual) hbase
  have hscaleOld :
      HCPolySupport.Book.Ch04.gammaProductConst
          (upperProfileHsepTau sigma) 1 *
          upperHsepResidualScale sigma M.gamma *
          probeSharpAfterBandTunedBaseScale M R.scale m (E : ℝ) k n ≤
        HCPolySupport.Book.Ch04.gammaProductConst
          (upperProfileHsepTau sigma) 1 *
          upperHsepResidualScale sigma M.gamma *
          probeSharpAfterBandBaseGoodMassScale
            M R.scale m (E : ℝ) k n := by
    exact mul_le_mul_of_nonneg_left
      (probeSharpAfterBandTunedBaseScale_le_old M hR (E : ℝ) n)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (upperHsepResidualScale_pos sigma M.gamma).le)
  have hold := probeSharpAfterBandRareGoodMassScale_le_layerBound
    M hR E.property hgamma20 hsigma0 hsigma n
  refine hproduct.mono_scale (hscaleOld.trans ?_)
  simpa only [probeSharpAfterBandRareGoodMassScale,
    upperHsepResidualScale] using hold

private theorem probeSharpAfterBandTunedOrdinaryTracePerCubeConst_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpAfterBandTunedOrdinaryTracePerCubeConst d := by
  rw [probeSharpAfterBandTunedOrdinaryTracePerCubeConst]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg d) gammaTriangleConst_pos.le)
    (probeSharpAfterBandOrdinaryPerCubeConst_nonneg hd)

private theorem probeSharpAfterBandOrdinarySumConst_nonneg_tuned (d : ℕ) :
    0 ≤ probeSharpAfterBandOrdinarySumConst d := by
  rw [probeSharpAfterBandOrdinarySumConst]
  exact div_nonneg (probeSharpAfterBandOrdinaryLayerConst_nonneg d)
    (sq_nonneg _)

private theorem probeSharpAfterBandTunedRareTracePrefactor_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpAfterBandTunedRareTracePrefactor d := by
  rw [probeSharpAfterBandTunedRareTracePrefactor]
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
    (probeSharpAfterBandRareSumConst_pos d).le

theorem probeSharpAfterBandTunedOutputConst_pos
    (hd : 2 ≤ d) : 0 < probeSharpAfterBandTunedOutputConst d := by
  have hordinary :=
    probeSharpAfterBandTunedOrdinaryTracePerCubeConst_nonneg hd
  rw [probeSharpAfterBandTunedOutputConst]
  exact lt_of_lt_of_le (by linarith : 0 <
      1 + probeSharpAfterBandTunedOrdinaryTracePerCubeConst d)
    ((le_max_left _ _).trans (le_max_right _ _))

private theorem cstarInv_mul_exp_neg_afterBandRate_le_halfRate
    {cstarInv rate E X : ℝ} (hrate : 0 < rate)
    (hE : 1 ≤ E) (hlarge : 2 * rate⁻¹ ≤ E)
    (hX : E ^ 3 ≤ X) (hcstarInvE : cstarInv ≤ E) :
    cstarInv * Real.exp (-(rate * X)) ≤
      Real.exp (-((rate / 2) * X)) := by
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  have hrateE : 2 ≤ rate * E := by
    have hmul := mul_le_mul_of_nonneg_left hlarge hrate.le
    have hcancel : rate * (2 * rate⁻¹) = 2 := by
      field_simp [ne_of_gt hrate]
    rw [hcancel] at hmul
    simpa [mul_comm] using hmul
  have hEsq : E ≤ E ^ 2 := by
    linarith only [mul_nonneg hE0 (sub_nonneg.mpr hE)]
  have hrateCube : 2 * E ^ 2 ≤ rate * E ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hrateE (sq_nonneg E)
    linarith only [hmul]
  have hEhalfCube : E ≤ (rate / 2) * E ^ 3 := by
    linarith only [hrateCube, hEsq]
  have hhalf0 : 0 ≤ rate / 2 := div_nonneg hrate.le (by norm_num)
  have hEhalfX : E ≤ (rate / 2) * X :=
    hEhalfCube.trans (mul_le_mul_of_nonneg_left hX hhalf0)
  have hcstarExp : cstarInv ≤ Real.exp ((rate / 2) * X) :=
    hcstarInvE.trans (hEhalfX.trans (by
      linarith [Real.add_one_le_exp ((rate / 2) * X)]))
  calc
    _ ≤ Real.exp ((rate / 2) * X) * Real.exp (-(rate * X)) :=
      mul_le_mul_of_nonneg_right hcstarExp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; exact congrArg Real.exp (by ring)

private theorem afterBandGoodTrace_pointwiseSplit :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d},
      R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) →
        ∀ {E : { E : ℝ // (1 : ℝ) ≤ E }},
          (2 : ℕ) ≤ d →
            let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
            let shift : Vec d := triadicCubeShift R;
            ∀ (j₀ : Fin d),
              let B : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (eta : CutoffSample d) =>
                probeSharpAfterBandTunedBaseTerm M R.scale m (↑E : ℝ) k n eta;
              let Q : CutoffSample d → ℝ := fun (eta : CutoffSample d) =>
                probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) eta;
              let O : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
                (2 : ℝ) * B n (translateCutoffSample shift omega);
              let V : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
                Q (translateCutoffSample shift omega) * B n (translateCutoffSample shift omega);
              let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀);
              let ordinary : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), O n omega);
              let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) => (↑d : ℝ) * (C * ∑' (n : ℕ), V n omega);
              (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                  Summable fun (n : ℕ) => O n omega) →
                (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                    Summable fun (n : ℕ) => V n omega) →
                  (∀ (omega : CutoffSample d),
                      probeSharpAfterBandHsepFactor M R.scale (↑E : ℝ) omega ≤
                        (2 : ℝ) + probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) omega) →
                    ∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
                      ∑ j : Fin d,
                          ∑' (n : ℕ),
                            probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec j)
                              (fun (eta : CutoffSample d) =>
                                probeSharpAfterBandTerm M R.scale (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ m
                                    eta ^
                                  (2 : ℕ))
                              (translateCutoffSample shift omega) ≤
                        ordinary omega + rare omega := by
  intro d M m k R hR E hd k₀ shift _ B Q O V C ordinary rare hOsumAE hVsumAE hsepPoint
  filter_upwards [hOsumAE, hVsumAE] with omega hOsum hVsum
  let eta := translateCutoffSample shift omega
  let X : Fin d → ℕ → ℝ := fun j n =>
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
      k₀ n (m - 1) (basisVec j)
      (fun zeta => probeSharpAfterBandTerm M R.scale
        (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
        k₀ m zeta ^ 2) eta
  have hcoord (j : Fin d) : (∑' n, X j n) ≤
      C * (∑' n, O n omega) + C * (∑' n, V n omega) := by
    let Cj : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
    let Oj : ℕ → ℝ := fun n => Cj * O n omega
    let Vj : ℕ → ℝ := fun n => Cj * V n omega
    have hCj : 0 ≤ Cj := mul_nonneg
      (probeMeanGoodWaveConst_nonneg hd M)
      (vecNormSq_nonneg (basisVec j))
    have hOj : Summable Oj := hOsum.mul_left Cj
    have hVj : Summable Vj := hVsum.mul_left Cj
    have hX0 : ∀ n, 0 ≤ X j n := fun n =>
      probeSharpFramedGoodWavePart_nonneg hd M R.scale (E : ℝ)
        bfaProfileB k₀ n (m - 1) (basisVec j) (fun _ => sq_nonneg _) eta
    have hXle : ∀ n, X j n ≤ Oj n + Vj n := by
      intro n
      dsimp only [X]
      rw [probeSharpFramedGoodWavePart_afterBand_tuned_eq
        M hR (E : ℝ) n j eta]
      have hB0 := probeSharpAfterBandTunedBaseTerm_nonneg
        M R.scale m (E : ℝ) k n eta
      calc
        Cj * (probeSharpAfterBandHsepFactor M R.scale (E : ℝ) eta *
            B n eta) ≤
          Cj * ((2 + Q eta) * B n eta) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hsepPoint eta) hB0) hCj
        _ = Oj n + Vj n := by
          simp only [Oj, Vj, O, V, B, Q, eta, Cj]
          ring
    have hXsum : Summable (X j) :=
      Summable.of_nonneg_of_le hX0 hXle (hOj.add hVj)
    calc
      ∑' n, X j n ≤ ∑' n, (Oj n + Vj n) :=
        Summable.tsum_le_tsum hXle hXsum (hOj.add hVj)
      _ = (∑' n, Oj n) + ∑' n, Vj n := hOj.tsum_add hVj
      _ = C * (∑' n, O n omega) + C * (∑' n, V n omega) := by
        simp only [Oj, Vj, tsum_mul_left]
        rw [show Cj = C by
          simp only [Cj, C, vecNormSq_basisVec]]
  calc
    (∑ j : Fin d, ∑' n : ℕ, X j n) ≤
        ∑ _j : Fin d,
          (C * (∑' n, O n omega) + C * (∑' n, V n omega)) :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = ordinary omega + rare omega := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ordinary, rare]
      ring

private theorem upperAfterBandOrdinaryProfile_estimate1 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (hR : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      (hS : Frozen.Section3.inductionState M (m - (1 : ℤ)) E) {sigma : ℝ} (hsigma0 : (0 : ℝ) < sigma)
      (hsigma : sigma ≤ (1 / 2 : ℝ)) (hEgamma : (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))),
      let shift : Vec d := triadicCubeShift R;
      let B : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (eta : CutoffSample d) =>
        probeSharpAfterBandTunedBaseTerm M R.scale m (↑E : ℝ) k n eta;
      let Q : CutoffSample d → ℝ := fun (eta : CutoffSample d) => probeSharpAfterBandHsepResidual M R.scale (↑E : ℝ) eta;
      let V : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        Q (translateCutoffSample shift omega) * B n (translateCutoffSample shift omega);
      ∀ (hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
        (hgamma20 : M.gamma ≤ (1 / 20 : ℝ)) (n : ℕ),
        IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (upperProfileTargetSigma sigma)) (V n)
          (probeSharpAfterBandRareGoodMassLayerBound M (↑E : ℝ) k n) := by
  intro d M m k R hR E hS sigma hsigma0 hsigma hEgamma shift B instance14 V hmaxAux hgamma20 n
  have hcenter := isBigOWith_upperProfileTarget_tunedAfterBandRareLayer
    M hR hS hsigma0 hsigma hmaxAux hEgamma hgamma20 n
  exact Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
    M shift
    (show Measurable (fun omega =>
        probeSharpAfterBandHsepResidual M R.scale (E : ℝ) omega *
          probeSharpAfterBandTunedBaseTerm M R.scale m (E : ℝ) k n omega) from
      (measurable_probeSharpAfterBandHsepResidual M R.scale (E : ℝ)).mul
        (measurable_probeSharpAfterBandTunedBaseTerm
          M R.scale m (E : ℝ) k n))
    hcenter

private theorem upperAfterBandOrdinaryProfile_momentBounds1 : upperAfterBandOrdinaryProfile_momentBounds1_statement := by
  intro d M m k R hR E hS sigma hsigma0 hsigma hEgamma hd shift j₀ B _ O V C target ordinary rare AO Z AV hmaxAux hgamma20 hO0 hV0 hOmeas hVmeas
  have hOterm : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (O n)
      (probeSharpAfterBandOrdinaryGoodMassLayer M (E : ℝ) k n) := by
    intro n
    have hcenter :=
      isBigOWith_gammaSigma_one_tunedAfterBandOrdinaryLayer
        M hR (E : ℝ) n
    exact Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift
      (measurable_probeSharpAfterBandTunedBaseTerm
        M R.scale m (E : ℝ) k n |>.const_mul 2)
      (by simpa only [O, B, shift] using hcenter)
  have hVterm : ∀ n, IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma)) (V n)
      (probeSharpAfterBandRareGoodMassLayerBound M (E : ℝ) k n)  := @upperAfterBandOrdinaryProfile_estimate1 (d) (M) (m) (k) (R) (hR) (E) (hS) (sigma) (hsigma0) (hsigma) (hEgamma) (hmaxAux) (hgamma20)
  have hObig : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (fun omega => ∑' n, O n omega) AO := by
    have h := Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
      (μ := (cutoffSampleLaw M).toMeasure) (σ := 1)
      (X := O) (a := fun n =>
        probeSharpAfterBandOrdinaryGoodMassLayer M (E : ℝ) k n)
      one_pos hO0 hOmeas
      (probeSharpAfterBandOrdinaryGoodMassLayer_pos_tuned M (E : ℝ) k)
      (summable_probeSharpAfterBandOrdinaryGoodMassLayer_tuned
        M E.property hgamma20 k)
      hOterm
      (tsum_probeSharpAfterBandOrdinaryGoodMassLayer_le
        M E.property hgamma20 k)
    simpa only [AO, target] using h
  have hVbig : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => ∑' n, V n omega) AV := by
    have h := Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
      (μ := (cutoffSampleLaw M).toMeasure)
      (σ := upperProfileTargetSigma sigma)
      (X := V) (a := probeSharpAfterBandRareGoodMassLayerBound
        M (E : ℝ) k)
      (upperProfileTargetSigma_pos hsigma0 hsigma) hV0 hVmeas
      (probeSharpAfterBandRareGoodMassLayerBound_pos M (E : ℝ) k)
      (summable_probeSharpAfterBandRareGoodMassLayerBound M (E : ℝ) k)
      hVterm
      (by rw [tsum_probeSharpAfterBandRareGoodMassLayerBound_eq])
    simpa only [AV, target, Z] using h
  have hOsumAE : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => O n omega :=
    Algsuperdiff.Section3.Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      one_pos hO0 (fun n => (hOmeas n).aemeasurable)
      (probeSharpAfterBandOrdinaryGoodMassLayer_pos_tuned M (E : ℝ) k)
      (summable_probeSharpAfterBandOrdinaryGoodMassLayer_tuned
        M E.property hgamma20 k) hOterm
  have hVsumAE : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => V n omega :=
    Algsuperdiff.Section3.Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      (upperProfileTargetSigma_pos hsigma0 hsigma) hV0
      (fun n => (hVmeas n).aemeasurable)
      (probeSharpAfterBandRareGoodMassLayerBound_pos M (E : ℝ) k)
      (summable_probeSharpAfterBandRareGoodMassLayerBound M (E : ℝ) k) hVterm
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
    have hnn : Measurable (fun omega =>
        ((∑' n, (O n omega).toNNReal : NNReal) : ℝ)) :=
      (Measurable.tsum fun n => (hOmeas n).real_toNNReal).coe_nnreal_real
    convert hnn using 1
    funext omega
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by
      rw [Real.toNNReal_of_nonneg (hO0 n omega)]
      rfl
  exact ⟨hObig, hVbig, hOsumAE, hVsumAE, hC0, hordinary0, hrare0, hOsumMeas⟩

private theorem upperAfterBandOrdinaryProfile_momentBounds2 : upperAfterBandOrdinaryProfile_momentBounds2_statement := by
  intro d M m k R hR E sigma hd k₀ shift _ B Q O V _ target ordinary rare AO _ _ ordinaryScale rareScale hObig hVbig hOsumAE hVsumAE hC0 hordinary0 hrare0 hsepPoint hpoint
  have hENNRealEq : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j)
          (fun eta => probeSharpAfterBandTerm M R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
            k₀ m eta ^ 2)
          (translateCutoffSample shift omega))) =
        ENNReal.ofReal
          (∑ j : Fin d, ∑' n : ℕ,
            probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              k₀ n (m - 1) (basisVec j)
              (fun eta => probeSharpAfterBandTerm M R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
                k₀ m eta ^ 2)
              (translateCutoffSample shift omega)) := by
    filter_upwards [hOsumAE, hVsumAE] with omega hOsum hVsum
    let eta := translateCutoffSample shift omega
    let Xlane : Fin d → ℕ → ℝ := fun j n =>
      probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
        k₀ n (m - 1) (basisVec j)
        (fun zeta => probeSharpAfterBandTerm M R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
          k₀ m zeta ^ 2) eta
    have hX0 (j : Fin d) : ∀ n, 0 ≤ Xlane j n := fun n =>
      probeSharpFramedGoodWavePart_nonneg hd M R.scale (E : ℝ)
        bfaProfileB k₀ n (m - 1) (basisVec j) (fun _ => sq_nonneg _) eta
    have hXsum (j : Fin d) : Summable (Xlane j) := by
      let Cj : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
      let Oj : ℕ → ℝ := fun n => Cj * O n omega
      let Vj : ℕ → ℝ := fun n => Cj * V n omega
      have hCj : 0 ≤ Cj := mul_nonneg
        (probeMeanGoodWaveConst_nonneg hd M)
        (vecNormSq_nonneg (basisVec j))
      have hOj : Summable Oj := hOsum.mul_left Cj
      have hVj : Summable Vj := hVsum.mul_left Cj
      have hXle : ∀ n, Xlane j n ≤ Oj n + Vj n := by
        intro n
        dsimp only [Xlane]
        rw [probeSharpFramedGoodWavePart_afterBand_tuned_eq
          M hR (E : ℝ) n j eta]
        have hB0 := probeSharpAfterBandTunedBaseTerm_nonneg
          M R.scale m (E : ℝ) k n eta
        calc
          Cj * (probeSharpAfterBandHsepFactor M R.scale (E : ℝ) eta *
              B n eta) ≤ Cj * ((2 + Q eta) * B n eta) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hsepPoint eta) hB0) hCj
          _ = Oj n + Vj n := by
            simp only [Oj, Vj, O, V, B, Q, eta, Cj]
            ring
      exact Summable.of_nonneg_of_le (hX0 j) hXle (hOj.add hVj)
    change (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal (Xlane j n)) =
      ENNReal.ofReal (∑ j : Fin d, ∑' n : ℕ, Xlane j n)
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun j _ => tsum_nonneg fun n => hX0 j n)]
    exact Finset.sum_congr rfl fun j _ =>
      (ENNReal.ofReal_tsum_of_nonneg (hX0 j) (hXsum j)).symm
  have hENNRealDom : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j)
          (fun eta => probeSharpAfterBandTerm M R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
            k₀ m eta ^ 2)
          (translateCutoffSample shift omega))) ≤
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
    simpa only [rare, rareScale, upperProfileTargetSigma] using
      (hVbig.const_mul hC0).const_mul (Nat.cast_nonneg d)
  have htarget0 : 0 ≤ target := by
    dsimp only [target]
    exact mul_nonneg
      (le_min zero_le_one
        (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity)))
      (Real.rpow_nonneg (by norm_num) _)
  have hordinaryScale0 : 0 ≤ ordinaryScale := by
    dsimp only [ordinaryScale, AO, target]
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg hC0
        (mul_nonneg gammaTriangleConst_pos.le
          (mul_nonneg
            (probeSharpAfterBandOrdinarySumConst_nonneg_tuned d)
            (mul_nonneg
              (le_min zero_le_one
                (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity)))
              (Real.rpow_nonneg (by norm_num) _)))))
  exact ⟨hENNRealEq, hENNRealDom, hordinaryOrlicz, hrareOrlicz, htarget0, hordinaryScale0⟩

private theorem upperAfterBandOrdinaryProfile_comparisonBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) {k : ℕ} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma Cup : ℝ} (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : (2 : ℕ) ≤ d),
      let j₀ : Fin d := ⟨(0 : ℕ), (by positivity)⟩;
      let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀);
      let target : ℝ := min (1 : ℝ) (M.gamma * (↑(k + (1 : ℕ)) : ℝ)) * (3 : ℝ) ^ (M.gamma * (↑(k + (1 : ℕ)) : ℝ));
      let Z : ℝ := Real.exp (-(upperHsepResidualRate * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
      let AV : ℝ := gammaTriangleConst (upperProfileTargetSigma sigma) * (probeSharpAfterBandRareSumConst d * target * Z);
      let rareScale : ℝ := (↑d : ℝ) * (C * AV);
      ∀ (_ : (0 : ℝ) ≤ target) (_ : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹),
        let K : ℝ := probeSharpAfterBandTunedRareTracePrefactor d;
        let X : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
        let eps : ℝ := Real.exp (-(Cup⁻¹ * X));
        ∀ (_ : (0 : ℝ) ≤ K) (_ : K * ((Disorder.cstar M)⁻¹ * Z) ≤ eps ^ (8 : ℕ)),
          let profilePow : ℝ := (3 : ℝ) ^ (M.gamma * (↑(k + (1 : ℕ)) : ℝ));
          rareScale ≤ profilePow * eps ^ (8 : ℕ) := by
  intro d M k _ sigma _ hsigma0 hsigma hd _ C target Z AV rareScale htarget0 hcstar0 K _ eps hK0 hKreserve profilePow
  have hprofilePow0 : 0 ≤ profilePow := by
    dsimp only [profilePow]
    exact Real.rpow_nonneg (by norm_num) _
  have hT : gammaTriangleConst (upperProfileTargetSigma sigma) ≤
      upperAfterBandRareTriangleConst :=
    gammaTriangleConst_upperProfileTarget_le hsigma0 hsigma
  have hT0 : 0 ≤ gammaTriangleConst (upperProfileTargetSigma sigma) :=
    gammaTriangleConst_pos.le
  have hW0 : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  have hRsum0 : 0 ≤ probeSharpAfterBandRareSumConst d :=
    (probeSharpAfterBandRareSumConst_pos d).le
  have hZ0 : 0 ≤ Z := by dsimp only [Z]; exact (Real.exp_pos _).le
  have hmin : min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) ≤ 1 :=
    min_le_left _ _
  have htarget : target ≤ profilePow := by
    dsimp only [target, profilePow]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hmin hprofilePow0
  have hcoef : (d : ℝ) *
        gammaTriangleConst (upperProfileTargetSigma sigma) *
        probeMeanGoodWaveDimensionConst d *
        probeSharpAfterBandRareSumConst d ≤ K := by
    dsimp only [K, probeSharpAfterBandTunedRareTracePrefactor]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg d)) hW0) hRsum0
  have hcoef0 : 0 ≤ (d : ℝ) *
      gammaTriangleConst (upperProfileTargetSigma sigma) *
      probeMeanGoodWaveDimensionConst d *
      probeSharpAfterBandRareSumConst d :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg d) hT0) hW0) hRsum0
  have hrareRaw : rareScale ≤
      profilePow *
        (K * ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z)) := by
    dsimp only [rareScale, C, AV]
    rw [vecNormSq_basisVec, mul_one,
      probeMeanGoodWaveConst_eq_dimension_mul_cstarInv]
    calc
      (d : ℝ) *
          (probeMeanGoodWaveDimensionConst d *
            (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
            (gammaTriangleConst (upperProfileTargetSigma sigma) *
              (probeSharpAfterBandRareSumConst d * target * Z))) =
        ((d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
          probeMeanGoodWaveDimensionConst d *
          probeSharpAfterBandRareSumConst d) *
          ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * target * Z) := by ring
      _ ≤ K * ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * target * Z) :=
        mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (mul_nonneg hcstar0 htarget0) hZ0)
      _ ≤ K * ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          profilePow * Z) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htarget hcstar0) hZ0) hK0
      _ = profilePow *
          (K * ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z)) := by ring
  have hrareScale : rareScale ≤ profilePow * eps ^ 8 :=
    hrareRaw.trans (mul_le_mul_of_nonneg_left hKreserve hprofilePow0)
  exact hrareScale

private theorem upperAfterBandOrdinaryProfile_comparisonBounds2 :
    ∀ {d : ℕ} (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma Cup : ℝ} (_ : (0 : ℝ) < sigma)
      (_ : sigma ≤ (1 / 2 : ℝ)) (_ : max (Real.exp (Cup / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ))
      (_ : probeSharpAfterBandTunedOutputConst d ≤ Cup) (_ : (2 : ℕ) ≤ d),
      let Z : ℝ := Real.exp (-(upperHsepResidualRate * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)));
      ∀ (_ : (0 : ℝ) < Cup) (_ : M.gamma ≤ (↑E : ℝ) ^ (-5 : ℤ)),
        let K : ℝ := probeSharpAfterBandTunedRareTracePrefactor d;
        let X : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
        let eps : ℝ := Real.exp (-(Cup⁻¹ * X));
        (0 : ℝ) ≤ K ∧ K * ((Disorder.cstar M)⁻¹ * Z) ≤ eps ^ (8 : ℕ) := by
  intro _ M E sigma Cup hsigma0 hsigma hmax houtput hd Z hCup0 hgammaZ K X eps
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact probeSharpAfterBandTunedRareTracePrefactor_nonneg hd
  have hrareBranch :
      1 + 2 * (K + 8) * upperHsepResidualRate⁻¹ ≤ Cup := by
    simpa only [K] using
      ((le_max_right _ _).trans (le_max_right _ _)).trans houtput
  have hlargeChoice : 2 * upperHsepResidualRate⁻¹ ≤ Cup := by
    have hinv : 0 < upperHsepResidualRate⁻¹ :=
      inv_pos.mpr upperHsepResidualRate_pos
    linarith only [hrareBranch, hinv.le, mul_nonneg hK0 hinv.le]
  have hprefChoice : K + 8 ≤ (upperHsepResidualRate / 2) * Cup := by
    have hhalf : 0 ≤ upperHsepResidualRate / 2 :=
      div_nonneg upperHsepResidualRate_pos.le (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hrareBranch hhalf
    have hcancel : (upperHsepResidualRate / 2) *
        (2 * (K + 8) * upperHsepResidualRate⁻¹) = K + 8 := by
      field_simp [ne_of_gt upperHsepResidualRate_pos]
    linarith only [hmul, hcancel, hhalf]
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgammaZ
  have hCupExp : Cup ≤ Real.exp (Cup / sigma) := by
    have hdiv : Cup ≤ Cup / sigma := by
      rw [le_div_iff₀ hsigma0]
      exact mul_le_of_le_one_right hCup0.le (by linarith only [hsigma])
    exact hdiv.trans ((le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp (Cup / sigma)))
  have hlargeE : 2 * upperHsepResidualRate⁻¹ ≤ (E : ℝ) :=
    hlargeChoice.trans (hCupExp.trans ((le_max_left _ _).trans hmax))
  have hXcube : (E : ℝ) ^ 3 ≤ X := by
    dsimp only [X]
    exact Algsuperdiff.Section3.Provider.Percolation.cube_le_invSq_mul_gammaInv
      M E.property hgammaZ
  have hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    (le_max_right _ _).trans hmax
  have hcstarAbsorb :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z ≤
        Real.exp (-((upperHsepResidualRate / 2) * X)) := by
    simpa only [Z] using cstarInv_mul_exp_neg_afterBandRate_le_halfRate
      upperHsepResidualRate_pos E.property hlargeE hXcube hcstarE
  have hreserve : K *
      Real.exp (-((upperHsepResidualRate / 2) * X)) ≤ eps ^ 8 := by
    dsimp only [eps]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hprefChoice
  have hKreserve : K *
      ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z) ≤ eps ^ 8 :=
    (mul_le_mul_of_nonneg_left hcstarAbsorb hK0).trans hreserve
  exact ⟨hK0, hKreserve⟩

/-- The literal fifth named lane at the common tuned depth, in the same
ordinary/rare form consumed by the other good-wave estimates. -/
theorem exists_tunedAfterBand_good_finite_trace_split
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : probeSharpAfterBandTunedOutputConst d ≤ Cup) :
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
              (fun eta => probeSharpAfterBandTerm M R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n)
                (collarBandMeanDepth M (E : ℝ)) m eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega)) ≤
            ordinary omega + rare omega) ∧
        (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => probeSharpAfterBandTerm M R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n)
                (collarBandMeanDepth M (E : ℝ)) m eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) =
            ENNReal.ofReal
              (∑ j : Fin d, ∑' n : ℕ,
                probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
                  (fun eta => probeSharpAfterBandTerm M R.scale
                    (probeSharpLayerAnchor R.scale bfaProfileB
                      (collarBandMeanDepth M (E : ℝ)) n)
                    (collarBandMeanDepth M (E : ℝ)) m eta ^ 2)
                  (translateCutoffSample (triadicCubeShift R) omega))) ∧
        (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => probeSharpAfterBandTerm M R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n)
                (collarBandMeanDepth M (E : ℝ)) m eta ^ 2)
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
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)) *
            (Real.exp (-(Cup⁻¹ *
              ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) ^ 8) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let shift : Vec d := triadicCubeShift R
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let B : ℕ → CutoffSample d → ℝ := fun n eta =>
    probeSharpAfterBandTunedBaseTerm M R.scale m (E : ℝ) k n eta
  let Q : CutoffSample d → ℝ := fun eta =>
    probeSharpAfterBandHsepResidual M R.scale (E : ℝ) eta
  let O : ℕ → CutoffSample d → ℝ := fun n omega =>
    2 * B n (translateCutoffSample shift omega)
  let V : ℕ → CutoffSample d → ℝ := fun n omega =>
    Q (translateCutoffSample shift omega) *
      B n (translateCutoffSample shift omega)
  let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀)
  let target : ℝ := min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
    (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))
  let ordinary : CutoffSample d → ℝ := fun omega =>
    (d : ℝ) * (C * ∑' n : ℕ, O n omega)
  let rare : CutoffSample d → ℝ := fun omega =>
    (d : ℝ) * (C * ∑' n : ℕ, V n omega)
  let AO : ℝ := gammaTriangleConst 1 *
    (probeSharpAfterBandOrdinarySumConst d * target)
  let Z : ℝ := Real.exp (-(upperHsepResidualRate *
    ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))
  let AV : ℝ := gammaTriangleConst (upperProfileTargetSigma sigma) *
    (probeSharpAfterBandRareSumConst d * target * Z)
  let ordinaryScale : ℝ := (d : ℝ) * (C * AO)
  let rareScale : ℝ := (d : ℝ) * (C * AV)
  have hCup0 : 0 < Cup :=
    (probeSharpAfterBandTunedOutputConst_pos hd).trans_le houtput
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans houtput
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  obtain ⟨_hE4, _hunit, hgamma20, _hinvSq, hgammaZ⟩ :=
    badEventGates_of_profileAuxiliaryMaxGate M E.property hsigma0 hsigma
      hmaxAux hEgamma
  have hO0 : ∀ n omega, 0 ≤ O n omega := by
    intro n omega
    exact mul_nonneg (by norm_num)
      (probeSharpAfterBandTunedBaseTerm_nonneg
        M R.scale m (E : ℝ) k n _)
  have hV0 : ∀ n omega, 0 ≤ V n omega := by
    intro n omega
    exact mul_nonneg
      (probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ) _)
      (probeSharpAfterBandTunedBaseTerm_nonneg
        M R.scale m (E : ℝ) k n _)
  have hOmeas : ∀ n, Measurable (O n) := by
    intro n
    exact ((measurable_probeSharpAfterBandTunedBaseTerm
      M R.scale m (E : ℝ) k n).comp
        (measurable_translateCutoffSample shift)).const_mul 2
  have hVmeas : ∀ n, Measurable (V n) := by
    intro n
    exact ((measurable_probeSharpAfterBandHsepResidual
      M R.scale (E : ℝ)).comp
        (measurable_translateCutoffSample shift)).mul
      ((measurable_probeSharpAfterBandTunedBaseTerm
        M R.scale m (E : ℝ) k n).comp
          (measurable_translateCutoffSample shift))
  obtain ⟨hObig, hVbig, hOsumAE, hVsumAE, hC0, hordinary0, hrare0, hOsumMeas⟩ :=
    (show (IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (fun omega => ∑' n, O n omega) AO) ∧ (IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => ∑' n, V n omega) AV) ∧ (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => O n omega) ∧ (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Summable fun n => V n omega) ∧ (0 ≤ C) ∧ (∀ omega, 0 ≤ ordinary omega) ∧ (∀ omega, 0 ≤ rare
        omega) ∧ (Measurable (fun omega => ∑' n, O n omega)) from
      @upperAfterBandOrdinaryProfile_momentBounds1 (d) (M) (m) (k) (R) (hR) (E) (hS) (sigma)
        (hsigma0) (hsigma) (hEgamma) (hd) (hmaxAux) (hgamma20) (hO0) (hV0) (hOmeas) (hVmeas))
  have hVsumMeas : Measurable (fun omega => ∑' n, V n omega) := by
    have hnn : Measurable (fun omega =>
        ((∑' n, (V n omega).toNNReal : NNReal) : ℝ)) :=
      (Measurable.tsum fun n => (hVmeas n).real_toNNReal).coe_nnreal_real
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
  have hpoint := @afterBandGoodTrace_pointwiseSplit (d) (M) (m) (k) (R) (hR) (E) (hd) (j₀)
    (hOsumAE) (hVsumAE) (hsepPoint)
  obtain ⟨hENNRealEq, hENNRealDom, hordinaryOrlicz, hrareOrlicz, htarget0, hordinaryScale0⟩ :=
    (show (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j)
          (fun eta => probeSharpAfterBandTerm M R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
            k₀ m eta ^ 2)
          (translateCutoffSample shift omega))) =
        ENNReal.ofReal
          (∑ j : Fin d, ∑' n : ℕ,
            probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              k₀ n (m - 1) (basisVec j)
              (fun eta => probeSharpAfterBandTerm M R.scale
                (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
                k₀ m eta ^ 2)
              (translateCutoffSample shift omega))) ∧ (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          k₀ n (m - 1) (basisVec j)
          (fun eta => probeSharpAfterBandTerm M R.scale
            (probeSharpLayerAnchor R.scale bfaProfileB k₀ n)
            k₀ m eta ^ 2)
          (translateCutoffSample shift omega))) ≤
        ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega)) ∧ (IsBigOWith
          (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) ordinary ordinaryScale) ∧ (IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3)) rare rareScale) ∧ (0 ≤ target) ∧ (0 ≤ ordinaryScale) from
      @upperAfterBandOrdinaryProfile_momentBounds2 (d) (M) (m) (k) (R) (hR) (E) (sigma) (hd)
        (hObig) (hVbig) (hOsumAE) (hVsumAE) (hC0) (hordinary0) (hrare0) (hsepPoint) (hpoint))
  have hrareScale0 : 0 ≤ rareScale := by
    dsimp only [rareScale, AV, target, Z]
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg hC0
        (mul_nonneg gammaTriangleConst_pos.le
          (mul_nonneg
            (mul_nonneg
              (probeSharpAfterBandRareSumConst_pos d).le htarget0)
            (Real.exp_pos _).le)))
  have hordinaryBranch :
      1 + probeSharpAfterBandTunedOrdinaryTracePerCubeConst d ≤ Cup :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans houtput
  have hordinaryConst :
      probeSharpAfterBandTunedOrdinaryTracePerCubeConst d ≤ Cup := by
    linarith
  have hcstar0 : 0 ≤
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1).le
  have hordinaryRaw : ordinaryScale =
      probeSharpAfterBandTunedOrdinaryTracePerCubeConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * target := by
    dsimp only [ordinaryScale, C, AO]
    rw [vecNormSq_basisVec, mul_one,
      probeMeanGoodWaveConst_eq_dimension_mul_cstarInv,
      probeSharpAfterBandTunedOrdinaryTracePerCubeConst,
      probeSharpAfterBandOrdinaryPerCubeConst,
      probeMeanGoodWaveDimensionConst]
    ring
  have hordinaryScale : ordinaryScale ≤
      upperSaturatedPerCubeAmplitude Cup
        (Algsuperdiff.Section3.Disorder.cstar M) M.gamma k := by
    rw [hordinaryRaw, upperSaturatedPerCubeAmplitude]
    have hbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hordinaryConst hcstar0) htarget0
    convert hbound using 1
    all_goals first
      | rfl
      | (dsimp only [target]; push_cast; ring)
  let K : ℝ := probeSharpAfterBandTunedRareTracePrefactor d
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  obtain ⟨hK0, hKreserve⟩ :=
    (show (0 ≤ K) ∧ (K *
      ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * Z) ≤ eps ^ 8) from
      @upperAfterBandOrdinaryProfile_comparisonBounds2 (d) (M) (E) (sigma) (Cup) (hsigma0)
        (hsigma) (hmax) (houtput) (hd) (hCup0) (hgammaZ))
  let profilePow : ℝ :=
    (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))
  have hrareScale : rareScale ≤ profilePow * eps ^ 8 :=
    @upperAfterBandOrdinaryProfile_comparisonBounds1 (d) (M) (k) (E) (sigma) (Cup) (hsigma0)
      (hsigma) (hd) (htarget0) (hcstar0) (hK0) (hKreserve)
  exact ⟨ordinary, rare, ordinaryScale, rareScale,
    hordinary0, hordinaryMeas, hrare0, hrareMeas,
    by simpa only [k₀, shift] using hpoint,
    by simpa only [k₀, shift] using hENNRealEq,
    by simpa only [k₀, shift] using hENNRealDom,
    hordinaryOrlicz, hordinaryScale0, hordinaryScale,
    hrareOrlicz, hrareScale0,
    by simpa only [profilePow, eps, X] using hrareScale⟩

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
