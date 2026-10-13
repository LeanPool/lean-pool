/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperBandMeanShiftProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHsepResidualScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerSeries
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandOrlicz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability

/-!
# UpperBandMeanConsumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact consumption of the framed band-mean lane

This file connects the deterministic deep-band mean to its literal named
good-cell summand in the framed strict-descendant envelope.  The random
separation factor is split pointwise into its deterministic `2` branch and the
explicit hsep residual.  The ordinary branch is exactly the previously proved
band-mean shift profile; the rare branch is priced directly as a deterministic
multiple of the hsep residual, without introducing a fictitious random input.

Almost-everywhere summability of the translated rare layers is derived from
their layerwise stretched-exponential bounds.  Only one good-cell band-mean
coordinate lane is treated.  Root, collar, the other named lanes, the complete
envelope, the cutoff observable, and the source-facing upper theorem remain
outside this file.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}


/-! ## Common-depth terminal specialization -/

/-- The deterministic carrier of literal named summand 3 at the common
source-compatible depth. -/
def probeSharpBandMeanTunedBaseTerm
    (M : ABKModel d) (E : ℝ) (k n : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * Real.sqrt (probeSharpLayerMassEnvelope d n) *
    (3 : ℝ) ^ (-(M.gamma *
      ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
        (collarBandMeanDepth M E : ℝ)))) *
    waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
      (collarBandMeanDepth M E) ^ 2

/-- The deterministic coefficient remaining after summing the tuned Whitney
layers for one basis coordinate. -/
def probeSharpBandMeanTunedCoordinateCoeff
    (M : ABKModel d) (E : ℝ) (k : ℕ) (j : Fin d) : ℝ :=
  probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
    ∑' n : ℕ, probeSharpBandMeanTunedBaseTerm M E k n

/-- The literal real-valued Whitney sum of named summand 3 at the common
depth and translated strict descendant. -/
def probeSharpFramedBandMeanTunedCoordinateWhitneySum
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (omega : CutoffSample d) : ℝ :=
  ∑' n : ℕ,
    probeSharpFramedGoodWavePart M R.scale E bfaProfileB
      (collarBandMeanDepth M E) n (m - 1) (basisVec j)
      (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
        (collarBandMeanDepth M E) ^ 2)
      (translateCutoffSample (triadicCubeShift R) omega)

theorem probeSharpBandMeanTunedBaseTerm_nonneg
    (M : ABKModel d) (E : ℝ) (k n : ℕ) :
    0 ≤ probeSharpBandMeanTunedBaseTerm M E k n := by
  rw [probeSharpBandMeanTunedBaseTerm]
  positivity

theorem probeSharpBandMeanTunedCoordinateCoeff_nonneg
    (M : ABKModel d) (E : ℝ) (k : ℕ) (j : Fin d) :
    0 ≤ probeSharpBandMeanTunedCoordinateCoeff M E k j := by
  rw [probeSharpBandMeanTunedCoordinateCoeff]
  exact mul_nonneg
    (mul_nonneg
      (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
      (vecNormSq_nonneg (basisVec j)))
    (tsum_nonneg fun n => probeSharpBandMeanTunedBaseTerm_nonneg M E k n)

private theorem three_rpow_neg_nat_half_eq_band_mean_tuned (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℝ) / 2) =
      ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  rw [show -(n : ℝ) / 2 = (-(1 / 2 : ℝ)) * (n : ℝ) by ring,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]

private theorem probeSharpBandMeanTunedBaseTerm_le_geometric
    (M : ABKModel d) (E : ℝ) (k n : ℕ) :
    probeSharpBandMeanTunedBaseTerm M E k n ≤
      (5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
        waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M E) ^ 2) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  have hD : 0 ≤ (k : ℝ) + (n : ℝ) +
      (bfaAfterBandLayerCeil n : ℝ) +
      (collarBandMeanDepth M E : ℝ) := by positivity
  have hpow : (3 : ℝ) ^ (-(M.gamma *
      ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
        (collarBandMeanDepth M E : ℝ)))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg M.shellPrefix.gamma_pos.le hD))
  rw [probeSharpBandMeanTunedBaseTerm,
    sqrt_probeSharpLayerMassEnvelope_eq,
    three_rpow_neg_nat_half_eq_band_mean_tuned]
  have hleft : 0 ≤ 5 * (d : ℝ) ^ 2 *
      (Real.sqrt (6 * (d : ℝ)) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) := by positivity
  have hband : 0 ≤ waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
      (collarBandMeanDepth M E) ^ 2 := sq_nonneg _
  calc
    5 * (d : ℝ) ^ 2 *
          (Real.sqrt (6 * (d : ℝ)) *
            ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) *
          (3 : ℝ) ^ (-(M.gamma *
            ((k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
              (collarBandMeanDepth M E : ℝ)))) *
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
            (collarBandMeanDepth M E) ^ 2 ≤
        (5 * (d : ℝ) ^ 2 *
          (Real.sqrt (6 * (d : ℝ)) *
            ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n)) * 1 *
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
            (collarBandMeanDepth M E) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hleft) hband
    _ = _ := by ring

theorem summable_probeSharpBandMeanTunedBaseTerm
    (M : ABKModel d) (E : ℝ) (k : ℕ) :
    Summable fun n : ℕ => probeSharpBandMeanTunedBaseTerm M E k n := by
  let A : ℝ := 5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
    waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
      (collarBandMeanDepth M E) ^ 2
  let rho : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact Real.rpow_nonneg (by norm_num) _
  have hrho1 : rho < 1 := by
    dsimp only [rho]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact Summable.of_nonneg_of_le
    (probeSharpBandMeanTunedBaseTerm_nonneg M E k)
    (fun n => by
      simpa only [A, rho] using
        probeSharpBandMeanTunedBaseTerm_le_geometric M E k n)
    ((summable_geometric_of_lt_one hrho0 hrho1).mul_left A)

private theorem probeSharpFramedGoodWavePart_bandMean_tuned_eq
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) (p : Vec d) (omega : CutoffSample d) :
    probeSharpFramedGoodWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1) p
        (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M E) ^ 2) omega =
      probeMeanGoodWaveConst M * vecNormSq p *
        (probeSharpAfterBandHsepFactor M R.scale E omega *
          probeSharpBandMeanTunedBaseTerm M E k n) := by
  let k₀ := collarBandMeanDepth M E
  let D : ℝ := (k : ℝ) + (n : ℝ) +
    (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ)
  have hframe := probeSharpFramedAfterBandMultiplier_descendant_eq
    M hR E bfaProfileB k₀ n omega
  have hpow :
      (3 : ℝ) ^ (M.gamma * (hsep M R.scale E bfaProfileB omega : ℝ)) *
          (3 : ℝ) ^ (-(M.gamma * D)) =
        (3 : ℝ) ^ (M.gamma *
          ((hsep M R.scale E bfaProfileB omega : ℝ) - D)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [probeSharpFramedGoodWavePart, probeSharpAfterBandHsepFactor,
    probeSharpBandMeanTunedBaseTerm, hframe]
  change
    probeMeanGoodWaveConst M * vecNormSq p *
          Real.sqrt (probeSharpLayerMassEnvelope d n) *
          (3 : ℝ) ^ (M.gamma *
            ((hsep M R.scale E bfaProfileB omega : ℝ) - D)) *
          (5 * (d : ℝ) ^ 2 *
            waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2) =
      probeMeanGoodWaveConst M * vecNormSq p *
        ((3 : ℝ) ^
            (M.gamma * (hsep M R.scale E bfaProfileB omega : ℝ)) *
          (5 * (d : ℝ) ^ 2 *
            Real.sqrt (probeSharpLayerMassEnvelope d n) *
            (3 : ℝ) ^ (-(M.gamma * D)) *
            waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2))
  rw [← hpow]
  ring

/-- The literal tuned band-mean layer is bounded by its deterministic branch
and the explicit hsep-residual branch. -/
theorem probeSharpFramedGoodWavePart_bandMean_tuned_le_ordinary_add_rare
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M (E : ℝ)) ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega) ≤
      2 * (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        probeSharpBandMeanTunedBaseTerm M (E : ℝ) k n) +
      probeSharpAfterBandHsepResidual M R.scale (E : ℝ)
          (translateCutoffSample (triadicCubeShift R) omega) *
        (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          probeSharpBandMeanTunedBaseTerm M (E : ℝ) k n) := by
  let eta := translateCutoffSample (triadicCubeShift R) omega
  let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
  let B : ℝ := probeSharpBandMeanTunedBaseTerm M (E : ℝ) k n
  have heq := probeSharpFramedGoodWavePart_bandMean_tuned_eq
    M hR (E : ℝ) n (basisVec j) eta
  obtain ⟨hpoint, _hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hstate hsigma0 hsigma hmax hEgamma
  have hC : 0 ≤ C := mul_nonneg
    (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
    (vecNormSq_nonneg (basisVec j))
  have hB : 0 ≤ B :=
    probeSharpBandMeanTunedBaseTerm_nonneg M (E : ℝ) k n
  rw [heq]
  calc
    C * (probeSharpAfterBandHsepFactor M R.scale (E : ℝ) eta * B) ≤
        C * ((2 + probeSharpAfterBandHsepResidual
          M R.scale (E : ℝ) eta) * B) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hpoint eta) hB) hC
    _ = 2 * (C * B) +
        probeSharpAfterBandHsepResidual M R.scale (E : ℝ) eta *
          (C * B) := by ring

/-- The literal tuned Whitney sum for one coordinate has an exact
deterministic-plus-residual majorant. -/
theorem probeSharpFramedBandMeanTunedCoordinateWhitneySum_le_split
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedBandMeanTunedCoordinateWhitneySum
        M m R (E : ℝ) j omega ≤
      2 * probeSharpBandMeanTunedCoordinateCoeff M (E : ℝ) k j +
      probeSharpAfterBandHsepResidual M R.scale (E : ℝ)
          (translateCutoffSample (triadicCubeShift R) omega) *
        probeSharpBandMeanTunedCoordinateCoeff M (E : ℝ) k j := by
  let eta := translateCutoffSample (triadicCubeShift R) omega
  let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
  let Q : ℝ := probeSharpAfterBandHsepResidual
    M R.scale (E : ℝ) eta
  let B : ℕ → ℝ := fun n =>
    probeSharpBandMeanTunedBaseTerm M (E : ℝ) k n
  let X : ℕ → ℝ := fun n =>
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
      (fun _zeta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
        (collarBandMeanDepth M (E : ℝ)) ^ 2) eta
  let O : ℕ → ℝ := fun n => 2 * (C * B n)
  let V : ℕ → ℝ := fun n => Q * (C * B n)
  have hC : 0 ≤ C := mul_nonneg
    (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
    (vecNormSq_nonneg (basisVec j))
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ) eta
  have hB0 : ∀ n, 0 ≤ B n := fun n =>
    probeSharpBandMeanTunedBaseTerm_nonneg M (E : ℝ) k n
  have hBsum : Summable B := by
    simpa only [B] using
      summable_probeSharpBandMeanTunedBaseTerm M (E : ℝ) k
  have hOsum : Summable O := by
    simpa only [O, mul_assoc] using hBsum.mul_left (2 * C)
  have hVsum : Summable V := by
    simpa only [V, mul_assoc] using hBsum.mul_left (Q * C)
  have hX0 : ∀ n, 0 ≤ X n := fun n => by
    dsimp only [X]
    exact probeSharpFramedGoodWavePart_nonneg M.shellPrefix.dimension
      M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
      (fun _zeta => sq_nonneg _) eta
  have hXle : ∀ n, X n ≤ O n + V n := fun n => by
    have hreal :=
      probeSharpFramedGoodWavePart_bandMean_tuned_le_ordinary_add_rare
        M hR hstate hsigma0 hsigma hmax hEgamma n j omega
    simpa only [X, O, V, C, Q, B, eta] using hreal
  have hright : Summable fun n => O n + V n := hOsum.add hVsum
  have hXsum : Summable X :=
    Summable.of_nonneg_of_le hX0 hXle hright
  rw [probeSharpFramedBandMeanTunedCoordinateWhitneySum]
  change ∑' n, X n ≤ _
  calc
    ∑' n, X n ≤ ∑' n, (O n + V n) :=
      Summable.tsum_le_tsum hXle hXsum hright
    _ = (∑' n, O n) + ∑' n, V n := hOsum.tsum_add hVsum
    _ = 2 * probeSharpBandMeanTunedCoordinateCoeff M (E : ℝ) k j +
        probeSharpAfterBandHsepResidual M R.scale (E : ℝ) eta *
          probeSharpBandMeanTunedCoordinateCoeff M (E : ℝ) k j := by
      simp only [O, V, tsum_mul_left,
        probeSharpBandMeanTunedCoordinateCoeff, C, Q, B]

private theorem tsum_probeSharpBandMeanTunedBaseTerm_le
    (M : ABKModel d) (E : ℝ) (k : ℕ) :
    (∑' n : ℕ, probeSharpBandMeanTunedBaseTerm M E k n) ≤
      (5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
        (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
        waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M E) ^ 2 := by
  let A : ℝ := 5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
    waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
      (collarBandMeanDepth M E) ^ 2
  let rho : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact Real.rpow_nonneg (by norm_num) _
  have hrho1 : rho < 1 := by
    dsimp only [rho]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hright : Summable fun n : ℕ => A * rho ^ n :=
    (summable_geometric_of_lt_one hrho0 hrho1).mul_left A
  have hleft := summable_probeSharpBandMeanTunedBaseTerm M E k
  calc
    (∑' n : ℕ, probeSharpBandMeanTunedBaseTerm M E k n) ≤
        ∑' n : ℕ, A * rho ^ n :=
      Summable.tsum_le_tsum
        (fun n => by
          simpa only [A, rho] using
            probeSharpBandMeanTunedBaseTerm_le_geometric M E k n)
        hleft hright
    _ = A * (1 - rho)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hrho0 hrho1]
    _ = _ := by
      dsimp only [A, rho]
      ring

/-- Twice the tuned deterministic coordinate coefficient fits the existing
dimension-only band-mean shift budget. -/
theorem two_mul_probeSharpBandMeanTunedCoordinateCoeff_le_shiftConst
    (M : ABKModel d) {E : ℝ} (hE : 1 ≤ E)
    (hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (k : ℕ) (j : Fin d) :
    2 * probeSharpBandMeanTunedCoordinateCoeff M E k j ≤
      probeSharpBandMeanCoordinateShiftConst d := by
  let S : ℝ := 5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹
  let B : ℝ := waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
    (collarBandMeanDepth M E) ^ 2
  have hsum : (∑' n : ℕ, probeSharpBandMeanTunedBaseTerm M E k n) ≤
      S * B := by
    simpa only [S, B] using tsum_probeSharpBandMeanTunedBaseTerm_le M E k
  have houter : 0 ≤ probeMeanGoodWaveConst M :=
    probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M
  have hdim : 0 ≤ probeSharpBandMeanDimensionConst d :=
    probeSharpBandMeanDimensionConst_nonneg M.shellPrefix.dimension
  have hS : 0 ≤ S := by
    dsimp only [S]
    have hr : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact mul_nonneg (by positivity)
      (inv_nonneg.mpr (sub_nonneg.mpr hr.le))
  have hband :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * B ≤
        waveBandConst (probeDeepBandMeanAmplitude d) := by
    dsimp only [B, collarBandMeanDepth]
    exact cstarInv_mul_waveBandMean_sq_le
      (A := probeDeepBandMeanAmplitude d)
      (c := collarBandMeanDepthCoeff d)
      (cstar := Algsuperdiff.Section3.Disorder.cstar M)
      (collarBandMeanDepthCoeff_pos d).le
      (collarBandMeanDepthCoeff_le_one d) hE M.shellPrefix.gamma_pos
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
      hcstarE hEgamma
  rw [probeSharpBandMeanTunedCoordinateCoeff, vecNormSq_basisVec, mul_one]
  calc
    2 * (probeMeanGoodWaveConst M *
          ∑' n : ℕ, probeSharpBandMeanTunedBaseTerm M E k n) =
        (2 * probeMeanGoodWaveConst M) *
          ∑' n : ℕ, probeSharpBandMeanTunedBaseTerm M E k n := by ring
    _ ≤ (2 * probeMeanGoodWaveConst M) * (S * B) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by norm_num) houter)
    _ = probeSharpBandMeanDimensionConst d * (2 * S) *
          ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * B) := by
      rw [probeMeanGoodWaveConst, probeSharpBandMeanDimensionConst]
      ring
    _ ≤ probeSharpBandMeanDimensionConst d * (2 * S) *
          waveBandConst (probeDeepBandMeanAmplitude d) :=
      mul_le_mul_of_nonneg_left hband
        (mul_nonneg hdim (mul_nonneg (by norm_num) hS))
    _ = probeSharpBandMeanCoordinateShiftConst d := by
      rw [probeSharpBandMeanCoordinateShiftConst]
      dsimp only [S]
      ring

/-- One dimension-only choice pays the tuned deterministic trace, the profile
gate, and the rare prefactor absorption. -/
def probeSharpBandMeanTunedOutputConst (d : ℕ) : ℝ :=
  max (profileAuxiliaryConst d)
    (1 + max (probeSharpBandMeanTraceShiftConst d)
      ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
        upperHsepResidualRate⁻¹))

theorem probeSharpBandMeanTunedOutputConst_pos (hd : 2 ≤ d) :
    0 < probeSharpBandMeanTunedOutputConst d := by
  rw [probeSharpBandMeanTunedOutputConst]
  have htrace := probeSharpBandMeanTraceShiftConst_nonneg hd
  have hrare : 0 ≤
      (probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
        upperHsepResidualRate⁻¹ := by
    positivity [upperHsepResidualConst_pos, upperHsepResidualRate_pos]
  have hmax0 : 0 ≤ max (probeSharpBandMeanTraceShiftConst d)
      ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
        upperHsepResidualRate⁻¹) :=
    hrare.trans (le_max_right _ _)
  exact (by linarith : 0 < 1 + max (probeSharpBandMeanTraceShiftConst d)
    ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
      upperHsepResidualRate⁻¹)).trans_le (le_max_right _ _)

private theorem probeSharpBandMeanTuned_output_choice {Cup : ℝ}
    (houtput : probeSharpBandMeanTunedOutputConst d ≤ Cup) :
    probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8 ≤
      upperHsepResidualRate * Cup := by
  have hbranch :
      (probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
          upperHsepResidualRate⁻¹ ≤ Cup := by
    calc
      (probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
          upperHsepResidualRate⁻¹ ≤
          1 + max (probeSharpBandMeanTraceShiftConst d)
            ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
              upperHsepResidualRate⁻¹) := by
        linarith [le_max_right (probeSharpBandMeanTraceShiftConst d)
          ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
            upperHsepResidualRate⁻¹)]
      _ ≤ probeSharpBandMeanTunedOutputConst d := by
        rw [probeSharpBandMeanTunedOutputConst]
        exact le_max_right _ _
      _ ≤ Cup := houtput
  have hmul := mul_le_mul_of_nonneg_left hbranch
    upperHsepResidualRate_pos.le
  have hcancel : upperHsepResidualRate *
      ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
        upperHsepResidualRate⁻¹) =
      probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8 := by
    field_simp [ne_of_gt upperHsepResidualRate_pos]
  rwa [hcancel] at hmul

private theorem bandMeanTrace_ofReal_eq_layerSum :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d},
      R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) →
        ∀ {E : { E : ℝ // (1 : ℝ) ≤ E }},
          (2 : ℕ) ≤ d →
            ∀ (omega : CutoffSample d),
              ∑ j : Fin d,
                  ∑' (n : ℕ),
                    ENNReal.ofReal
                      (probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
                        (collarBandMeanDepth M (↑E : ℝ)) n
                        (m - (1 : ℤ)) (basisVec j)
                        (fun (_eta : CutoffSample d) =>
                          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma (collarBandMeanDepth
                            M (↑E : ℝ)) ^ (2 : ℕ))
                        (translateCutoffSample (triadicCubeShift R) omega)) =
                ENNReal.ofReal (∑ j : Fin d, probeSharpFramedBandMeanTunedCoordinateWhitneySum M m
                  R (↑E : ℝ) j omega) := by
  intro d M m k R hR E hd omega
  let eta := translateCutoffSample (triadicCubeShift R) omega
  have hterm0 (j : Fin d) (n : ℕ) : 0 ≤
      probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M (E : ℝ)) ^ 2) eta :=
    probeSharpFramedGoodWavePart_nonneg hd M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
      (fun _eta => sq_nonneg _) eta
  have htermSum (j : Fin d) : Summable fun n : ℕ =>
      probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M (E : ℝ)) ^ 2) eta := by
    have hbase := (summable_probeSharpBandMeanTunedBaseTerm
      M (E : ℝ) k).mul_left
        (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          probeSharpAfterBandHsepFactor M R.scale (E : ℝ) eta)
    have hfun : (fun n : ℕ =>
        probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
            (collarBandMeanDepth M (E : ℝ)) ^ 2) eta) =
        fun n : ℕ => (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          probeSharpAfterBandHsepFactor M R.scale (E : ℝ) eta) *
          probeSharpBandMeanTunedBaseTerm M (E : ℝ) k n := by
      funext n
      rw [probeSharpFramedGoodWavePart_bandMean_tuned_eq
        M hR (E : ℝ) n (basisVec j) eta]
      ring
    rw [hfun]
    exact hbase
  simp only [probeSharpFramedBandMeanTunedCoordinateWhitneySum]
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => tsum_nonneg fun n => by
    simpa only [eta] using hterm0 j n)]
  exact Finset.sum_congr rfl fun j _ => by
    simpa only [eta] using
      (ENNReal.ofReal_tsum_of_nonneg (hterm0 j) (htermSum j)).symm

/-- Terminal finite-coordinate split for literal named summand 3 at the common
tuned depth.  Its ordinary witness is a bounded deterministic shift; only the
explicit hsep residual occupies the target Orlicz lane. -/
theorem exists_good_band_mean_tuned_finite_trace_split
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma)
    (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : probeSharpBandMeanTunedOutputConst d ≤ Cup) :
    ∃ ordinary rare : CutoffSample d → ℝ,
      ∃ rareScale : ℝ,
        (∀ omega, 0 ≤ ordinary omega) ∧
        Measurable ordinary ∧
        (∀ omega, 0 ≤ rare omega) ∧
        Measurable rare ∧
        (∀ omega,
          (∑ j : Fin d,
            probeSharpFramedBandMeanTunedCoordinateWhitneySum
              M m R (E : ℝ) j omega) ≤
            ordinary omega + rare omega) ∧
        (∀ omega,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
                (collarBandMeanDepth M (E : ℝ)) ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) =
            ENNReal.ofReal
              (∑ j : Fin d,
                probeSharpFramedBandMeanTunedCoordinateWhitneySum
                  M m R (E : ℝ) j omega)) ∧
        (∀ omega,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
                (collarBandMeanDepth M (E : ℝ)) ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) ≤
            ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega)) ∧
        (∀ omega, ordinary omega ≤ Cup) ∧
        IsBigOWith (cutoffSampleLaw M).toMeasure
          (gammaSigma ((1 - sigma) / 3)) rare rareScale ∧
        0 ≤ rareScale ∧
        rareScale ≤
          (Real.exp (-(Cup⁻¹ *
            ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8 := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let shift : Vec d := triadicCubeShift R
  let C : ℝ := probeSharpBandMeanTunedCoordinateCoeff M (E : ℝ) k j₀
  let D : ℝ := (d : ℝ) * C
  let ordinary : CutoffSample d → ℝ := fun _omega => (d : ℝ) * (2 * C)
  let rare : CutoffSample d → ℝ := fun omega => D *
    probeSharpAfterBandHsepResidual M R.scale (E : ℝ)
      (translateCutoffSample shift omega)
  let rareScale : ℝ := D * upperHsepResidualScale sigma M.gamma
  have hCup0 : 0 < Cup :=
    (probeSharpBandMeanTunedOutputConst_pos hd).trans_le houtput
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans houtput
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact probeSharpBandMeanTunedCoordinateCoeff_nonneg
      M (E : ℝ) k j₀
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (Nat.cast_nonneg d) hC0
  have hcoeffEq (j : Fin d) :
      probeSharpBandMeanTunedCoordinateCoeff M (E : ℝ) k j = C := by
    dsimp only [C, probeSharpBandMeanTunedCoordinateCoeff]
    simp only [vecNormSq_basisVec]
  have hordinaryNonneg : ∀ omega, 0 ≤ ordinary omega := by
    intro omega
    dsimp only [ordinary]
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg (by norm_num) hC0)
  have hrareNonneg : ∀ omega, 0 ≤ rare omega := by
    intro omega
    dsimp only [rare]
    exact mul_nonneg hD0
      (probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ)
        (translateCutoffSample shift omega))
  have hordinaryMeasurable : Measurable ordinary := measurable_const
  have hrareMeasurable : Measurable rare := by
    dsimp only [rare]
    exact ((measurable_probeSharpAfterBandHsepResidual
      M R.scale (E : ℝ)).comp
        (measurable_translateCutoffSample shift)).const_mul _
  have hpoint : ∀ omega,
      (∑ j : Fin d,
        probeSharpFramedBandMeanTunedCoordinateWhitneySum
          M m R (E : ℝ) j omega) ≤
        ordinary omega + rare omega := by
    intro omega
    calc
      (∑ j : Fin d,
          probeSharpFramedBandMeanTunedCoordinateWhitneySum
            M m R (E : ℝ) j omega) ≤
          ∑ j : Fin d,
            (2 * probeSharpBandMeanTunedCoordinateCoeff
                M (E : ℝ) k j +
              probeSharpAfterBandHsepResidual M R.scale (E : ℝ)
                  (translateCutoffSample shift omega) *
                probeSharpBandMeanTunedCoordinateCoeff
                  M (E : ℝ) k j) := by
        exact Finset.sum_le_sum fun j _ =>
          probeSharpFramedBandMeanTunedCoordinateWhitneySum_le_split
            M hR hstate hsigma0 hsigma hmaxAux hEgamma j omega
      _ = ordinary omega + rare omega := by
        simp_rw [hcoeffEq]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ordinary, rare, D, shift]
        ring
  have hENNRealEq := @bandMeanTrace_ofReal_eq_layerSum (d) (M) (m) (k) (R) (hR) (E) (hd)
  have hENNRealDom : ∀ omega,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
            (collarBandMeanDepth M (E : ℝ)) ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega))) ≤
        ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega) := by
    intro omega
    rw [hENNRealEq omega,
      ← ENNReal.ofReal_add (hordinaryNonneg omega) (hrareNonneg omega)]
    exact ENNReal.ofReal_le_ofReal (hpoint omega)
  have hcoordinateBound : 2 * C ≤
      probeSharpBandMeanCoordinateShiftConst d := by
    dsimp only [C]
    exact two_mul_probeSharpBandMeanTunedCoordinateCoeff_le_shiftConst
      M E.property ((le_max_right _ _).trans hmax) hEgamma k j₀
  have htraceBound : (d : ℝ) * (2 * C) ≤
      probeSharpBandMeanTraceShiftConst d := by
    calc
      (d : ℝ) * (2 * C) ≤
          (d : ℝ) * probeSharpBandMeanCoordinateShiftConst d :=
        mul_le_mul_of_nonneg_left hcoordinateBound (Nat.cast_nonneg d)
      _ = probeSharpBandMeanTraceShiftConst d := by
        rw [probeSharpBandMeanTraceShiftConst]
  have hbudget : max (probeSharpBandMeanTraceShiftConst d)
      ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
        upperHsepResidualRate⁻¹) ≤ Cup := by
    have hbranch : 1 + max (probeSharpBandMeanTraceShiftConst d)
        ((probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst + 8) *
          upperHsepResidualRate⁻¹) ≤ Cup :=
      (le_max_right _ _).trans houtput
    linarith
  have htraceBudget : probeSharpBandMeanTraceShiftConst d ≤ Cup :=
    (le_max_left _ _).trans hbudget
  have hordinaryBound : ∀ omega, ordinary omega ≤ Cup := by
    intro omega
    exact htraceBound.trans htraceBudget
  obtain ⟨_hfactor, hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hstate hsigma0 hsigma hmaxAux hEgamma
  have hresidual' : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileHsepTau sigma))
      (probeSharpAfterBandHsepResidual M R.scale (E : ℝ))
      (upperHsepResidualScale sigma M.gamma) := by
    simpa only [upperHsepResidualScale] using hresidual
  have htau : 0 < upperProfileHsepTau sigma :=
    upperProfileHsepTau_pos hsigma0 hsigma
  have htargetTau : upperProfileTargetSigma sigma ≤
      upperProfileHsepTau sigma := by
    refine (upperProfileTargetSigma_le_hsep_mul_one hsigma0 hsigma).trans ?_
    rw [div_le_iff₀ (add_pos htau one_pos)]
    nlinarith [sq_nonneg (upperProfileHsepTau sigma)]
  have hresidualTarget :=
    HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
      htargetTau hresidual'
  have htranslated :=
    Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M shift (measurable_probeSharpAfterBandHsepResidual
        M R.scale (E : ℝ)) hresidualTarget
  have hrareOrlicz : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3)) rare rareScale := by
    have hscaled := htranslated.const_mul hD0
    simpa only [rare, rareScale, upperProfileTargetSigma, D, shift]
      using hscaled
  have hrareScale0 : 0 ≤ rareScale := by
    dsimp only [rareScale]
    exact mul_nonneg hD0 (upperHsepResidualScale_pos sigma M.gamma).le
  have hCTrace : D ≤ probeSharpBandMeanTraceShiftConst d := by
    have hCdouble : C ≤ 2 * C := by linarith
    calc
      D ≤ (d : ℝ) * (2 * C) := by
        dsimp only [D]
        exact mul_le_mul_of_nonneg_left hCdouble (Nat.cast_nonneg d)
      _ ≤ probeSharpBandMeanTraceShiftConst d := htraceBound
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  let K : ℝ := probeSharpBandMeanTraceShiftConst d *
    upperHsepResidualConst
  have hresScale := upperHsepResidualScale_le_exp
    hsigma0 hsigma E.property M.shellPrefix.gamma_pos
  have hrareExp : rareScale ≤
      K * Real.exp (-(upperHsepResidualRate * X)) := by
    dsimp only [rareScale, K, X]
    calc
      D * upperHsepResidualScale sigma M.gamma ≤
          probeSharpBandMeanTraceShiftConst d *
            upperHsepResidualScale sigma M.gamma :=
        mul_le_mul_of_nonneg_right hCTrace
          (upperHsepResidualScale_pos sigma M.gamma).le
      _ ≤ probeSharpBandMeanTraceShiftConst d *
          (upperHsepResidualConst *
            Real.exp (-(upperHsepResidualRate *
              ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) :=
        mul_le_mul_of_nonneg_left hresScale
          (probeSharpBandMeanTraceShiftConst_nonneg hd)
      _ = (probeSharpBandMeanTraceShiftConst d * upperHsepResidualConst) *
          Real.exp (-(upperHsepResidualRate *
            ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) := by ring
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hchoice : K + 8 ≤ upperHsepResidualRate * Cup := by
    simpa only [K] using probeSharpBandMeanTuned_output_choice houtput
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (probeSharpBandMeanTraceShiftConst_nonneg hd)
      upperHsepResidualConst_pos.le
  have hrareBound : rareScale ≤ eps ^ 8 := by
    refine hrareExp.trans ?_
    dsimp only [eps]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hchoice
  exact ⟨ordinary, rare, rareScale,
    hordinaryNonneg, hordinaryMeasurable,
    hrareNonneg, hrareMeasurable, hpoint, hENNRealEq, hENNRealDom,
    hordinaryBound,
    hrareOrlicz, hrareScale0, by
      simpa only [eps, X] using hrareBound⟩

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
