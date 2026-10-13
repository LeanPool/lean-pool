/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperBandMeanConsumption

/-!
# UpperHeadSharpSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Sharp separation estimates for the framed wave-head lane

The literal squared wave-head estimate carries `gamma * hsep`.  The first part
of this file prices that factor in `Gamma_1`.  The resulting ordinary
coordinate lane is controlled in `Gamma_1`, while the residual lane has
exponent `Gamma_((1 - sigma) / 3)` and an explicit scale bounded by the eighth
power of the frozen exceptional scale.

Spatial maxima, coordinate traces, and root/depth aggregation remain
downstream.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-- The `Gamma_1` scale obtained by taking the `upperProfileBaseSigma sigma` power
of the proved exponential hsep tail. -/
def upperHeadHsepOneScale (sigma gamma : ℝ) : ℝ :=
  gamma *
    (upperProfileBaseSigma sigma * bfaProfileB * Real.log 3)⁻¹ *
    hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
      upperProfileBaseSigma sigma

theorem upperHeadHsepOneScale_pos
    {sigma gamma : ℝ} (hsigma0 : 0 < sigma)
    (hsigma : sigma ≤ 1 / 2) (hgamma : 0 < gamma) :
    0 < upperHeadHsepOneScale sigma gamma := by
  rw [upperHeadHsepOneScale]
  have hp := upperProfileBaseSigma_pos hsigma0 hsigma
  have hc : 0 < upperProfileBaseSigma sigma * bfaProfileB * Real.log 3 :=
    mul_pos (mul_pos hp bfaProfileB_pos) (Real.log_pos (by norm_num))
  exact mul_pos (mul_pos hgamma (inv_pos.mpr hc))
    (Real.rpow_pos_of_pos (hsepAmplitude_pos _ _) _)

private theorem hsep_cast_le_base_rpow
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (h : ℕ) :
    (h : ℝ) ≤
      (upperProfileBaseSigma sigma * bfaProfileB * Real.log 3)⁻¹ *
        ((3 : ℝ) ^ (bfaProfileB * (h : ℝ))) ^
          upperProfileBaseSigma sigma := by
  let p : ℝ := upperProfileBaseSigma sigma
  let c : ℝ := p * bfaProfileB * Real.log 3
  let x : ℝ := h
  have hp : 0 < p := upperProfileBaseSigma_pos hsigma0 hsigma
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (mul_pos hp bfaProfileB_pos) (Real.log_pos (by norm_num))
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hcx : c * x ≤ Real.exp (c * x) := by
    linarith [Real.add_one_le_exp (c * x)]
  have hscaled : x ≤ c⁻¹ * Real.exp (c * x) := by
    have hmul := mul_le_mul_of_nonneg_left hcx (inv_nonneg.mpr hc.le)
    have hcancel : c⁻¹ * (c * x) = x := by
      field_simp [hc.ne']
    rwa [hcancel] at hmul
  have hexp :
      Real.exp (c * x) =
        ((3 : ℝ) ^ (bfaProfileB * x)) ^ p := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    dsimp only [c]
    ring
  simpa only [p, c, x, hexp]
    using hscaled

/-- Under the frozen profile gates, the basic hsep exponential at the fixed
profile slope has exponent `upperProfileBaseSigma sigma`. -/
theorem isBigOWith_upperProfileBase_three_rpow_bfa_hsep
    (M : ABKModel d) (root : ℤ) {E : {E : ℝ // 1 ≤ E}}
    (hSroot : Algsuperdiff.Frozen.Section3.inductionState M (root - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileBaseSigma sigma))
      (fun omega => (3 : ℝ) ^
        (bfaProfileB * (hsep M root (E : ℝ) bfaProfileB omega : ℝ)))
      (hsepAmplitude (upperProfileSigma sigma) bfaProfileB) := by
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
  have hbase := isBigOWith_gammaSigma_three_rpow_hsep_of_gates
    (m := root) (E := (E : ℝ)) (sigma := upperProfileSigma sigma)
    (b := bfaProfileB) M M.shellPrefix.dimension E.property hSroot
    hsigmaProfile0 hsigmaProfileHalf bfaProfileB_pos
    bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20 hinvSq hEb hgammaZ
  simpa only [upperProfileBaseSigma] using hbase

/-- The sharp squared-head factor `gamma * hsep` is `Gamma_1` at an explicit scale.
The proof uses the power rule on the proved exponential hsep tail; no new
probabilistic premise is exposed. -/
theorem isBigOWith_gammaSigma_one_gamma_mul_hsep
    (M : ABKModel d) (root : ℤ) {E : {E : ℝ // 1 ≤ E}}
    (hSroot : Algsuperdiff.Frozen.Section3.inductionState M (root - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (fun omega => M.gamma *
        (hsep M root (E : ℝ) bfaProfileB omega : ℝ))
      (upperHeadHsepOneScale sigma M.gamma) := by
  let p : ℝ := upperProfileBaseSigma sigma
  let K : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB
  let Y : CutoffSample d → ℝ := fun omega => (3 : ℝ) ^
    (bfaProfileB * (hsep M root (E : ℝ) bfaProfileB omega : ℝ))
  let c : ℝ := p * bfaProfileB * Real.log 3
  have hp : 0 < p := upperProfileBaseSigma_pos hsigma0 hsigma
  have hK : 0 < K := by dsimp only [K]; exact hsepAmplitude_pos _ _
  have hY0 : ∀ omega, 0 ≤ Y omega := fun omega => by
    dsimp only [Y]
    positivity
  have hY : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma p) Y K := by
    simpa only [p, K, Y] using
      isBigOWith_upperProfileBase_three_rpow_bfa_hsep
        M root hSroot hsigma0 hsigma hmax hEgamma
  have hpow := HCPolySupport.IndependentSums.isBigOWith_gammaSigma_rpow
    (μ := (cutoffSampleLaw M).toMeasure) hp hK.le hY0 hY
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (mul_pos hp bfaProfileB_pos) (Real.log_pos (by norm_num))
  have hcoeff : 0 ≤ M.gamma * c⁻¹ :=
    mul_nonneg M.shellPrefix.gamma_pos.le (inv_nonneg.mpr hc.le)
  have hscaled := hpow.const_mul hcoeff
  have hle : ∀ omega : CutoffSample d,
      M.gamma * (hsep M root (E : ℝ) bfaProfileB omega : ℝ) ≤
        (M.gamma * c⁻¹) * Y omega ^ p := by
    intro omega
    have hh := hsep_cast_le_base_rpow hsigma0 hsigma
      (hsep M root (E : ℝ) bfaProfileB omega)
    have hmul := mul_le_mul_of_nonneg_left (by
      simpa only [p, c, Y] using hh) M.shellPrefix.gamma_pos.le
    simpa only [p, c, Y, mul_assoc] using hmul
  have hmono := isBigOWith_gammaSigma_of_le hle hscaled
  have hpp : p / p = 1 := div_self hp.ne'
  simpa only [upperHeadHsepOneScale, p, K, Y, c, hpp, mul_assoc]
    using hmono

private theorem three_rpow_neg_nat_half_eq_good_head (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℝ) / 2) =
      ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  rw [show -(n : ℝ) / 2 = (-(1 / 2 : ℝ)) * (n : ℝ) by ring,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]

def goodHeadTunedDepthDecay
    (M : ABKModel d) (E : ℝ) (k : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(M.gamma *
    ((k : ℝ) + (collarBandMeanDepth M E : ℝ))))

def goodHeadTunedLayerBase
    (M : ABKModel d) (n : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * Real.sqrt (probeSharpLayerMassEnvelope d n) *
    (3 : ℝ) ^ (-(M.gamma *
      ((n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)))) *
    waveL4HeadConst d ^ 2

/-- The complete deterministic coefficient of one tuned good-head layer.
The factorization keeps the full `k + n + ceil + k₀` negative offset. -/
def goodHeadTunedBaseTerm
    (M : ABKModel d) (E : ℝ) (k n : ℕ) : ℝ :=
  goodHeadTunedDepthDecay M E k * goodHeadTunedLayerBase M n

def goodHeadTunedCoordinateCoeff
    (M : ABKModel d) (E : ℝ) (k : ℕ) (j : Fin d) : ℝ :=
  probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
    goodHeadTunedDepthDecay M E k *
    ∑' n : ℕ, goodHeadTunedLayerBase M n

def goodHeadTunedCoordinateLane
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k : ℕ) (j : Fin d)
    (omega : CutoffSample d) : ℝ :=
  goodHeadTunedCoordinateCoeff M E k j *
    (M.gamma * (hsep M root E bfaProfileB omega : ℝ))

def goodHeadTunedOrdinaryCoordinateLane
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k : ℕ) (j : Fin d)
    (omega : CutoffSample d) : ℝ :=
  2 * goodHeadTunedCoordinateLane M root E k j omega

def goodHeadTunedRareCoordinateLane
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k : ℕ) (j : Fin d)
    (omega : CutoffSample d) : ℝ :=
  probeSharpAfterBandHsepResidual M root E omega *
    goodHeadTunedCoordinateLane M root E k j omega

def goodHeadTunedCoordinateScale
    (M : ABKModel d) (E sigma : ℝ) (k : ℕ) (j : Fin d) : ℝ :=
  goodHeadTunedCoordinateCoeff M E k j *
    upperHeadHsepOneScale sigma M.gamma

def goodHeadTunedOrdinaryCoordinateScale
    (M : ABKModel d) (E sigma : ℝ) (k : ℕ) (j : Fin d) : ℝ :=
  2 * goodHeadTunedCoordinateScale M E sigma k j

def goodHeadTunedRareCoordinateScale
    (M : ABKModel d) (E sigma : ℝ) (k : ℕ) (j : Fin d) : ℝ :=
  HCPolySupport.Book.Ch04.gammaProductConst
      (upperProfileHsepTau sigma) 1 *
    upperHsepResidualScale sigma M.gamma *
    goodHeadTunedCoordinateScale M E sigma k j

def goodHeadTunedCoordinateWhitneySum
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (omega : CutoffSample d) : ℝ :=
  ∑' n : ℕ,
    probeSharpFramedGoodWavePart M R.scale E bfaProfileB
      (collarBandMeanDepth M E) n (m - 1) (basisVec j)
      (fun eta => waveHeadTerm M R.scale E bfaProfileB
        (probeSharpLayerAnchor R.scale bfaProfileB
          (collarBandMeanDepth M E) n) eta ^ 2)
      (translateCutoffSample (triadicCubeShift R) omega)

theorem good_head_tuned_depth_decay_nonneg
    (M : ABKModel d) (E : ℝ) (k : ℕ) :
    0 ≤ goodHeadTunedDepthDecay M E k := by
  rw [goodHeadTunedDepthDecay]
  positivity

theorem good_head_tuned_layer_base_nonneg
    (M : ABKModel d) (n : ℕ) :
    0 ≤ goodHeadTunedLayerBase M n := by
  rw [goodHeadTunedLayerBase]
  positivity

theorem good_head_tuned_base_term_nonneg
    (M : ABKModel d) (E : ℝ) (k n : ℕ) :
    0 ≤ goodHeadTunedBaseTerm M E k n := by
  rw [goodHeadTunedBaseTerm]
  exact mul_nonneg (good_head_tuned_depth_decay_nonneg M E k)
    (good_head_tuned_layer_base_nonneg M n)

private theorem good_head_tuned_layer_base_le_geometric
    (M : ABKModel d) (n : ℕ) :
    goodHeadTunedLayerBase M n ≤
      (5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
        waveL4HeadConst d ^ 2) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  have hN : 0 ≤ (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) := by
    positivity
  have hpow : (3 : ℝ) ^ (-(M.gamma *
      ((n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg M.shellPrefix.gamma_pos.le hN))
  rw [goodHeadTunedLayerBase, sqrt_probeSharpLayerMassEnvelope_eq,
    three_rpow_neg_nat_half_eq_good_head]
  have hleft : 0 ≤ 5 * (d : ℝ) ^ 2 *
      (Real.sqrt (6 * (d : ℝ)) *
        ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) := by positivity
  have hconst : 0 ≤ waveL4HeadConst d ^ 2 := sq_nonneg _
  calc
    5 * (d : ℝ) ^ 2 *
          (Real.sqrt (6 * (d : ℝ)) *
            ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) *
          (3 : ℝ) ^ (-(M.gamma *
            ((n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)))) *
          waveL4HeadConst d ^ 2 ≤
        (5 * (d : ℝ) ^ 2 *
          (Real.sqrt (6 * (d : ℝ)) *
            ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n)) * 1 *
          waveL4HeadConst d ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hleft) hconst
    _ = _ := by ring

theorem summable_good_head_tuned_layer_base (M : ABKModel d) :
    Summable fun n : ℕ => goodHeadTunedLayerBase M n := by
  let A : ℝ := 5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
    waveL4HeadConst d ^ 2
  let rho : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact Real.rpow_nonneg (by norm_num) _
  have hrho1 : rho < 1 := by
    dsimp only [rho]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hright : Summable fun n : ℕ => A * rho ^ n :=
    (summable_geometric_of_lt_one hrho0 hrho1).mul_left A
  exact Summable.of_nonneg_of_le
    (good_head_tuned_layer_base_nonneg M)
    (fun n => by
      simpa only [A, rho] using good_head_tuned_layer_base_le_geometric M n)
    hright

theorem summable_good_head_tuned_base_term
    (M : ABKModel d) (E : ℝ) (k : ℕ) :
    Summable fun n : ℕ => goodHeadTunedBaseTerm M E k n := by
  simpa only [goodHeadTunedBaseTerm] using
    (summable_good_head_tuned_layer_base M).mul_left
      (goodHeadTunedDepthDecay M E k)

theorem good_head_tuned_coordinate_coeff_nonneg
    (M : ABKModel d) (E : ℝ) (k : ℕ) (j : Fin d) :
    0 ≤ goodHeadTunedCoordinateCoeff M E k j := by
  rw [goodHeadTunedCoordinateCoeff]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
        (vecNormSq_nonneg (basisVec j)))
      (good_head_tuned_depth_decay_nonneg M E k))
    (tsum_nonneg (good_head_tuned_layer_base_nonneg M))

theorem good_head_tuned_coordinate_lane_nonneg
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k : ℕ) (j : Fin d)
    (omega : CutoffSample d) :
    0 ≤ goodHeadTunedCoordinateLane M root E k j omega := by
  rw [goodHeadTunedCoordinateLane]
  exact mul_nonneg (good_head_tuned_coordinate_coeff_nonneg M E k j)
    (mul_nonneg M.shellPrefix.gamma_pos.le (Nat.cast_nonneg _))

theorem good_head_tuned_rare_coordinate_lane_nonneg
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k : ℕ) (j : Fin d)
    (omega : CutoffSample d) :
    0 ≤ goodHeadTunedRareCoordinateLane M root E k j omega := by
  rw [goodHeadTunedRareCoordinateLane]
  exact mul_nonneg
    (probeSharpAfterBandHsepResidual_nonneg M root E omega)
    (good_head_tuned_coordinate_lane_nonneg M root E k j omega)

theorem measurable_good_head_tuned_coordinate_lane
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k : ℕ) (j : Fin d) :
    Measurable (goodHeadTunedCoordinateLane M root E k j) := by
  exact measurable_comp_hsep M root E bfaProfileB fun h : ℕ =>
    goodHeadTunedCoordinateCoeff M E k j * (M.gamma * (h : ℝ))

theorem measurable_good_head_tuned_rare_coordinate_lane
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k : ℕ) (j : Fin d) :
    Measurable (goodHeadTunedRareCoordinateLane M root E k j) := by
  exact (measurable_probeSharpAfterBandHsepResidual M root E).mul
    (measurable_good_head_tuned_coordinate_lane M root E k j)

theorem good_head_tuned_coordinate_scale_nonneg
    (M : ABKModel d) (E sigma : ℝ) (k : ℕ) (j : Fin d)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2) :
    0 ≤ goodHeadTunedCoordinateScale M E sigma k j := by
  rw [goodHeadTunedCoordinateScale]
  exact mul_nonneg (good_head_tuned_coordinate_coeff_nonneg M E k j)
    (upperHeadHsepOneScale_pos hsigma0 hsigma M.shellPrefix.gamma_pos).le

/-- Literal summand 2 with the complete tuned negative offset retained. -/
theorem probeSharpFramedGoodWavePart_le_good_head_tuned_factor
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedGoodWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1) (basisVec j)
        (fun eta => waveHeadTerm M R.scale E bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M E) n) eta ^ 2)
        omega ≤
      probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        (probeSharpAfterBandHsepFactor M R.scale E omega *
          (goodHeadTunedBaseTerm M E k n *
            (M.gamma * (hsep M R.scale E bfaProfileB omega : ℝ)))) := by
  let k₀ := collarBandMeanDepth M E
  let D : ℝ := (k : ℝ) + (n : ℝ) +
    (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ)
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  have hframe := probeSharpFramedAfterBandMultiplier_descendant_eq
    M hR E bfaProfileB k₀ n omega
  have hpow :
      (3 : ℝ) ^ (M.gamma *
          ((hsep M R.scale E bfaProfileB omega : ℝ) - D)) =
        (3 : ℝ) ^ (M.gamma *
            (hsep M R.scale E bfaProfileB omega : ℝ)) *
          (3 : ℝ) ^ (-(M.gamma * D)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hsplit :
      (3 : ℝ) ^ (-(M.gamma * D)) =
        goodHeadTunedDepthDecay M E k *
          (3 : ℝ) ^ (-(M.gamma *
            ((n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)))) := by
    rw [goodHeadTunedDepthDecay, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    dsimp only [D, k₀]
    ring
  have houter : 0 ≤ probeMeanGoodWaveConst M * vecNormSq (basisVec j) :=
    mul_nonneg
      (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
      (vecNormSq_nonneg (basisVec j))
  have hfactor : 0 ≤ probeSharpAfterBandHsepFactor M R.scale E omega := by
    rw [probeSharpAfterBandHsepFactor]
    positivity
  have hcoeff : 0 ≤ 5 * (d : ℝ) ^ 2 *
      Real.sqrt (probeSharpLayerMassEnvelope d n) *
      (3 : ℝ) ^ (-(M.gamma * D)) := by positivity
  have hframe' :
      probeSharpFramedAfterBandMultiplier M R.scale E bfaProfileB
          k₀ n (m - 1) omega =
        (3 : ℝ) ^ (M.gamma *
          ((hsep M R.scale E bfaProfileB omega : ℝ) - D)) := by
    simpa only [D, bfaAfterBandLayerCeil] using hframe
  rw [probeSharpFramedGoodWavePart, hframe', hpow,
    probeSharpAfterBandHsepFactor]
  let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
  let F : ℝ := (3 : ℝ) ^
    (M.gamma * (hsep M R.scale E bfaProfileB omega : ℝ))
  let A : ℝ := 5 * (d : ℝ) ^ 2 *
    Real.sqrt (probeSharpLayerMassEnvelope d n) *
      (3 : ℝ) ^ (-(M.gamma * D))
  let H : ℝ := waveHeadTerm M R.scale E bfaProfileB ell omega
  have hC : 0 ≤ C := by simpa only [C] using houter
  have hF : 0 ≤ F := by
    simpa only [F, probeSharpAfterBandHsepFactor] using hfactor
  have hA : 0 ≤ A := by simpa only [A] using hcoeff
  calc
    probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          Real.sqrt (probeSharpLayerMassEnvelope d n) *
          ((3 : ℝ) ^ (M.gamma *
              (hsep M R.scale E bfaProfileB omega : ℝ)) *
            (3 : ℝ) ^ (-(M.gamma * D))) *
          (5 * (d : ℝ) ^ 2 *
            waveHeadTerm M R.scale E bfaProfileB ell omega ^ 2) =
        C * F * A * H ^ 2 := by
      simp only [C, F, A, H]
      ring
    _ ≤ C * F * A *
          (waveL4HeadConst d ^ 2 *
            (M.gamma * (hsep M R.scale E bfaProfileB omega : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (waveHeadTerm_sq_le M R.scale E bfaProfileB ell omega)
        (mul_nonneg (mul_nonneg hC hF) hA)
    _ = _ := by
      simp only [C, F, A, D, k₀, goodHeadTunedBaseTerm,
        goodHeadTunedLayerBase]
      rw [hsplit]
      ring

/-- splits the retained framed power without touching the tuned decay. -/
theorem probeSharpFramedGoodWavePart_le_good_head_tuned_ordinary_add_rare
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
        (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
          (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega) ≤
      let eta := translateCutoffSample (triadicCubeShift R) omega
      let C := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
      let B := goodHeadTunedBaseTerm M (E : ℝ) k n
      let G := M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB eta : ℝ)
      C * (2 * (B * G)) +
        C * (probeSharpAfterBandHsepResidual M R.scale (E : ℝ) eta *
          (B * G)) := by
  have hhead := probeSharpFramedGoodWavePart_le_good_head_tuned_factor
    M hR (E : ℝ) n j
      (translateCutoffSample (triadicCubeShift R) omega)
  obtain ⟨hpoint, _hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hS hsigma0 hsigma hmax hEgamma
  let eta := translateCutoffSample (triadicCubeShift R) omega
  let C := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
  let B := goodHeadTunedBaseTerm M (E : ℝ) k n
  let G := M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB eta : ℝ)
  have hC : 0 ≤ C := mul_nonneg
    (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
    (vecNormSq_nonneg (basisVec j))
  have hBG : 0 ≤ B * G := mul_nonneg
    (good_head_tuned_base_term_nonneg M (E : ℝ) k n)
    (mul_nonneg M.shellPrefix.gamma_pos.le (Nat.cast_nonneg _))
  refine hhead.trans ?_
  calc
    C * (probeSharpAfterBandHsepFactor M R.scale (E : ℝ) eta *
          (B * G)) ≤
        C * ((2 + probeSharpAfterBandHsepResidual
          M R.scale (E : ℝ) eta) * (B * G)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hpoint eta) hBG) hC
    _ = C * (2 * (B * G)) +
        C * (probeSharpAfterBandHsepResidual
          M R.scale (E : ℝ) eta * (B * G)) := by ring

theorem good_head_tuned_coordinate_whitney_sum_le_ordinary_add_rare
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) (omega : CutoffSample d) :
    goodHeadTunedCoordinateWhitneySum M m R (E : ℝ) j omega ≤
      goodHeadTunedOrdinaryCoordinateLane M R.scale (E : ℝ) k j
        (translateCutoffSample (triadicCubeShift R) omega) +
      goodHeadTunedRareCoordinateLane M R.scale (E : ℝ) k j
        (translateCutoffSample (triadicCubeShift R) omega) := by
  let eta := translateCutoffSample (triadicCubeShift R) omega
  let C : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
  let G : ℝ := M.gamma *
    (hsep M R.scale (E : ℝ) bfaProfileB eta : ℝ)
  let Q : ℝ := probeSharpAfterBandHsepResidual M R.scale (E : ℝ) eta
  let B : ℕ → ℝ := fun n => goodHeadTunedBaseTerm M (E : ℝ) k n
  let X : ℕ → ℝ := fun n =>
    probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
      (fun zeta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
        (probeSharpLayerAnchor R.scale bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n) zeta ^ 2) eta
  let O : ℕ → ℝ := fun n => (2 * C * G) * B n
  let V : ℕ → ℝ := fun n => (C * Q * G) * B n
  have hC : 0 ≤ C := mul_nonneg
    (probeMeanGoodWaveConst_nonneg M.shellPrefix.dimension M)
    (vecNormSq_nonneg (basisVec j))
  have hG : 0 ≤ G := mul_nonneg M.shellPrefix.gamma_pos.le
    (Nat.cast_nonneg _)
  have hQ : 0 ≤ Q := by
    simpa only [Q] using
      probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ) eta
  have hB0 : ∀ n, 0 ≤ B n := fun n =>
    good_head_tuned_base_term_nonneg M (E : ℝ) k n
  have hBsum : Summable B := by
    simpa only [B] using summable_good_head_tuned_base_term M (E : ℝ) k
  have hO0 : ∀ n, 0 ≤ O n := fun n => by
    dsimp only [O]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC) hG) (hB0 n)
  have hV0 : ∀ n, 0 ≤ V n := fun n => by
    dsimp only [V]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC hQ) hG) (hB0 n)
  have hOsum : Summable O := by
    simpa only [O] using hBsum.mul_left (2 * C * G)
  have hVsum : Summable V := by
    simpa only [V] using hBsum.mul_left (C * Q * G)
  have hX0 : ∀ n, 0 ≤ X n := fun n => by
    dsimp only [X]
    exact probeSharpFramedGoodWavePart_nonneg M.shellPrefix.dimension
      M R.scale (E : ℝ) bfaProfileB
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
      (fun zeta => sq_nonneg _) eta
  have hXle : ∀ n, X n ≤ O n + V n := fun n => by
    have hreal := probeSharpFramedGoodWavePart_le_good_head_tuned_ordinary_add_rare
      M hR hS hsigma0 hsigma hmax hEgamma n j omega
    calc
      X n ≤ _ := hreal
      _ = O n + V n := by
        simp only [eta, C, G, Q, B, O, V]
        ring
  have hright : Summable fun n => O n + V n := hOsum.add hVsum
  have hXsum : Summable X :=
    Summable.of_nonneg_of_le hX0 hXle hright
  rw [goodHeadTunedCoordinateWhitneySum]
  change ∑' n, X n ≤ _
  calc
    ∑' n, X n ≤ ∑' n, (O n + V n) :=
      Summable.tsum_le_tsum hXle hXsum hright
    _ = (∑' n, O n) + ∑' n, V n := hOsum.tsum_add hVsum
    _ = goodHeadTunedOrdinaryCoordinateLane M R.scale (E : ℝ) k j eta +
        goodHeadTunedRareCoordinateLane M R.scale (E : ℝ) k j eta := by
      simp only [O, V, tsum_mul_left,
        goodHeadTunedOrdinaryCoordinateLane,
        goodHeadTunedRareCoordinateLane,
        goodHeadTunedCoordinateLane,
        goodHeadTunedCoordinateCoeff,
        goodHeadTunedBaseTerm, B, C, G, Q]
      ring

private theorem inductionState_mono_good_head_tuned
    (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}) {m₁ m₂ : ℤ}
    (hm : m₁ ≤ m₂)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₂ E) :
    Algsuperdiff.Frozen.Section3.inductionState M m₁ E := by
  rw [Algsuperdiff.Frozen.Section3.inductionState] at hS ⊢
  exact ⟨fun i hi => hS.1 i (hi.trans hm),
    fun i hi => hS.2 i (hi.trans hm)⟩

theorem isBigOWith_gammaSigma_one_good_head_tuned_ordinary_coordinate_lane_comp
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) :
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (fun omega => goodHeadTunedOrdinaryCoordinateLane
        M R.scale (E : ℝ) k j
          (translateCutoffSample (triadicCubeShift R) omega))
      (goodHeadTunedOrdinaryCoordinateScale M (E : ℝ) sigma k j) := by
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by rw [hscale]; omega
  have hSroot := inductionState_mono_good_head_tuned M E hroot hS
  have hbase := isBigOWith_gammaSigma_one_gamma_mul_hsep
    M R.scale hSroot hsigma0 hsigma hmax hEgamma
  have hcenter := hbase.const_mul
    (good_head_tuned_coordinate_coeff_nonneg M (E : ℝ) k j)
  have hordinary := hcenter.const_mul (by norm_num : (0 : ℝ) ≤ 2)
  have hmeas : Measurable
      (goodHeadTunedOrdinaryCoordinateLane M R.scale (E : ℝ) k j) :=
    (measurable_good_head_tuned_coordinate_lane
      M R.scale (E : ℝ) k j).const_mul _
  exact Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
    M (triadicCubeShift R) hmeas (by
      simpa only [goodHeadTunedCoordinateLane,
        goodHeadTunedCoordinateScale,
        goodHeadTunedOrdinaryCoordinateLane,
        goodHeadTunedOrdinaryCoordinateScale] using! hordinary)

theorem isBigOWith_upperProfileTarget_good_head_tuned_rare_coordinate_lane_comp
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (j : Fin d) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3))
      (fun omega => goodHeadTunedRareCoordinateLane
        M R.scale (E : ℝ) k j
          (translateCutoffSample (triadicCubeShift R) omega))
      (goodHeadTunedRareCoordinateScale M (E : ℝ) sigma k j) := by
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by rw [hscale]; omega
  have hSroot := inductionState_mono_good_head_tuned M E hroot hS
  obtain ⟨_hpoint, hresidual⟩ :=
    probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
      M hR hS hsigma0 hsigma hmax hEgamma
  have hresidual' : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileHsepTau sigma))
      (probeSharpAfterBandHsepResidual M R.scale (E : ℝ))
      (upperHsepResidualScale sigma M.gamma) := by
    simpa only [upperHsepResidualScale] using hresidual
  have hbase := isBigOWith_gammaSigma_one_gamma_mul_hsep
    M R.scale hSroot hsigma0 hsigma hmax hEgamma
  have hcenter := hbase.const_mul
    (good_head_tuned_coordinate_coeff_nonneg M (E : ℝ) k j)
  have hcenter' : IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (goodHeadTunedCoordinateLane M R.scale (E : ℝ) k j)
      (goodHeadTunedCoordinateScale M (E : ℝ) sigma k j) := by
    simpa only [goodHeadTunedCoordinateLane,
      goodHeadTunedCoordinateScale] using! hcenter
  have hproduct := isBigOWith_upperProfileTarget_hsep_mul_one
    hsigma0 hsigma
    (upperHsepResidualScale_pos sigma M.gamma).le
    (good_head_tuned_coordinate_scale_nonneg
      M (E : ℝ) sigma k j hsigma0 hsigma)
    (probeSharpAfterBandHsepResidual_nonneg M R.scale (E : ℝ))
    (good_head_tuned_coordinate_lane_nonneg M R.scale (E : ℝ) k j)
    hresidual' hcenter'
  have hcentered : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (goodHeadTunedRareCoordinateLane M R.scale (E : ℝ) k j)
      (goodHeadTunedRareCoordinateScale M (E : ℝ) sigma k j) := by
    simpa only [goodHeadTunedRareCoordinateLane,
      goodHeadTunedRareCoordinateScale] using! hproduct
  have htranslated :=
    Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M (triadicCubeShift R)
      (measurable_good_head_tuned_rare_coordinate_lane
        M R.scale (E : ℝ) k j) hcentered
  simpa only [upperProfileTargetSigma] using htranslated

def goodHeadTunedMassSumConst (d : ℕ) : ℝ :=
  (5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
      waveL4HeadConst d ^ 2) *
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

def goodHeadTunedHsepOneConst : ℝ :=
  (((7 : ℝ) / 8 * bfaProfileB * Real.log 3)⁻¹) *
    superposedFluxHsepConst

def goodHeadTunedCoordinateConst (d : ℕ) : ℝ :=
  probeMeanGoodWaveDimensionConst d * goodHeadTunedMassSumConst d *
    goodHeadTunedHsepOneConst

def goodHeadTunedRarePrefactor (d : ℕ) : ℝ :=
  64 * upperHsepResidualConst * goodHeadTunedCoordinateConst d

def goodHeadTunedOutputConst (d : ℕ) : ℝ :=
  max (profileAuxiliaryConst d)
    (1 + max
      (2 * (d : ℝ) * goodHeadTunedCoordinateConst d)
      (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
        upperHsepResidualRate⁻¹))

private theorem tsum_good_head_tuned_layer_base_le_mass_sum_const
    (M : ABKModel d) :
    (∑' n : ℕ, goodHeadTunedLayerBase M n) ≤
      goodHeadTunedMassSumConst d := by
  let A : ℝ := 5 * (d : ℝ) ^ 2 * Real.sqrt (6 * (d : ℝ)) *
    waveL4HeadConst d ^ 2
  let rho : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact Real.rpow_nonneg (by norm_num) _
  have hrho1 : rho < 1 := by
    dsimp only [rho]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hright : Summable fun n : ℕ => A * rho ^ n :=
    (summable_geometric_of_lt_one hrho0 hrho1).mul_left A
  have hsum : (∑' n : ℕ, goodHeadTunedLayerBase M n) ≤
      ∑' n : ℕ, A * rho ^ n :=
    Summable.tsum_le_tsum
      (fun n => by
        simpa only [A, rho] using good_head_tuned_layer_base_le_geometric M n)
      (summable_good_head_tuned_layer_base M) hright
  calc
    (∑' n : ℕ, goodHeadTunedLayerBase M n) ≤
        ∑' n : ℕ, A * rho ^ n := hsum
    _ = A * (1 - rho)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hrho0 hrho1]
    _ = goodHeadTunedMassSumConst d := by rfl

private theorem good_head_tuned_hsep_one_scale_le_const_mul_gamma
    {sigma gamma : ℝ} (hsigma0 : 0 < sigma)
    (hsigma : sigma ≤ 1 / 2) (hgamma : 0 ≤ gamma) :
    upperHeadHsepOneScale sigma gamma ≤
      goodHeadTunedHsepOneConst * gamma := by
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
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpLower bfaProfileB_pos.le)
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
  rw [upperHeadHsepOneScale, goodHeadTunedHsepOneConst]
  change gamma * c⁻¹ * K ^ p ≤ (c₀⁻¹ * H) * gamma
  calc
    gamma * c⁻¹ * K ^ p ≤ gamma * c₀⁻¹ * H := by gcongr
    _ = (c₀⁻¹ * H) * gamma := by ring

private theorem good_head_tuned_depth_decay_le_one
    (M : ABKModel d) (E : ℝ) (k : ℕ) :
    goodHeadTunedDepthDecay M E k ≤ 1 := by
  rw [goodHeadTunedDepthDecay]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (neg_nonpos.mpr (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity)))

private theorem good_head_tuned_coordinate_const_nonneg (hd : 2 ≤ d) :
    0 ≤ goodHeadTunedCoordinateConst d := by
  have hmean : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  have hmass : 0 ≤ goodHeadTunedMassSumConst d := by
    rw [goodHeadTunedMassSumConst]
    have hr : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact mul_nonneg (by positivity)
      (inv_nonneg.mpr (sub_nonneg.mpr hr.le))
  have hhsep : 0 ≤ goodHeadTunedHsepOneConst := by
    rw [goodHeadTunedHsepOneConst]
    exact mul_nonneg
      (inv_nonneg.mpr (by
        exact (mul_pos (mul_pos (by norm_num) bfaProfileB_pos)
          (Real.log_pos (by norm_num))).le))
      superposedFluxHsepConst_pos.le
  rw [goodHeadTunedCoordinateConst]
  exact mul_nonneg (mul_nonneg hmean hmass) hhsep

private theorem good_head_tuned_coordinate_scale_le
    (M : ABKModel d) (E sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (k : ℕ) (j : Fin d) :
    goodHeadTunedCoordinateScale M E sigma k j ≤
      goodHeadTunedCoordinateConst d *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma := by
  have hmass := tsum_good_head_tuned_layer_base_le_mass_sum_const M
  have hhsep := good_head_tuned_hsep_one_scale_le_const_mul_gamma
    hsigma0 hsigma M.shellPrefix.gamma_pos.le
  have hdecay := good_head_tuned_depth_decay_le_one M E k
  have hmean0 : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg M.shellPrefix.dimension)
  have hcstar0 : 0 ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1).le
  have hmass0 : 0 ≤ goodHeadTunedMassSumConst d := by
    rw [goodHeadTunedMassSumConst]
    have hr : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact mul_nonneg (by positivity)
      (inv_nonneg.mpr (sub_nonneg.mpr hr.le))
  have hhsep0 : 0 ≤ goodHeadTunedHsepOneConst := by
    rw [goodHeadTunedHsepOneConst]
    exact mul_nonneg
      (inv_nonneg.mpr (by
        exact (mul_pos (mul_pos (by norm_num) bfaProfileB_pos)
          (Real.log_pos (by norm_num))).le))
      superposedFluxHsepConst_pos.le
  have hsum0 : 0 ≤ ∑' n : ℕ, goodHeadTunedLayerBase M n :=
    tsum_nonneg (good_head_tuned_layer_base_nonneg M)
  have hscale0 : 0 ≤ upperHeadHsepOneScale sigma M.gamma :=
    (upperHeadHsepOneScale_pos hsigma0 hsigma M.shellPrefix.gamma_pos).le
  rw [goodHeadTunedCoordinateScale, goodHeadTunedCoordinateCoeff,
    probeMeanGoodWaveConst_eq_dimension_mul_cstarInv,
    vecNormSq_basisVec, mul_one, goodHeadTunedCoordinateConst]
  calc
    (probeMeanGoodWaveDimensionConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) *
          goodHeadTunedDepthDecay M E k *
          (∑' n : ℕ, goodHeadTunedLayerBase M n) *
          upperHeadHsepOneScale sigma M.gamma ≤
        (probeMeanGoodWaveDimensionConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) * 1 *
          goodHeadTunedMassSumConst d *
          (goodHeadTunedHsepOneConst * M.gamma) := by
      gcongr
    _ = (probeMeanGoodWaveDimensionConst d *
          goodHeadTunedMassSumConst d * goodHeadTunedHsepOneConst) *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma := by ring

private theorem good_head_tuned_rare_prefactor_nonneg (hd : 2 ≤ d) :
    0 ≤ goodHeadTunedRarePrefactor d := by
  rw [goodHeadTunedRarePrefactor]
  positivity [upperHsepResidualConst_pos,
    good_head_tuned_coordinate_const_nonneg hd]

theorem good_head_tuned_output_const_pos (hd : 2 ≤ d) :
    0 < goodHeadTunedOutputConst d := by
  rw [goodHeadTunedOutputConst]
  have hK := good_head_tuned_rare_prefactor_nonneg hd
  have hrateInv : 0 < upperHsepResidualRate⁻¹ :=
    inv_pos.mpr upperHsepResidualRate_pos
  have hrare : 0 ≤ ((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
      upperHsepResidualRate⁻¹ := by positivity
  have hmax0 : 0 ≤ max
      (2 * (d : ℝ) * goodHeadTunedCoordinateConst d)
      (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
        upperHsepResidualRate⁻¹) :=
    hrare.trans (le_max_right _ _)
  exact (by linarith : 0 < 1 + max
    (2 * (d : ℝ) * goodHeadTunedCoordinateConst d)
    (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
      upperHsepResidualRate⁻¹)).trans_le (le_max_right _ _)

private theorem good_head_tuned_rare_coordinate_scale_le_exp
    (M : ABKModel d) {E : {E : ℝ // 1 ≤ E}}
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hcstar : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (k : ℕ) (j : Fin d) :
    goodHeadTunedRareCoordinateScale M (E : ℝ) sigma k j ≤
      goodHeadTunedRarePrefactor d *
        Real.exp (-(upperHsepResidualRate *
          ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let P : ℝ := HCPolySupport.Book.Ch04.gammaProductConst
    (upperProfileHsepTau sigma) 1
  let Rscale : ℝ := upperHsepResidualScale sigma M.gamma
  let C : ℝ := goodHeadTunedCoordinateScale M (E : ℝ) sigma k j
  let B : ℝ := goodHeadTunedCoordinateConst d
  let Z : ℝ := Real.exp (-(upperHsepResidualRate *
    ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hP : P ≤ 64 := by
    dsimp only [P]
    exact gammaProductConst_upperProfileHsepTau_one_le_sixty_four
      hsigma0 hsigma
  have hR0 : 0 ≤ Rscale := by
    dsimp only [Rscale]
    exact (upperHsepResidualScale_pos sigma M.gamma).le
  have hR : Rscale ≤ upperHsepResidualConst * Z := by
    dsimp only [Rscale, Z]
    exact upperHsepResidualScale_le_exp hsigma0 hsigma E.property
      M.shellPrefix.gamma_pos
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact good_head_tuned_coordinate_scale_nonneg
      M (E : ℝ) sigma k j hsigma0 hsigma
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact good_head_tuned_coordinate_const_nonneg M.shellPrefix.dimension
  have hcoord := good_head_tuned_coordinate_scale_le
    M (E : ℝ) sigma hsigma0 hsigma k j
  have hEgammaOne := mul_gamma_le_one_of_le_rpow_neg_fifth
    E.property M.shellPrefix.gamma_pos hEgamma
  have hcstarGamma :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcstar M.shellPrefix.gamma_pos.le).trans
      hEgammaOne
  have hC : C ≤ B := by
    calc
      C ≤ B * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          M.gamma := by simpa only [C, B] using hcoord
      _ = B * ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          M.gamma) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hcstarGamma hB0
      _ = B := mul_one _
  have hPR : P * Rscale ≤ 64 * (upperHsepResidualConst * Z) :=
    mul_le_mul hP hR hR0 (by norm_num)
  have hright0 : 0 ≤ 64 * (upperHsepResidualConst * Z) := by
    positivity [upperHsepResidualConst_pos, Real.exp_pos]
  rw [goodHeadTunedRareCoordinateScale]
  change P * Rscale * C ≤ _
  rw [goodHeadTunedRarePrefactor]
  calc
    P * Rscale * C ≤
        (64 * (upperHsepResidualConst * Z)) * B :=
      mul_le_mul hPR hC hC0 hright0
    _ = 64 * upperHsepResidualConst * B * Z := by ring

private theorem good_head_tuned_rare_output_choice {Cup : ℝ}
    (houtput : goodHeadTunedOutputConst d ≤ Cup) :
    (d : ℝ) * goodHeadTunedRarePrefactor d + 8 ≤
      upperHsepResidualRate * Cup := by
  have hbranch :
      ((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
          upperHsepResidualRate⁻¹ ≤ Cup := by
    calc
      ((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
          upperHsepResidualRate⁻¹ ≤
          1 + max
            (2 * (d : ℝ) * goodHeadTunedCoordinateConst d)
            (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
              upperHsepResidualRate⁻¹) := by
        linarith [le_max_right
          (2 * (d : ℝ) * goodHeadTunedCoordinateConst d)
          (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
            upperHsepResidualRate⁻¹)]
      _ ≤ goodHeadTunedOutputConst d := by
        rw [goodHeadTunedOutputConst]
        exact le_max_right _ _
      _ ≤ Cup := houtput
  have hmul := mul_le_mul_of_nonneg_left hbranch
    upperHsepResidualRate_pos.le
  have hcancel : upperHsepResidualRate *
      (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
        upperHsepResidualRate⁻¹) =
      (d : ℝ) * goodHeadTunedRarePrefactor d + 8 := by
    field_simp [ne_of_gt upperHsepResidualRate_pos]
  have htrace : (d : ℝ) * goodHeadTunedRarePrefactor d + 8 ≤
      upperHsepResidualRate * Cup := by rwa [hcancel] at hmul
  exact htrace


private theorem upperHeadSharpSplit_momentBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d},
    R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) →
    ∀ {E : { E : ℝ // (1 : ℝ) ≤ E }},
    Frozen.Section3.inductionState M (m - (1 : ℤ)) E →
    ∀ {sigma : ℝ},
    (0 : ℝ) < sigma →
    sigma ≤ (1 / 2 : ℝ) →
    (↑E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
    ∀ (hd : (2 : ℕ) ≤ d),
    let j₀ : Fin d := ⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two hd⟩;
    let shift : Vec d := triadicCubeShift R;
    let ordinary : CutoffSample d → ℝ := fun (omega : CutoffSample d) =>
    (↑d : ℝ) *
    goodHeadTunedOrdinaryCoordinateLane M R.scale (↑E : ℝ) k j₀ (translateCutoffSample shift omega);
    let rare : CutoffSample d → ℝ := fun (omega : CutoffSample d) =>
    (↑d : ℝ) *
    goodHeadTunedRareCoordinateLane M R.scale (↑E : ℝ) k j₀ (translateCutoffSample shift omega);
    let ordinaryScale : ℝ := (↑d : ℝ) * goodHeadTunedOrdinaryCoordinateScale M (↑E : ℝ) sigma k j₀;
    max (Real.exp (profileAuxiliaryConst d / sigma)) (Disorder.cstar M)⁻¹ ≤ (↑E : ℝ) →
    (∀ (j : Fin d) (eta : CutoffSample d),
    goodHeadTunedOrdinaryCoordinateLane M R.scale (↑E : ℝ) k j eta =
    goodHeadTunedOrdinaryCoordinateLane M R.scale (↑E : ℝ) k j₀ eta) →
    (∀ (j : Fin d) (eta : CutoffSample d),
    goodHeadTunedRareCoordinateLane M R.scale (↑E : ℝ) k j eta =
    goodHeadTunedRareCoordinateLane M R.scale (↑E : ℝ) k j₀ eta) →
    (∀ (omega : CutoffSample d), (0 : ℝ) ≤ ordinary omega) →
    (∀ (omega : CutoffSample d), (0 : ℝ) ≤ rare omega) →
    (∀ (omega : CutoffSample d),
    ∑ j : Fin d, goodHeadTunedCoordinateWhitneySum M m R (↑E : ℝ) j omega ≤
    ordinary omega + rare omega) ∧
    (∀ (omega : CutoffSample d),
    ∑ j : Fin d,
    ∑' (n : ℕ),
    ENNReal.ofReal
    (probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
    (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
    (fun (eta : CutoffSample d) =>
    waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
    (probeSharpLayerAnchor R.scale bfaProfileB
    (collarBandMeanDepth M (↑E : ℝ)) n)
    eta ^
    (2 : ℕ))
    (translateCutoffSample (triadicCubeShift R) omega)) =
    ENNReal.ofReal
    (∑ j : Fin d, goodHeadTunedCoordinateWhitneySum M m R (↑E : ℝ) j omega)) ∧
    (∀ (omega : CutoffSample d),
    ∑ j : Fin d,
    ∑' (n : ℕ),
    ENNReal.ofReal
    (probeSharpFramedGoodWavePart M R.scale (↑E : ℝ) bfaProfileB
    (collarBandMeanDepth M (↑E : ℝ)) n (m - (1 : ℤ)) (basisVec j)
    (fun (eta : CutoffSample d) =>
    waveHeadTerm M R.scale (↑E : ℝ) bfaProfileB
    (probeSharpLayerAnchor R.scale bfaProfileB
    (collarBandMeanDepth M (↑E : ℝ)) n)
    eta ^
    (2 : ℕ))
    (translateCutoffSample (triadicCubeShift R) omega)) ≤
    ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega)) ∧
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma (1 : ℝ))
    ordinary ordinaryScale := by
  intro d M m k R hR E hstate _ hsigma0 hsigma hEgamma hd j₀ shift ordinary rare ordinaryScale hmaxAux hordinaryEq hrareEq hordinaryNonneg hrareNonneg
  have hpoint : ∀ omega,
      (∑ j : Fin d,
        goodHeadTunedCoordinateWhitneySum M m R (E : ℝ) j omega) ≤
          ordinary omega + rare omega := by
    intro omega
    calc
      (∑ j : Fin d,
          goodHeadTunedCoordinateWhitneySum M m R (E : ℝ) j omega) ≤
          ∑ j : Fin d,
            (goodHeadTunedOrdinaryCoordinateLane
                M R.scale (E : ℝ) k j
                  (translateCutoffSample shift omega) +
              goodHeadTunedRareCoordinateLane
                M R.scale (E : ℝ) k j
                  (translateCutoffSample shift omega)) := by
        exact Finset.sum_le_sum fun j _ =>
          good_head_tuned_coordinate_whitney_sum_le_ordinary_add_rare
            M hR hstate hsigma0 hsigma hmaxAux hEgamma j omega
      _ = ordinary omega + rare omega := by
        rw [Finset.sum_add_distrib]
        simp_rw [hordinaryEq, hrareEq]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ordinary, rare, shift]
  have hENNRealEq : ∀ omega,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega))) =
        ENNReal.ofReal
          (∑ j : Fin d,
            goodHeadTunedCoordinateWhitneySum M m R (E : ℝ) j omega) := by
    intro omega
    have hterm0 (j : Fin d) (n : ℕ) : 0 ≤
        probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega) :=
      probeSharpFramedGoodWavePart_nonneg hd M R.scale (E : ℝ) bfaProfileB
        (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
        (fun eta => sq_nonneg _) _
    have htermSum (j : Fin d) : Summable fun n : ℕ =>
        probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega) := by
      let eta := translateCutoffSample (triadicCubeShift R) omega
      let Cj := probeMeanGoodWaveConst M * vecNormSq (basisVec j)
      let G := M.gamma * (hsep M R.scale (E : ℝ) bfaProfileB eta : ℝ)
      let Q := probeSharpAfterBandHsepResidual M R.scale (E : ℝ) eta
      let B : ℕ → ℝ := fun n => goodHeadTunedBaseTerm M (E : ℝ) k n
      let O : ℕ → ℝ := fun n => Cj * (2 * (B n * G))
      let V : ℕ → ℝ := fun n => Cj * (Q * (B n * G))
      have hBsum : Summable B := by
        simpa only [B] using summable_good_head_tuned_base_term M (E : ℝ) k
      have hOsum : Summable O := by
        simpa only [O, mul_assoc, mul_comm, mul_left_comm] using
          hBsum.mul_left (2 * Cj * G)
      have hVsum : Summable V := by
        simpa only [V, mul_assoc, mul_comm, mul_left_comm] using
          hBsum.mul_left (Cj * Q * G)
      exact Summable.of_nonneg_of_le (hterm0 j) (fun n => by
        have h := probeSharpFramedGoodWavePart_le_good_head_tuned_ordinary_add_rare
          M hR hstate hsigma0 hsigma hmaxAux hEgamma n j omega
        simpa only [eta, Cj, G, Q, B, O, V] using h) (hOsum.add hVsum)
    simp only [goodHeadTunedCoordinateWhitneySum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => tsum_nonneg (hterm0 j))]
    exact Finset.sum_congr rfl fun j _ =>
      (ENNReal.ofReal_tsum_of_nonneg (hterm0 j) (htermSum j)).symm
  have hENNRealDom : ∀ omega,
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
          (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
          (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
            (probeSharpLayerAnchor R.scale bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
          (translateCutoffSample (triadicCubeShift R) omega))) ≤
        ENNReal.ofReal (ordinary omega) + ENNReal.ofReal (rare omega) := by
    intro omega
    rw [hENNRealEq omega,
      ← ENNReal.ofReal_add (hordinaryNonneg omega) (hrareNonneg omega)]
    exact ENNReal.ofReal_le_ofReal (hpoint omega)
  have hordinaryOrlicz : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) ordinary ordinaryScale := by
    have hcoordinate :=
      isBigOWith_gammaSigma_one_good_head_tuned_ordinary_coordinate_lane_comp
        M hR hstate hsigma0 hsigma hmaxAux hEgamma j₀
    have htrace := hcoordinate.const_mul (Nat.cast_nonneg d)
    simpa only [ordinary, ordinaryScale, shift] using htrace
  exact ⟨hpoint, hENNRealEq, hENNRealDom, hordinaryOrlicz⟩

/-- Terminal finite-coordinate split for literal summand 2 of the sharp
per-cube estimate.  The two witnesses are explicit nonnegative measurable
lanes.  Their scales are paid, respectively, by the saturated ordinary
amplitude and by the fixed eighth-power exceptional reserve. -/
theorem exists_good_head_tuned_finite_trace_split
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma)
    (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : goodHeadTunedOutputConst d ≤ Cup) :
    ∃ ordinary rare : CutoffSample d → ℝ,
      ∃ ordinaryScale rareScale : ℝ,
        (∀ omega, 0 ≤ ordinary omega) ∧
        Measurable ordinary ∧
        (∀ omega, 0 ≤ rare omega) ∧
        Measurable rare ∧
        (∀ omega,
          (∑ j : Fin d,
            goodHeadTunedCoordinateWhitneySum M m R (E : ℝ) j omega) ≤
              ordinary omega + rare omega) ∧
        (∀ omega,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
              (translateCutoffSample (triadicCubeShift R) omega))) =
            ENNReal.ofReal
              (∑ j : Fin d,
                goodHeadTunedCoordinateWhitneySum M m R (E : ℝ) j omega)) ∧
        (∀ omega,
          (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedGoodWavePart M R.scale (E : ℝ) bfaProfileB
              (collarBandMeanDepth M (E : ℝ)) n (m - 1) (basisVec j)
              (fun eta => waveHeadTerm M R.scale (E : ℝ) bfaProfileB
                (probeSharpLayerAnchor R.scale bfaProfileB
                  (collarBandMeanDepth M (E : ℝ)) n) eta ^ 2)
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
            ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8 := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let shift : Vec d := triadicCubeShift R
  let ordinary : CutoffSample d → ℝ := fun omega =>
    (d : ℝ) * goodHeadTunedOrdinaryCoordinateLane
      M R.scale (E : ℝ) k j₀ (translateCutoffSample shift omega)
  let rare : CutoffSample d → ℝ := fun omega =>
    (d : ℝ) * goodHeadTunedRareCoordinateLane
      M R.scale (E : ℝ) k j₀ (translateCutoffSample shift omega)
  let ordinaryScale : ℝ := (d : ℝ) *
    goodHeadTunedOrdinaryCoordinateScale M (E : ℝ) sigma k j₀
  let rareScale : ℝ := (d : ℝ) *
    goodHeadTunedRareCoordinateScale M (E : ℝ) sigma k j₀
  have hCup0 : 0 < Cup :=
    (good_head_tuned_output_const_pos hd).trans_le houtput
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans houtput
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hordinaryEq (j : Fin d) (eta : CutoffSample d) :
      goodHeadTunedOrdinaryCoordinateLane
          M R.scale (E : ℝ) k j eta =
        goodHeadTunedOrdinaryCoordinateLane
          M R.scale (E : ℝ) k j₀ eta := by
    simp only [goodHeadTunedOrdinaryCoordinateLane,
      goodHeadTunedCoordinateLane, goodHeadTunedCoordinateCoeff,
      vecNormSq_basisVec]
  have hrareEq (j : Fin d) (eta : CutoffSample d) :
      goodHeadTunedRareCoordinateLane M R.scale (E : ℝ) k j eta =
        goodHeadTunedRareCoordinateLane M R.scale (E : ℝ) k j₀ eta := by
    simp only [goodHeadTunedRareCoordinateLane,
      goodHeadTunedCoordinateLane, goodHeadTunedCoordinateCoeff,
      vecNormSq_basisVec]
  have hordinaryNonneg : ∀ omega, 0 ≤ ordinary omega := by
    intro omega
    dsimp only [ordinary]
    exact mul_nonneg (Nat.cast_nonneg d) (by
      rw [goodHeadTunedOrdinaryCoordinateLane]
      exact mul_nonneg (by norm_num)
        (good_head_tuned_coordinate_lane_nonneg
          M R.scale (E : ℝ) k j₀ (translateCutoffSample shift omega)))
  have hrareNonneg : ∀ omega, 0 ≤ rare omega := by
    intro omega
    dsimp only [rare]
    exact mul_nonneg (Nat.cast_nonneg d)
      (good_head_tuned_rare_coordinate_lane_nonneg
        M R.scale (E : ℝ) k j₀ (translateCutoffSample shift omega))
  have hordinaryMeasurable : Measurable ordinary := by
    dsimp only [ordinary]
    exact (((measurable_good_head_tuned_coordinate_lane
      M R.scale (E : ℝ) k j₀).const_mul _).comp
        (measurable_translateCutoffSample shift)).const_mul _
  have hrareMeasurable : Measurable rare := by
    dsimp only [rare]
    exact ((measurable_good_head_tuned_rare_coordinate_lane
      M R.scale (E : ℝ) k j₀).comp
        (measurable_translateCutoffSample shift)).const_mul _
  obtain ⟨hpoint, hENNRealEq, hENNRealDom, hordinaryOrlicz⟩ :=
    @upperHeadSharpSplit_momentBounds1 (d) (M) (m) (k) (R) (hR) (E) (hstate) (sigma) (hsigma0)
      (hsigma) (hEgamma) (hd) (hmaxAux) (hordinaryEq) (hrareEq) (hordinaryNonneg) (hrareNonneg)
  have hrareOrlicz : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3)) rare rareScale := by
    have hcoordinate :=
      isBigOWith_upperProfileTarget_good_head_tuned_rare_coordinate_lane_comp
        M hR hstate hsigma0 hsigma hmaxAux hEgamma j₀
    have htrace := hcoordinate.const_mul (Nat.cast_nonneg d)
    simpa only [rare, rareScale, shift] using htrace
  have hcoordinateScale0 : 0 ≤
      goodHeadTunedCoordinateScale M (E : ℝ) sigma k j₀ :=
    good_head_tuned_coordinate_scale_nonneg
      M (E : ℝ) sigma k j₀ hsigma0 hsigma
  have hordinaryScale0 : 0 ≤ ordinaryScale := by
    dsimp only [ordinaryScale, goodHeadTunedOrdinaryCoordinateScale]
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg (by norm_num) hcoordinateScale0)
  have hrareScale0 : 0 ≤ rareScale := by
    dsimp only [rareScale, goodHeadTunedRareCoordinateScale]
    exact mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg
        (mul_nonneg (by positivity)
          (upperHsepResidualScale_pos sigma M.gamma).le)
        hcoordinateScale0)
  have hbudget : max
      (2 * (d : ℝ) * goodHeadTunedCoordinateConst d)
      (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
        upperHsepResidualRate⁻¹) ≤ Cup := by
    have hbranch : 1 + max
        (2 * (d : ℝ) * goodHeadTunedCoordinateConst d)
        (((d : ℝ) * goodHeadTunedRarePrefactor d + 8) *
          upperHsepResidualRate⁻¹) ≤ Cup :=
      (le_max_right _ _).trans houtput
    linarith
  have hordinaryBudget :
      2 * (d : ℝ) * goodHeadTunedCoordinateConst d ≤ Cup :=
    (le_max_left _ _).trans hbudget
  have hcstar0 : 0 ≤
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1).le
  have hordinaryRaw : ordinaryScale ≤
      (2 * (d : ℝ) * goodHeadTunedCoordinateConst d) *
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma := by
    have hcoordinate := good_head_tuned_coordinate_scale_le
      M (E : ℝ) sigma hsigma0 hsigma k j₀
    dsimp only [ordinaryScale, goodHeadTunedOrdinaryCoordinateScale]
    calc
      (d : ℝ) * (2 * goodHeadTunedCoordinateScale
          M (E : ℝ) sigma k j₀) ≤
          (d : ℝ) * (2 *
            (goodHeadTunedCoordinateConst d *
              (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma)) := by
        gcongr
      _ = (2 * (d : ℝ) * goodHeadTunedCoordinateConst d) *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma := by ring
  have hordinaryBase : ordinaryScale ≤
      Cup * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma :=
    hordinaryRaw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hordinaryBudget hcstar0)
      M.shellPrefix.gamma_pos.le)
  have hpow : 1 ≤ (3 : ℝ) ^
      (M.gamma * ((k : ℝ) + 1)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have hgamma1 : M.gamma ≤ 1 :=
    M.shellPrefix.gamma_le_quarter.trans (by norm_num)
  have hordinaryScale : ordinaryScale ≤
      upperSaturatedPerCubeAmplitude Cup
        (Algsuperdiff.Section3.Disorder.cstar M) M.gamma k := by
    calc
      ordinaryScale ≤
          Cup * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma :=
        hordinaryBase
      _ = Cup * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          M.gamma * 1 := by ring
      _ ≤ Cup * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * M.gamma *
          (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (mul_nonneg hCup0.le hcstar0)
            M.shellPrefix.gamma_pos.le)
      _ ≤ upperSaturatedPerCubeAmplitude Cup
          (Algsuperdiff.Section3.Disorder.cstar M) M.gamma k :=
        plainGammaPerCubeAmplitude_le_upperSaturated
          hCup0.le hcstar0 M.shellPrefix.gamma_pos.le hgamma1 k
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  let K : ℝ := (d : ℝ) * goodHeadTunedRarePrefactor d
  have hcstar : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤
      (E : ℝ) := (le_max_right _ _).trans hmax
  have hrareCoordinate := good_head_tuned_rare_coordinate_scale_le_exp
    M hsigma0 hsigma hcstar hEgamma k j₀
  have hrareRaw : rareScale ≤
      K * Real.exp (-(upperHsepResidualRate * X)) := by
    dsimp only [rareScale, K, X]
    calc
      (d : ℝ) * goodHeadTunedRareCoordinateScale
          M (E : ℝ) sigma k j₀ ≤
          (d : ℝ) * (goodHeadTunedRarePrefactor d *
            Real.exp (-(upperHsepResidualRate *
              ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) :=
        mul_le_mul_of_nonneg_left hrareCoordinate (Nat.cast_nonneg d)
      _ = (d : ℝ) * goodHeadTunedRarePrefactor d *
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
    simpa only [K] using good_head_tuned_rare_output_choice houtput
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (Nat.cast_nonneg d)
      (good_head_tuned_rare_prefactor_nonneg hd)
  have hrareScale : rareScale ≤ eps ^ 8 := by
    refine hrareRaw.trans ?_
    dsimp only [eps]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hchoice
  exact ⟨ordinary, rare, ordinaryScale, rareScale,
    hordinaryNonneg, hordinaryMeasurable,
    hrareNonneg, hrareMeasurable, hpoint, hENNRealEq, hENNRealDom,
    hordinaryOrlicz, hordinaryScale0, hordinaryScale,
    hrareOrlicz, hrareScale0, by
      simpa only [eps, X] using hrareScale⟩

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
