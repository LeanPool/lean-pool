/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice

/-!
# UpperCollarBandMeanTunedProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Collar band-mean profile at the source-compatible tuned depth

This file repeats only the collar band-mean layer estimate whose earlier
specialization used coefficient `1`.  Its integer depth is now the internal
choice `collarBandMeanDepth`, with no new caller premise.  The exact collar
carrier and all generic cap/mass interpolation lemmas are reused unchanged.

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
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-- The exact outer band coefficient at the internally selected depth. -/
def probeSharpCollarBandMeanTunedOuter
    (M : ABKModel d) (E : ℝ) (j : Fin d) : ℝ :=
  probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
    (5 * (d : ℝ) ^ 2 *
      waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
        (collarBandMeanDepth M E) ^ 2)

/-- The deterministic Whitney scale at the internally selected depth. -/
def probeSharpCollarBandMeanTunedLayerScale
    (M : ABKModel d) (E : ℝ) (n : ℕ) : ℝ :=
  probeSharpCollarBandMeanOuterConst d *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ)) *
    whitneyDecayRatio ^ n

theorem probeSharpCollarBandMeanTunedOuter_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (E : ℝ) (j : Fin d) :
    0 ≤ probeSharpCollarBandMeanTunedOuter M E j := by
  rw [probeSharpCollarBandMeanTunedOuter]
  exact mul_nonneg
    (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M)
      (vecNormSq_nonneg (basisVec j)))
    (mul_nonneg (by positivity) (sq_nonneg _))

theorem probeSharpCollarBandMeanTunedLayerScale_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (E : ℝ) (n : ℕ) :
    0 ≤ probeSharpCollarBandMeanTunedLayerScale M E n := by
  rw [probeSharpCollarBandMeanTunedLayerScale]
  exact mul_nonneg
    (mul_nonneg
      (probeSharpCollarBandMeanOuterConst_nonneg hd)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity)
              (probeSharpCollarBandMeanCapQuarter_nonneg
                M E (collarBandMeanDepth M E)))
            (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (by norm_num) _)))
    (pow_nonneg whitneyDecayRatio_nonneg n)


/-- The deterministic band mean remains dimension-bounded for the smaller
source-compatible coefficient. -/
theorem probeSharpCollarBandMeanTunedOuter_le_const
    (hd : 2 ≤ d) (M : ABKModel d) {E : ℝ} (hE : 1 ≤ E)
    (hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ))) (j : Fin d) :
    probeSharpCollarBandMeanTunedOuter M E j ≤
      probeSharpCollarBandMeanOuterConst d := by
  have hband := cstarInv_mul_waveBandMean_sq_le
    (A := probeDeepBandMeanAmplitude d) (c := collarBandMeanDepthCoeff d)
    (cstar := Algsuperdiff.Section3.Disorder.cstar M)
    (collarBandMeanDepthCoeff_pos d).le
    (collarBandMeanDepthCoeff_le_one d) hE M.shellPrefix.gamma_pos
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1 hcstarE hEgamma
  have hdim0 := probeSharpBandMeanDimensionConst_nonneg hd
  have hfive : 0 ≤ 5 * (d : ℝ) ^ 2 := by positivity
  rw [probeSharpCollarBandMeanTunedOuter, collarBandMeanDepth,
    vecNormSq_basisVec, mul_one, probeMeanGoodWaveConst,
    probeSharpCollarBandMeanOuterConst,
    probeSharpBandMeanDimensionConst]
  calc
    (1920 * simplexCrudeConst d (1 / 4) *
          probeSimplexMeanSensitivityConst d *
          (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) *
        (5 * (d : ℝ) ^ 2 *
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
            (waveBandDepth (collarBandMeanDepthCoeff d) E M.gamma) ^ 2) =
      (5 * (d : ℝ) ^ 2) *
        (1920 * simplexCrudeConst d (1 / 4) *
          probeSimplexMeanSensitivityConst d) *
        ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
            (waveBandDepth (collarBandMeanDepthCoeff d) E M.gamma) ^ 2) := by ring
    _ ≤ (5 * (d : ℝ) ^ 2) *
        (1920 * simplexCrudeConst d (1 / 4) *
          probeSimplexMeanSensitivityConst d) *
        waveBandConst (probeDeepBandMeanAmplitude d) :=
      mul_le_mul_of_nonneg_left hband (mul_nonneg hfive hdim0)
    _ = _ := by ring

/-- The collar/frame core bound at an arbitrary deterministic integer depth.
The proof is the same source algebra as the coefficient-one specialization;
no size property of `k₀` is used here. -/
theorem probeSharpCollarBandMeanLayerCore_le_atDepth
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (k₀ n : ℕ) (omega : CutoffSample d) :
    probeSharpCollarBandMeanLayerCore M R.scale E k₀ n (m - 1)
        (superposedGradConst d) omega ≤
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M E k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ)) *
        slstarPowerTerm M R.scale E bfaProfileB M.gamma omega *
        whitneyDecayRatio ^ n := by
  let hs := hsep M R.scale E bfaProfileB omega
  let c := bfaAfterBandLayerCeil n
  have hframe := probeSharpFramedAfterBandMultiplier_descendant_eq
    M hR E bfaProfileB k₀ n omega
  have hbad := sqrt_assemblyBad_le_collarBandMean_fourthRoot
    M E hs k₀ n
  rw [collarBandMean_fourthRoot_eq] at hbad
  have hceil : c ≤ n := by
    simpa only [c, bfaAfterBandLayerCeil] using bfaAfterBandLayerCeil_le n
  have hgap : n + c ≤ 2 * n + 1 := by omega
  have hdecay := weighted_whitney_layer_factor_le
    (b := bfaProfileB) (gamma := (0 : ℝ)) bfaProfileB_pos.le
    (by norm_num [bfaProfileB]) (by norm_num) (by linarith [bfaProfileB_pos])
    n (n + c) hgap
  have hneg : (3 : ℝ) ^
      (M.gamma * (-((k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ)))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hsum : 0 ≤ (k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ) := by
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos M.shellPrefix.gamma_pos.le
      (neg_nonpos.mpr hsum)
  have hfactor0 : 0 ≤ probeSharpFramedCollarFactor
      M R.scale E bfaProfileB k₀ n (superposedGradConst d) omega :=
    probeSharpFramedCollarFactor_nonneg
      M R.scale E bfaProfileB k₀ n (superposedGradConst d) omega
  have hframe0 : 0 ≤ probeSharpFramedAfterBandMultiplier
      M R.scale E bfaProfileB k₀ n (m - 1) omega :=
    probeSharpFramedAfterBandMultiplier_nonneg
      M R.scale E bfaProfileB k₀ n (m - 1) omega
  have hreplace :
      probeSharpCollarBandMeanLayerCore M R.scale E k₀ n (m - 1)
          (superposedGradConst d) omega ≤
        probeSharpFramedCollarFactor M R.scale E bfaProfileB k₀ n
            (superposedGradConst d) omega *
          (probeSharpCollarBandMeanCapQuarter M E k₀ *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (-(n : ℝ) / 4)) *
          probeSharpFramedAfterBandMultiplier
            M R.scale E bfaProfileB k₀ n (m - 1) omega := by
    rw [probeSharpCollarBandMeanLayerCore]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbad hfactor0) hframe0
  refine hreplace.trans ?_
  rw [probeSharpFramedCollarFactor, hframe, whitneyScale,
    whitneyScaleSeq]
  change
    (4 * (superposedGradConst d ^ 2 *
          (3 : ℝ) ^ (2 * (bfaProfileB *
            ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ))))) *
        (probeSharpCollarBandMeanCapQuarter M E k₀ *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (-(n : ℝ) / 4)) *
        (3 : ℝ) ^ (M.gamma *
          ((hs : ℝ) -
            ((k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ))))) ≤ _
  have hsplit :
      (3 : ℝ) ^ (2 * (bfaProfileB *
            ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ)))) *
          (3 : ℝ) ^ (M.gamma *
            ((hs : ℝ) - ((k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ)))) =
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
          slstarPowerTerm M R.scale E bfaProfileB M.gamma omega *
          (3 : ℝ) ^ (2 * bfaProfileB * ((n + c : ℕ) : ℝ)) *
          (3 : ℝ) ^
            (M.gamma * (-((k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ)))) := by
    rw [slstarPowerTerm]
    repeat' rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hfixed : 0 ≤ 4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M E k₀ *
      probeSharpCollarBandMeanMassQuarterConst d := by
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (probeSharpCollarBandMeanCapQuarter_nonneg M E k₀))
      (probeSharpCollarBandMeanMassQuarterConst_nonneg d)
  have hpower0 : 0 ≤ slstarPowerTerm
      M R.scale E bfaProfileB M.gamma omega :=
    slstarPowerTerm_nonneg M R.scale E bfaProfileB M.gamma omega
  have hkpow0 : 0 ≤ (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hdecay' :
      (3 : ℝ) ^ (-(n : ℝ) / 4) *
          (3 : ℝ) ^ (2 * bfaProfileB * ((n + c : ℕ) : ℝ)) ≤
        (3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n := by
    simpa only [add_zero] using hdecay
  calc
    _ =
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M E k₀ *
        probeSharpCollarBandMeanMassQuarterConst d) *
        (((3 : ℝ) ^ (2 * (bfaProfileB *
              ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ)))) *
            (3 : ℝ) ^ (M.gamma *
              ((hs : ℝ) -
                ((k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ))))) *
          (3 : ℝ) ^ (-(n : ℝ) / 4)) := by ring
    _ =
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M E k₀ *
        probeSharpCollarBandMeanMassQuarterConst d) *
        ((3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
          slstarPowerTerm M R.scale E bfaProfileB M.gamma omega) *
        ((3 : ℝ) ^ (-(n : ℝ) / 4) *
          (3 : ℝ) ^ (2 * bfaProfileB * ((n + c : ℕ) : ℝ))) *
        (3 : ℝ) ^
          (M.gamma * (-((k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ)))) := by
      rw [hsplit]
      ring
    _ ≤ (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M E k₀ *
        probeSharpCollarBandMeanMassQuarterConst d) *
        ((3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
          slstarPowerTerm M R.scale E bfaProfileB M.gamma omega) *
        ((3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n) * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hdecay'
          (mul_nonneg hfixed (mul_nonneg hkpow0 hpower0)))
        hneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg
          (mul_nonneg hfixed (mul_nonneg hkpow0 hpower0))
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (pow_nonneg whitneyDecayRatio_nonneg n)))
    _ = _ := by ring

/-- The literal ninth named summand at the source-compatible depth. -/
theorem probeSharpFramedCollarWavePart_bandMeanTuned_le
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : ℝ} (hE : 1 ≤ E)
    (hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E)
    (hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarWavePart M R.scale E bfaProfileB
        (collarBandMeanDepth M E) n (m - 1) (basisVec j)
        (superposedGradConst d)
        (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma
          (collarBandMeanDepth M E) ^ 2) omega ≤
      probeSharpCollarBandMeanTunedLayerScale M E n *
        slstarPowerTerm M R.scale E bfaProfileB M.gamma omega := by
  rw [probeSharpFramedCollarWavePart_bandMean_eq,
    ← probeSharpCollarBandMeanTunedOuter]
  have houter := probeSharpCollarBandMeanTunedOuter_le_const
    hd M hE hcstarE hEgamma j
  have hcore := probeSharpCollarBandMeanLayerCore_le_atDepth
    M hR E (collarBandMeanDepth M E) n omega
  have houter0 := probeSharpCollarBandMeanTunedOuter_nonneg hd M E j
  have hcore0 := probeSharpCollarBandMeanLayerCore_nonneg
    M R.scale E (collarBandMeanDepth M E) n (m - 1)
      (superposedGradConst d) omega
  calc
    probeSharpCollarBandMeanTunedOuter M E j *
        probeSharpCollarBandMeanLayerCore M R.scale E
          (collarBandMeanDepth M E) n (m - 1)
          (superposedGradConst d) omega ≤
      probeSharpCollarBandMeanOuterConst d *
        ((4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ)) *
          slstarPowerTerm M R.scale E bfaProfileB M.gamma omega *
          whitneyDecayRatio ^ n) :=
      mul_le_mul houter hcore hcore0
        (probeSharpCollarBandMeanOuterConst_nonneg hd)
    _ = _ := by rw [probeSharpCollarBandMeanTunedLayerScale]; ring

theorem summable_probeSharpCollarBandMeanTunedLayerScale
    (M : ABKModel d) (E : ℝ) :
    Summable fun n : ℕ => probeSharpCollarBandMeanTunedLayerScale M E n := by
  rw [show (fun n : ℕ => probeSharpCollarBandMeanTunedLayerScale M E n) =
      fun n : ℕ =>
        (probeSharpCollarBandMeanOuterConst d *
          (4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (2 * bfaProfileB * (collarBandMeanDepth M E : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ))) *
          whitneyDecayRatio ^ n by
    funext n
    rw [probeSharpCollarBandMeanTunedLayerScale]]
  exact (summable_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one).mul_left _

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
