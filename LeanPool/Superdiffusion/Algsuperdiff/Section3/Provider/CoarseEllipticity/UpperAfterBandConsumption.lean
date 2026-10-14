/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandOrdinaryProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHeadSharpCoordinate
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability

/-!
# UpperAfterBandConsumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity
open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section
variable {d : ℕ}
private theorem probeSharpCollarBandMeanLayerCore_le_retainFrame
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (k₀ n : ℕ) (omega : CutoffSample d) :
    probeSharpCollarBandMeanLayerCore M R.scale E k₀ n (m - 1)
        (superposedGradConst d) omega ≤
      ((4 * superposedGradConst d ^ 2 *
          probeSharpCollarBandMeanCapQuarter M E k₀ *
          probeSharpCollarBandMeanMassQuarterConst d *
          (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
          (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n) *
        slstarPowerTerm M R.scale E bfaProfileB M.gamma omega *
        (3 : ℝ) ^ (M.gamma *
          (-((k : ℝ) + (n : ℝ) +
            (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ)))) := by
  let hs := hsep M R.scale E bfaProfileB omega
  let c := bfaAfterBandLayerCeil n
  have hframe := probeSharpFramedAfterBandMultiplier_descendant_eq
    M hR E bfaProfileB k₀ n omega
  have hbad := sqrt_assemblyBad_le_collarBandMean_fourthRoot M E hs k₀ n
  rw [collarBandMean_fourthRoot_eq] at hbad
  have hceil : c ≤ n := by
    simpa only [c, bfaAfterBandLayerCeil] using bfaAfterBandLayerCeil_le n
  have hgap : n + c ≤ 2 * n + 1 := by omega
  have hdecay := weighted_whitney_layer_factor_le
    (b := bfaProfileB) (gamma := (0 : ℝ)) bfaProfileB_pos.le
    (by norm_num [bfaProfileB]) (by norm_num) (by linarith [bfaProfileB_pos])
    n (n + c) hgap
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
  rw [probeSharpFramedCollarFactor, hframe, whitneyScale, whitneyScaleSeq]
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
        ((3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n) *
        (3 : ℝ) ^
          (M.gamma * (-((k : ℝ) + (n : ℝ) + (c : ℝ) + (k₀ : ℝ)))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdecay'
          (mul_nonneg hfixed (mul_nonneg hkpow0 hpower0)))
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      dsimp only [c]
      ring
private theorem whitney_frame_afterBandExactScale_sq_le
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : ℝ} (hE : 1 ≤ E) (hgamma20 : M.gamma ≤ 1 / 20)
    (n : ℕ) :
    let k₀ := collarBandMeanDepth M E
    let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
    let rho : ℝ := (3 : ℝ) ^ (-(1 / 40 : ℝ))
    whitneyDecayRatio ^ n *
        (3 : ℝ) ^ (M.gamma *
          (-((k : ℝ) + (n : ℝ) +
            (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ)))) *
        probeSharpAfterBandExactScale M ell k₀ m ^ 2 ≤
      54 * waveSharpUpperConst d ^ 2 *
        (((n + 1 : ℕ) : ℝ) * rho ^ n) *
        (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) := by
  dsimp only
  let k₀ := collarBandMeanDepth M E
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let a := bfaAfterBandLayerCeil n
  let rho : ℝ := (3 : ℝ) ^ (-(1 / 40 : ℝ))
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
      (3 : ℝ) ^ (M.gamma *
          (-((k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ)))) *
          (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ))) =
        (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma *
            (1 + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) := by
    rw [hheight]
    repeat' rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hceilNat : a ≤ n := by
    dsimp only [a]
    exact bfaAfterBandLayerCeil_le n
  have hceil : (a : ℝ) ≤ n := by exact_mod_cast hceilNat
  have hgamma0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hsat := bfaAfterBandSaturation_le hgamma0 k n
  have hsat' : min 1
      (M.gamma * (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) ≤
        (2 * ((n + 1 : ℕ) : ℝ)) *
          min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) := by
    simpa only [a] using hsat
  have htargetMin0 : 0 ≤ min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) :=
    le_min zero_le_one
      (mul_nonneg hgamma0 (Nat.cast_nonneg (k + 1)))
  have htargetPow0 : 0 ≤
      (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmin0 : 0 ≤ min 1
      (M.gamma * (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) := by
    exact le_min zero_le_one (mul_nonneg hgamma0 (by positivity))
  let c := collarBandMeanDepthCoeff d
  have ht : 0 ≤ c * (E ^ 2)⁻¹ * M.gamma⁻¹ := by
    exact mul_nonneg
      (mul_nonneg (collarBandMeanDepthCoeff_pos d).le
        (inv_nonneg.mpr (sq_nonneg E)))
      (inv_nonneg.mpr hgamma0)
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
  have hgk₀ : M.gamma * (k₀ : ℝ) ≤ 2 := by
    have hdepth' : M.gamma * (k₀ : ℝ) ≤ c * (E ^ 2)⁻¹ + M.gamma := hdepth
    linarith only [hdepth', hcEinv, hgamma20]
  have hna : M.gamma * ((n : ℝ) + (a : ℝ)) ≤
      (1 / 10 : ℝ) * (n : ℝ) := by
    calc
      M.gamma * ((n : ℝ) + (a : ℝ)) ≤
          M.gamma * (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hgamma0
      _ ≤ (1 / 20 : ℝ) * (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hgamma20 (by positivity)
      _ = (1 / 10 : ℝ) * (n : ℝ) := by ring
  have hexponent :
      (-(1 / 8 : ℝ)) * (n : ℝ) +
          M.gamma * (1 + (n : ℝ) + (a : ℝ) + (k₀ : ℝ)) ≤
        3 + (-(1 / 40 : ℝ)) * (n : ℝ) := by
    have hgammaOne : M.gamma * 1 ≤ 1 / 20 := by simpa using hgamma20
    linarith only [hna, hgk₀, hgammaOne]
  have hlayerGrowth :
      whitneyDecayRatio ^ n *
          (3 : ℝ) ^ (M.gamma *
            (1 + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) ≤
        27 * rho ^ n := by
    have hlhs :
        whitneyDecayRatio ^ n *
            (3 : ℝ) ^ (M.gamma *
              (1 + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) =
          (3 : ℝ) ^ ((-(1 / 8 : ℝ)) * (n : ℝ) +
            M.gamma *
              (1 + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) := by
      rw [whitneyDecayRatio, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hrhs : 27 * rho ^ n =
        (3 : ℝ) ^ (3 + (-(1 / 40 : ℝ)) * (n : ℝ)) := by
      dsimp only [rho]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      have h27 : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        norm_num
      rw [h27, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [hlhs, hrhs]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  rw [probeSharpAfterBandExactScale_sq_eq_min M hL, hgap]
  change
    whitneyDecayRatio ^ n *
        (3 : ℝ) ^ (M.gamma *
          (-((k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ)))) *
        (waveSharpUpperConst d ^ 2 *
          min 1 (M.gamma * (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
          (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ)))) ≤ _
  calc
    _ = waveSharpUpperConst d ^ 2 *
        min 1 (M.gamma *
          (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
        whitneyDecayRatio ^ n *
        ((3 : ℝ) ^ (M.gamma *
          (-((k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ)))) *
          (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ)))) := by ring
    _ = waveSharpUpperConst d ^ 2 *
        min 1 (M.gamma *
          (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
        whitneyDecayRatio ^ n *
        ((3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma *
            (1 + (n : ℝ) + (a : ℝ) + (k₀ : ℝ)))) := by rw [hpow]
    _ = waveSharpUpperConst d ^ 2 *
        (min 1 (M.gamma *
          (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) *
        (whitneyDecayRatio ^ n *
          (3 : ℝ) ^ (M.gamma *
            (1 + (n : ℝ) + (a : ℝ) + (k₀ : ℝ)))) := by ring
    _ ≤ waveSharpUpperConst d ^ 2 *
        ((2 * ((n + 1 : ℕ) : ℝ) *
          min 1 (M.gamma * ((k + 1 : ℕ) : ℝ))) *
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) *
        (27 * rho ^ n) := by
      have hinner := mul_le_mul
        (mul_le_mul_of_nonneg_right hsat' htargetPow0)
        hlayerGrowth
        (mul_nonneg (pow_nonneg whitneyDecayRatio_nonneg n)
          (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg
          (mul_nonneg (by positivity) htargetMin0) htargetPow0)
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hinner (sq_nonneg (waveSharpUpperConst d)))
    _ = _ := by ring
/-- The tuned collar after-band coordinate lane at a strict descendant. -/
def probeSharpFramedCollarAfterBandCoordinateLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (omega : CutoffSample d) : ℝ :=
  ∑' n : ℕ,
    probeSharpFramedCollarWavePart M R.scale E bfaProfileB
      (collarBandMeanDepth M E) n (m - 1) (basisVec j)
      (superposedGradConst d)
      (fun eta => probeSharpAfterBandTerm M R.scale
        (probeSharpLayerAnchor R.scale bfaProfileB
          (collarBandMeanDepth M E) n)
        (collarBandMeanDepth M E) m eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega)
/-- The literal finite-coordinate collar after-band trace. -/
def probeSharpFramedCollarAfterBandTraceLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (omega : CutoffSample d) : ℝ :=
  ∑ j : Fin d,
    probeSharpFramedCollarAfterBandCoordinateLane M m R E j omega
private theorem probeSharpFramedCollarAfterBandLayer_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (root : ℤ) (E : ℝ)
    (k₀ n : ℕ) (i L : ℤ) (j : Fin d) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
      (basisVec j) (superposedGradConst d)
      (fun eta => probeSharpAfterBandTerm M root
        (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ L eta ^ 2)
      omega :=
  probeSharpFramedCollarWavePart_nonneg hd M root E bfaProfileB k₀ n i
    (basisVec j) (superposedGradConst d) (fun _eta => sq_nonneg _) omega
private theorem measurable_probeSharpFramedCollarAfterBandLayer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ)
    (i L : ℤ) (j : Fin d) :
    Measurable fun omega : CutoffSample d =>
      probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
        (basisVec j) (superposedGradConst d)
        (fun eta => probeSharpAfterBandTerm M root
          (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ L eta ^ 2)
        omega := by
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  have hterm : Measurable fun omega : CutoffSample d =>
      probeSharpAfterBandTerm M root ell k₀ L omega ^ 2 :=
    (measurable_probeSharpAfterBandTerm_exactScale M root ell k₀ L).pow_const 2
  have hcore := measurable_probeSharpCollarBandMeanLayerCore
    M root E k₀ n i (superposedGradConst d)
  rw [show
    (fun omega : CutoffSample d =>
      probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
        (basisVec j) (superposedGradConst d)
        (fun eta => probeSharpAfterBandTerm M root
          (probeSharpLayerAnchor root bfaProfileB k₀ n) k₀ L eta ^ 2)
        omega) =
      fun omega =>
        (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
          (5 * (d : ℝ) ^ 2)) *
        (probeSharpAfterBandTerm M root ell k₀ L omega ^ 2) *
        probeSharpCollarBandMeanLayerCore M root E k₀ n i
          (superposedGradConst d) omega by
    funext omega
    simp only [probeSharpFramedCollarWavePart,
      probeSharpCollarBandMeanLayerCore, ell]
    ring]
  exact (measurable_const.mul hterm).mul hcore
theorem probeSharpFramedCollarAfterBandCoordinateLane_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (E : ℝ) (j : Fin d) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarAfterBandCoordinateLane M m R E j omega := by
  rw [probeSharpFramedCollarAfterBandCoordinateLane]
  exact tsum_nonneg fun n =>
    probeSharpFramedCollarAfterBandLayer_nonneg hd M R.scale E
      (collarBandMeanDepth M E) n (m - 1) m j
      (translateCutoffSample (triadicCubeShift R) omega)
theorem measurable_probeSharpFramedCollarAfterBandCoordinateLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) :
    Measurable (probeSharpFramedCollarAfterBandCoordinateLane M m R E j) := by
  have hnn :=
    (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      ((measurable_probeSharpFramedCollarAfterBandLayer M R.scale E
          (collarBandMeanDepth M E) n (m - 1) m j).comp
        (measurable_translateCutoffSample (triadicCubeShift R))).real_toNNReal).coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [probeSharpFramedCollarAfterBandCoordinateLane, NNReal.coe_tsum]
  apply tsum_congr
  intro n
  simp only [Function.comp_apply]
  rw [Real.toNNReal_of_nonneg
    (probeSharpFramedCollarAfterBandLayer_nonneg M.shellPrefix.dimension M
      R.scale E (collarBandMeanDepth M E) n (m - 1) m j
      (translateCutoffSample (triadicCubeShift R) omega))]
  rfl
theorem probeSharpFramedCollarAfterBandCoordinateLane_eq
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j j' : Fin d) :
    probeSharpFramedCollarAfterBandCoordinateLane M m R E j =
      probeSharpFramedCollarAfterBandCoordinateLane M m R E j' := by
  funext omega
  rw [probeSharpFramedCollarAfterBandCoordinateLane,
    probeSharpFramedCollarAfterBandCoordinateLane]
  apply tsum_congr
  intro n
  simp only [probeSharpFramedCollarWavePart, vecNormSq_basisVec]
theorem probeSharpFramedCollarAfterBandTraceLane_eq_dimension_mul
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ)
    (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarAfterBandTraceLane M m R E omega =
      (d : ℝ) *
        probeSharpFramedCollarAfterBandCoordinateLane M m R E j omega := by
  rw [probeSharpFramedCollarAfterBandTraceLane]
  have hall : ∀ j' : Fin d,
      probeSharpFramedCollarAfterBandCoordinateLane M m R E j' omega =
        probeSharpFramedCollarAfterBandCoordinateLane M m R E j omega :=
    fun j' => congrFun
      (probeSharpFramedCollarAfterBandCoordinateLane_eq M m R E j' j) omega
  simp_rw [hall]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
theorem probeSharpFramedCollarAfterBandTraceLane_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (m : ℤ) (R : TriadicCube d)
    (E : ℝ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarAfterBandTraceLane M m R E omega := by
  rw [probeSharpFramedCollarAfterBandTraceLane]
  exact Finset.sum_nonneg fun j _ =>
    probeSharpFramedCollarAfterBandCoordinateLane_nonneg hd M m R E j omega
theorem measurable_probeSharpFramedCollarAfterBandTraceLane
    (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (E : ℝ) :
    Measurable (probeSharpFramedCollarAfterBandTraceLane M m R E) := by
  change Measurable fun omega : CutoffSample d =>
    ∑ j : Fin d,
      probeSharpFramedCollarAfterBandCoordinateLane M m R E j omega
  exact Finset.measurable_fun_sum Finset.univ fun j _ =>
    measurable_probeSharpFramedCollarAfterBandCoordinateLane M m R E j
private theorem collarAfterBand_coordinateTermBound :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d},
      R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ)) →
        ∀ {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ},
          (0 : ℝ) < sigma →
            sigma ≤ (1 / 2 : ℝ) →
              (2 : ℕ) ≤ d →
                ∀ (j₀ : Fin d),
                  let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
                  let rho : ℝ := (3 : ℝ) ^ (-(1 / 40 : ℝ));
                  let F : ℝ :=
                    probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                      ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                        probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ *
                            probeSharpCollarBandMeanMassQuarterConst d *
                          (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ)) *
                        (3 : ℝ) ^ (1 / 16 : ℝ));
                  let A₀ : ℝ :=
                    F * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * ((54 : ℝ) *
                      waveSharpUpperConst d ^ (2 : ℕ)));
                  let target : ℝ :=
                    min (1 : ℝ) (M.gamma * (↑(k + (1 : ℕ)) : ℝ)) * (3 : ℝ) ^ (M.gamma * (↑(k + (1
                      : ℕ)) : ℝ));
                  let ell : ℕ → ℤ := fun (n : ℕ) => probeSharpLayerAnchor R.scale bfaProfileB k₀ n;
                  let P : CutoffSample d → ℝ := fun (omega : CutoffSample d) =>
                    slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma
                      (translateCutoffSample (triadicCubeShift R) omega);
                  let _ : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
                    probeSharpAfterBandTerm M R.scale (ell n) k₀ m (translateCutoffSample
                      (triadicCubeShift R) omega) ^
                      (2 : ℕ);
                  let _ : ℕ → ℝ := fun (n : ℕ) => probeSharpAfterBandExactScale M (ell n) k₀ m ^
                    (2 : ℕ);
                  let _ : ℕ → ℝ := fun (n : ℕ) =>
                    F * whitneyDecayRatio ^ n *
                      (3 : ℝ) ^ (M.gamma * -((↑k : ℝ) + (↑n : ℝ) + (↑(bfaAfterBandLayerCeil n) :
                        ℝ) + (↑k₀ : ℝ)));
                  let B : ℕ → ℝ := fun (n : ℕ) => A₀ * ((↑(n + (1 : ℕ)) : ℝ) * rho ^ n) * target;
                  let X : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
                    probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 :
                      ℤ)) (basisVec j₀)
                      (superposedGradConst d)
                      (fun (eta : CutoffSample d) => probeSharpAfterBandTerm M R.scale (ell n) k₀
                        m eta ^ (2 : ℕ))
                      (translateCutoffSample (triadicCubeShift R) omega);
                  R.scale = m - (1 : ℤ) - (↑k : ℤ) →
                    M.gamma ≤ (1 / 20 : ℝ) →
                      M.gamma / (2 : ℝ) ≤ bfaProfileB * sigma →
                        let alpha : ℝ :=
                          upperProfileBaseSigma sigma /
                            (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) / bfaProfileB);
                        let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^
                          bfaPower M.gamma bfaProfileB;
                        let G : ℝ := Ch04.gammaProductConst alpha (1 : ℝ);
                        IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma
                          alpha)
                            (fun (omega : CutoffSample d) =>
                              slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma
                                (translateCutoffSample (triadicCubeShift R) omega))
                            AP →
                          (∀ (omega : CutoffSample d), (0 : ℝ) ≤ P omega) →
                            (0 : ℝ) ≤ AP →
                              G * AP ≤ (64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) →
                                (0 : ℝ) < probeMeanGoodWaveConst M →
                                  (0 : ℝ) < F →
                                    ∀ (n : ℕ),
                                      IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
                                        (gammaSigma (upperProfileTargetSigma sigma)) (X n) (B
                                          n) := by
  intro d M m k R hR E sigma hsigma0 hsigma _ j₀ k₀ rho F A₀ target ell P T AT D B X hscale
    hgamma20 hgammaHalf alpha AP G hP hP0 hAP0 hGAP hmean hF n
  have hL : ell n + (k₀ : ℤ) < m := by
    dsimp only [ell]
    rw [probeSharpLayerAnchor, hscale]
    omega
  have hrawT := isBigOWith_gammaSigma_one_probeSharpAfterBandTerm_sq_exactScale
    (m := R.scale) (ell := ell n) (L := m) (k₀ := k₀) M hL
  have hTbaseMeas : Measurable fun omega : CutoffSample d =>
      probeSharpAfterBandTerm M R.scale (ell n) k₀ m omega ^ 2 :=
    (measurable_probeSharpAfterBandTerm_exactScale
      M R.scale (ell n) k₀ m).pow_const 2
  have hT := Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
    M (triadicCubeShift R) hTbaseMeas hrawT
  have hT0 : ∀ omega, 0 ≤ T n omega := fun omega => by
    dsimp only [T]
    positivity
  have hAT0 : 0 ≤ AT n := by dsimp only [AT]; positivity
  have hproduct : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (fun omega => P omega * T n omega) (G * AP * AT n) := by
    simpa only [P, T, AT, G, alpha, AP] using
      (isBigOWith_upperProfileTarget_collarPower_mul_one
        (mu := (cutoffSampleLaw M).toMeasure)
        (sigma := sigma) (gamma := M.gamma / 2) (b := bfaProfileB)
        hsigma0 hsigma (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num))
        bfaProfileB_pos hgammaHalf hAP0 hAT0 hP0 (hT0) hP hT)
  have hD0 : 0 ≤ D n := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg hF.le (pow_nonneg whitneyDecayRatio_nonneg n))
      (Real.rpow_nonneg (by norm_num) _)
  have hmajor := hproduct.const_mul hD0
  have hpoint : ∀ omega, X n omega ≤ D n * (P omega * T n omega) := by
    intro omega
    have hcore := probeSharpCollarBandMeanLayerCore_le_retainFrame
      M hR (E : ℝ) k₀ n
        (translateCutoffSample (triadicCubeShift R) omega)
    let outer : ℝ := probeMeanGoodWaveConst M * vecNormSq (basisVec j₀) *
      (5 * (d : ℝ) ^ 2)
    let core : ℝ := probeSharpCollarBandMeanLayerCore M R.scale (E : ℝ)
      k₀ n (m - 1) (superposedGradConst d)
      (translateCutoffSample (triadicCubeShift R) omega)
    have houter0 : 0 ≤ outer := by
      dsimp only [outer]
      exact mul_nonneg
        (mul_nonneg hmean.le (vecNormSq_nonneg (basisVec j₀)))
        (by positivity)
    have heq : X n omega = outer * T n omega * core := by
      dsimp only [X, outer, T, core, ell]
      simp only [probeSharpFramedCollarWavePart,
        probeSharpCollarBandMeanLayerCore]
      ring
    rw [heq]
    calc
      outer * T n omega * core ≤
          outer * T n omega *
            (((4 * superposedGradConst d ^ 2 *
                probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
                probeSharpCollarBandMeanMassQuarterConst d *
                (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
                (3 : ℝ) ^ (1 / 16 : ℝ)) * whitneyDecayRatio ^ n) *
              P omega *
              (3 : ℝ) ^ (M.gamma *
                (-((k : ℝ) + (n : ℝ) +
                  (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ))))) :=
        mul_le_mul_of_nonneg_left hcore (mul_nonneg houter0 (hT0 omega))
      _ = D n * (P omega * T n omega) := by
        dsimp only [D, F, outer, P]
        rw [vecNormSq_basisVec, mul_one]
        ring
  have hraw : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma)) (X n)
      (D n * (G * AP * AT n)) :=
    isBigOWith_gammaSigma_of_le hpoint (by
      simpa only [mul_assoc] using hmajor)
  have hWT := whitney_frame_afterBandExactScale_sq_le
    M hR E.property hgamma20 n
  have hscaleB : D n * (G * AP * AT n) ≤ B n := by
    have hH0 : 0 ≤ 64 * superposedFluxHsepConst ^ (3 : ℝ) :=
      mul_nonneg (by norm_num)
        (Real.rpow_nonneg superposedFluxHsepConst_pos.le _)
    calc
      D n * (G * AP * AT n) =
          F * (G * AP) *
            (whitneyDecayRatio ^ n *
              (3 : ℝ) ^ (M.gamma *
                (-((k : ℝ) + (n : ℝ) +
                  (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ)))) *
              AT n) := by
        dsimp only [D]
        ring
      _ ≤ F * (64 * superposedFluxHsepConst ^ (3 : ℝ)) *
            (54 * waveSharpUpperConst d ^ 2 *
              (((n + 1 : ℕ) : ℝ) * rho ^ n) * target) := by
        refine mul_le_mul
          (mul_le_mul_of_nonneg_left hGAP hF.le) ?_ ?_ ?_
        · simpa only [AT, ell, k₀, rho, target] using hWT
        · exact mul_nonneg
            (mul_nonneg (pow_nonneg whitneyDecayRatio_nonneg n)
              (Real.rpow_nonneg (by norm_num) _)) hAT0
        · exact mul_nonneg hF.le hH0
      _ = B n := by
        dsimp only [B, A₀]
        ring
  exact hraw.mono_scale hscaleB

private theorem upperAfterBandConsumption_momentBounds1 :
    ∀ {d : ℕ} (M : ABKModel d) {R : TriadicCube d} {E : { E : ℝ // (1 : ℝ) ≤ E }} {sigma : ℝ},
    (0 : ℝ) < sigma →
    sigma ≤ (1 / 2 : ℝ) →
    (2 : ℕ) ≤ d →
    let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
    let F : ℝ :=
    probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
    ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) k₀ *
    probeSharpCollarBandMeanMassQuarterConst d *
    (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ)) *
    (3 : ℝ) ^ (1 / 16 : ℝ));
    let A₀ : ℝ := F * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * ((54 : ℝ) *
      waveSharpUpperConst d ^ (2 : ℕ)));
    let P : CutoffSample d → ℝ := fun (omega : CutoffSample d) =>
    slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma (translateCutoffSample
      (triadicCubeShift R) omega);
    (0 : ℝ) < upperProfileSigma sigma →
    upperProfileSigma sigma ≤ (1 / 8 : ℝ) →
    M.gamma / (2 : ℝ) ≤ bfaProfileB * sigma →
    M.gamma ≤ bfaProfileB →
    let alpha : ℝ :=
    upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) * bfaProfileB) /
      bfaProfileB);
    let AP : ℝ := hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma
      bfaProfileB;
    let G : ℝ := Ch04.gammaProductConst alpha (1 : ℝ);
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
    (gammaSigma (bfaTau (upperProfileSigma sigma) M.gamma bfaProfileB))
    (slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma)
    (hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB) →
    bfaTau (upperProfileSigma sigma) M.gamma bfaProfileB = alpha →
    IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma alpha)
    (fun (omega : CutoffSample d) =>
    slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma
    (translateCutoffSample (triadicCubeShift R) omega))
    AP ∧
    (∀ (omega : CutoffSample d), (0 : ℝ) ≤ P omega) ∧
    (0 : ℝ) ≤ AP ∧
    G * AP ≤ (64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) ∧
    (0 : ℝ) < probeMeanGoodWaveConst M ∧ (0 : ℝ) < F ∧ (0 : ℝ) < A₀ := by
  intro d M R E _ hsigma0 hsigma hd k₀ F A₀ P hsigmaProfile0 hsigmaProfileEighth hgammaHalf
    hgammaB alpha AP G hrawP halpha
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
  have hP0 : ∀ omega, 0 ≤ P omega := fun omega => by
    dsimp only [P]
    exact slstarPowerTerm_nonneg M R.scale (E : ℝ) bfaProfileB M.gamma _
  have hAP0 : 0 ≤ AP := by
    dsimp only [AP]
    exact Real.rpow_nonneg (hsepAmplitude_pos _ _).le _
  have hAP : AP ≤ superposedFluxHsepConst ^ (3 : ℝ) := by
    dsimp only [AP]
    exact hsepAmplitude_rpow_bfaPower_le_profile_cube
      hsigmaProfile0 hsigmaProfileEighth hgammaB
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hG : G ≤ 64 := by
    dsimp only [G, alpha]
    exact gamma_product_const_collar_head_le_sixty_four
      hsigma0 hsigma M.shellPrefix.gamma_pos.le hgammaHalf
  have hGAP : G * AP ≤ 64 * superposedFluxHsepConst ^ (3 : ℝ) :=
    mul_le_mul hG hAP hAP0 (by norm_num)
  have hmean : 0 < probeMeanGoodWaveConst M := by
    have hdR : 0 < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
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
    exact mul_pos (mul_pos (mul_pos (by norm_num) hsimplex) hsensitivity)
      (inv_pos.mpr (Algsuperdiff.Section3.Disorder.cstar_characterization M).1)
  have hgrad : 0 < superposedGradConst d :=
    lt_of_lt_of_le zero_lt_one
      (one_le_superposedGradConst (le_trans (by norm_num) hd))
  have hcapEnv : 0 <
      probeSharpCollarBandMeanCapEnvelope M (E : ℝ) k₀ := by
    rw [probeSharpCollarBandMeanCapEnvelope]
    positivity
  have hcap : 0 < probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ := by
    rw [probeSharpCollarBandMeanCapQuarter]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hcapEnv)
  have hmass : 0 < probeSharpCollarBandMeanMassQuarterConst d := by
    rw [probeSharpCollarBandMeanMassQuarterConst]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))
  have hwave : 0 < waveSharpUpperConst d := by
    have hexp1 : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
    have hmoment : 0 < gammaMomentConst 2 :=
      gammaMomentConst_pos (by norm_num)
    have htriangle : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    have hgeom : 0 <
        Algsuperdiff.Section3.Provider.Stream.geometricConcentrationConst :=
      Algsuperdiff.Section3.Provider.Stream.geometricConcentrationConst_pos
    have hdsq : 0 < (d : ℝ) ^ 2 := by
      exact sq_pos_of_pos (by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd))
    rw [waveSharpUpperConst]
    positivity
  have hF : 0 < F := by
    have hdR : 0 < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hd)
    have hfive : 0 < 5 * (d : ℝ) ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hdR)
    have hfixed : 0 < 4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ) := by
      positivity
    dsimp only [F]
    exact mul_pos (mul_pos hmean hfive) hfixed
  have hA₀ : 0 < A₀ := by
    dsimp only [A₀]
    exact mul_pos hF
      (mul_pos
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos superposedFluxHsepConst_pos _))
        (mul_pos (by norm_num) (sq_pos_of_pos hwave)))
  exact ⟨hP, hP0, hAP0, hGAP, hmean, hF, hA₀⟩

private theorem upperAfterBandConsumption_momentBounds2 :
    ∀ {d : ℕ} (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
      (_ : R ∈ descendantsAtScale (originCube d m) (m - (1 : ℤ) - (↑k : ℤ))) {E : { E : ℝ // (1 :
        ℝ) ≤ E }} {sigma : ℝ}
      (_ : (0 : ℝ) < sigma) (_ : sigma ≤ (1 / 2 : ℝ)) (_ : (2 : ℕ) ≤ d),
      let j₀ : Fin d := ⟨(0 : ℕ), (by first | assumption | infer_instance | positivity)⟩;
      let k₀ : ℕ := collarBandMeanDepth M (↑E : ℝ);
      let rho : ℝ := (3 : ℝ) ^ (-(1 / 40 : ℝ));
      let F : ℝ :=
        probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
          ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) * probeSharpCollarBandMeanCapQuarter M (↑E :
            ℝ) k₀ *
                probeSharpCollarBandMeanMassQuarterConst d *
              (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑k₀ : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ));
      let A₀ : ℝ := F * ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * ((54 : ℝ) *
        waveSharpUpperConst d ^ (2 : ℕ)));
      let target : ℝ := min (1 : ℝ) (M.gamma * (↑(k + (1 : ℕ)) : ℝ)) * (3 : ℝ) ^ (M.gamma * (↑(k +
        (1 : ℕ)) : ℝ));
      let ell : ℕ → ℤ := fun (n : ℕ) => probeSharpLayerAnchor R.scale bfaProfileB k₀ n;
      let _ : ℕ → ℝ := fun (n : ℕ) => A₀ * ((↑(n + (1 : ℕ)) : ℝ) * rho ^ n) * target;
      let _ : ℕ → CutoffSample d → ℝ := fun (n : ℕ) (omega : CutoffSample d) =>
        probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 : ℤ)) (basisVec
          j₀)
          (superposedGradConst d)
          (fun (eta : CutoffSample d) => probeSharpAfterBandTerm M R.scale (ell n) k₀ m eta ^ (2 :
            ℕ))
          (translateCutoffSample (triadicCubeShift R) omega);
      ∀ (_ : R.scale = m - (1 : ℤ) - (↑k : ℤ)) (_ : M.gamma ≤ (1 / 20 : ℝ))
        (_ : M.gamma / (2 : ℝ) ≤ bfaProfileB * sigma)
        (_ :
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d))
            (gammaSigma
              (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) *
                bfaProfileB) / bfaProfileB)))
            (fun (omega : CutoffSample d) =>
              slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma (translateCutoffSample
                (triadicCubeShift R) omega))
            (hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB))
        (_ :
          ∀ (omega : CutoffSample d),
            (0 : ℝ) ≤
              (fun (omega : CutoffSample d) =>
                  slstarPowerTerm M R.scale (↑E : ℝ) bfaProfileB M.gamma (translateCutoffSample
                    (triadicCubeShift R) omega))
                omega)
        (_ : (0 : ℝ) ≤ hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma
          bfaProfileB)
        (_ :
          Ch04.gammaProductConst
                (upperProfileBaseSigma sigma / (((2 : ℝ) * (M.gamma / (2 : ℝ)) + (2 : ℝ) *
                  bfaProfileB) / bfaProfileB))
                (1 : ℝ) *
              hsepAmplitude (upperProfileSigma sigma) bfaProfileB ^ bfaPower M.gamma bfaProfileB ≤
            (64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ))
        (_ : (0 : ℝ) < probeMeanGoodWaveConst M)
        (_ :
          (0 : ℝ) <
            probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
              ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                      probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) (collarBandMeanDepth M (↑E :
                        ℝ)) *
                    probeSharpCollarBandMeanMassQuarterConst d *
                  (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑(collarBandMeanDepth M (↑E : ℝ)) : ℝ)) *
                (3 : ℝ) ^ (1 / 16 : ℝ)))
        (_ :
          (0 : ℝ) <
            probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                        probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) (collarBandMeanDepth M (↑E :
                          ℝ)) *
                      probeSharpCollarBandMeanMassQuarterConst d *
                    (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑(collarBandMeanDepth M (↑E : ℝ)) : ℝ)) *
                  (3 : ℝ) ^ (1 / 16 : ℝ)) *
              ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * ((54 : ℝ) * waveSharpUpperConst d ^
                (2 : ℕ)))),
        (∀ᵐ (omega : CutoffSample d) ∂(↑(cutoffSampleLaw M) : Measure (CutoffSample d)),
            ENNReal.ofReal (probeSharpFramedCollarAfterBandTraceLane M m R (↑E : ℝ) omega) =
              ∑ j : Fin d,
                ∑' (n : ℕ),
                  ENNReal.ofReal
                    (probeSharpFramedCollarWavePart M R.scale (↑E : ℝ) bfaProfileB k₀ n (m - (1 :
                      ℤ)) (basisVec j)
                      (superposedGradConst d)
                      (fun (eta : CutoffSample d) => probeSharpAfterBandTerm M R.scale (ell n) k₀
                        m eta ^ (2 : ℕ))
                      (translateCutoffSample (triadicCubeShift R) omega))) ∧
          IsBigOWith (↑(cutoffSampleLaw M) : Measure (CutoffSample d)) (gammaSigma
            (upperProfileTargetSigma sigma))
            (fun (ω : CutoffSample d) => (↑d : ℝ) * probeSharpFramedCollarAfterBandCoordinateLane
              M m R (↑E : ℝ) j₀ ω)
            ((↑d : ℝ) *
              (gammaTriangleConst (upperProfileTargetSigma sigma) *
                ((A₀ * ∑' (n : ℕ), (↑(n + (1 : ℕ)) : ℝ) * rho ^ n) * target))) := by
  intro d M m k R hR E sigma hsigma0 hsigma hd j₀ k₀ rho _ A₀ target ell B X hscale hgamma20
    hgammaHalf hP hP0 hAP0 hGAP hmean hF hA₀
  have htarget : 0 < target := by
    dsimp only [target]
    have hgap0 : 0 < M.gamma * ((k + 1 : ℕ) : ℝ) :=
      mul_pos M.shellPrefix.gamma_pos (by positivity)
    exact mul_pos (lt_min zero_lt_one hgap0)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact Real.rpow_nonneg (by norm_num) _
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hrho1 : rho < 1 := by
    dsimp only [rho]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hrhonorm : ‖rho‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hrho0]
    exact hrho1
  have hpoly := summable_pow_mul_geometric_of_norm_lt_one
    (R := ℝ) 1 hrhonorm
  have hgeom : Summable (fun n : ℕ => rho ^ n) :=
    summable_geometric_of_norm_lt_one hrhonorm
  have hseries : Summable fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * rho ^ n := by
    simpa only [pow_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
      hpoly.add hgeom
  have hBpos : ∀ n, 0 < B n := fun n => by
    dsimp only [B]
    exact mul_pos
      (mul_pos hA₀ (mul_pos (by positivity) (pow_pos hrho n))) htarget
  have hBsum : Summable B := by
    simpa only [B] using (hseries.mul_left A₀).mul_right target
  have hX0 : ∀ n omega, 0 ≤ X n omega := fun n omega => by
    dsimp only [X, k₀, ell, j₀]
    exact probeSharpFramedCollarAfterBandLayer_nonneg hd M R.scale (E : ℝ)
      (collarBandMeanDepth M (E : ℝ)) n (m - 1) m j₀
      (translateCutoffSample (triadicCubeShift R) omega)
  have hXmeas : ∀ n, Measurable (X n) := fun n => by
    dsimp only [X]
    exact (measurable_probeSharpFramedCollarAfterBandLayer
      M R.scale (E : ℝ) k₀ n (m - 1) m j₀).comp
        (measurable_translateCutoffSample (triadicCubeShift R))
  have hterm := @collarAfterBand_coordinateTermBound (d) (M) (m) (k) (R) (hR) (E) (sigma)
    (hsigma0) (hsigma) (hd) (j₀) (hscale) (hgamma20) (hgammaHalf) (hP) (hP0) (hAP0) (hGAP) (hmean)
      (hF)
  have hXsumAE : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, Summable fun n => X n omega :=
    Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
      (upperProfileTargetSigma_pos hsigma0 hsigma) hX0
      (fun n => (hXmeas n).aemeasurable) hBpos hBsum hterm
  have hcoordinate : IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarAfterBandCoordinateLane M m R (E : ℝ) j₀)
      (gammaTriangleConst (upperProfileTargetSigma sigma) *
        (A₀ * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * rho ^ n) * target)) := by
    have hsum : ∑' n, B n =
        A₀ * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * rho ^ n) * target := by
      rw [show B = fun n : ℕ =>
        A₀ * (((n + 1 : ℕ) : ℝ) * rho ^ n) * target by rfl,
        tsum_mul_right, tsum_mul_left]
    have hsumO := Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
      (upperProfileTargetSigma_pos hsigma0 hsigma) hX0 hXmeas hBpos hBsum
      hterm hsum.le
    simpa only [probeSharpFramedCollarAfterBandCoordinateLane, X, k₀, ell,
      j₀] using! hsumO
  have hscaled := hcoordinate.const_mul (Nat.cast_nonneg d)
  have hbridge : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, ENNReal.ofReal
      (probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ) omega) =
      ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal (probeSharpFramedCollarWavePart M
        R.scale (E : ℝ) bfaProfileB k₀ n (m - 1) (basisVec j) (superposedGradConst d)
        (fun eta => probeSharpAfterBandTerm M R.scale (ell n) k₀ m eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega)) := by
    filter_upwards [hXsumAE] with omega hsum
    rw [probeSharpFramedCollarAfterBandTraceLane,
      ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        probeSharpFramedCollarAfterBandCoordinateLane_nonneg
          hd M m R (E : ℝ) j omega)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [probeSharpFramedCollarAfterBandCoordinateLane]
      exact ENNReal.ofReal_tsum_of_nonneg (fun n =>
        probeSharpFramedCollarAfterBandLayer_nonneg hd M R.scale (E : ℝ) k₀ n
          (m - 1) m j (translateCutoffSample (triadicCubeShift R) omega)) (by
        simpa only [X, ell, j₀, probeSharpFramedCollarWavePart, vecNormSq_basisVec]
          using hsum)
  have htraceO := hscaled
  exact ⟨hbridge, htraceO⟩

theorem collar_afterBand_trace_isBigOWith_depthProfile
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    let k₀ := collarBandMeanDepth M (E : ℝ)
    let rho : ℝ := (3 : ℝ) ^ (-(1 / 40 : ℝ))
    let F := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ))
    let A₀ := F *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (54 * waveSharpUpperConst d ^ 2))
    let target := min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
      (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))
    (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, ENNReal.ofReal
      (probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ) omega) =
      ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal (probeSharpFramedCollarWavePart M
        R.scale (E : ℝ) bfaProfileB k₀ n (m - 1) (basisVec j) (superposedGradConst d)
        (fun eta => probeSharpAfterBandTerm M R.scale
          (probeSharpLayerAnchor R.scale bfaProfileB k₀ n) k₀ m eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega))) ∧
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ)) ((d : ℝ) *
        (gammaTriangleConst (upperProfileTargetSigma sigma) *
          (A₀ * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * rho ^ n) * target))) := by
  dsimp only
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let j₀ : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩
  let k₀ := collarBandMeanDepth M (E : ℝ)
  let rho : ℝ := (3 : ℝ) ^ (-(1 / 40 : ℝ))
  let F : ℝ := probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanCapQuarter M (E : ℝ) k₀ *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ))
  let A₀ : ℝ := F *
    (64 * superposedFluxHsepConst ^ (3 : ℝ) *
      (54 * waveSharpUpperConst d ^ 2))
  let target : ℝ := min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
    (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))
  let ell : ℕ → ℤ := fun n =>
    probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let P : CutoffSample d → ℝ := fun omega =>
    slstarPowerTerm M R.scale (E : ℝ) bfaProfileB M.gamma
      (translateCutoffSample (triadicCubeShift R) omega)
  let T : ℕ → CutoffSample d → ℝ := fun n omega =>
    probeSharpAfterBandTerm M R.scale (ell n) k₀ m
      (translateCutoffSample (triadicCubeShift R) omega) ^ 2
  let AT : ℕ → ℝ := fun n =>
    probeSharpAfterBandExactScale M (ell n) k₀ m ^ 2
  let D : ℕ → ℝ := fun n =>
    F * whitneyDecayRatio ^ n *
      (3 : ℝ) ^ (M.gamma *
        (-((k : ℝ) + (n : ℝ) +
          (bfaAfterBandLayerCeil n : ℝ) + (k₀ : ℝ))))
  let B : ℕ → ℝ := fun n =>
    A₀ * (((n + 1 : ℕ) : ℝ) * rho ^ n) * target
  let X : ℕ → CutoffSample d → ℝ := fun n omega =>
    probeSharpFramedCollarWavePart M R.scale (E : ℝ) bfaProfileB
      k₀ n (m - 1) (basisVec j₀) (superposedGradConst d)
      (fun eta => probeSharpAfterBandTerm M R.scale (ell n) k₀ m eta ^ 2)
      (translateCutoffSample (triadicCubeShift R) omega)
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
  have hsigmaProfileEighth : upperProfileSigma sigma ≤ 1 / 8 := by
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
  have hrawP := isBigOWith_gammaSigma_slstarPowerTerm_of_gates
    (m := R.scale) (E := (E : ℝ))
    (sigma := upperProfileSigma sigma) (b := bfaProfileB) (gam := M.gamma)
    M hd E.property hSroot hsigmaProfile0 hsigmaProfileHalf bfaProfileB_pos
    bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20 hinvSq hEb
    hgammaZ M.shellPrefix.gamma_pos
  have halpha :
      bfaTau (upperProfileSigma sigma) M.gamma bfaProfileB = alpha := by
    dsimp only [alpha]
    rw [bfaTau, bfaPower, upperProfileBaseSigma]
    congr 2
    ring
  obtain ⟨hP, hP0, hAP0, hGAP, hmean, hF, hA₀⟩ :=
    @upperAfterBandConsumption_momentBounds1 (d) (M) (R) (E) (sigma) (hsigma0) (hsigma) (hd)
      (hsigmaProfile0) (hsigmaProfileEighth) (hgammaHalf) (hgammaB) (hrawP) (halpha)
  obtain ⟨hbridge, htraceO⟩ :=
    @upperAfterBandConsumption_momentBounds2 (d) (M) (m) (k) (R) (hR) (E) (sigma) (hsigma0)
      (hsigma) (hd) (hscale) (hgamma20) (hgammaHalf) (hP) (hP0) (hAP0) (hGAP) (hmean) (hF) (hA₀)
  rw [← show probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ) =
      fun omega => (d : ℝ) *
        probeSharpFramedCollarAfterBandCoordinateLane M m R (E : ℝ) j₀ omega by
    funext omega
    exact probeSharpFramedCollarAfterBandTraceLane_eq_dimension_mul
      M m R (E : ℝ) j₀ omega] at htraceO
  exact ⟨by simpa only [k₀, ell] using hbridge,
    by simpa only [A₀, F, rho, target, mul_assoc] using htraceO⟩
/-- Dimension-only prefactor after extracting the tuned collar cap. -/
noncomputable def collarAfterBandTunedTracePrefactor (d : ℕ) : ℝ :=
  (d : ℝ) * upperAfterBandRareTriangleConst *
    (probeMeanGoodWaveDimensionConst d * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (1 / 16 : ℝ)) *
      collarBandMeanTunedCapPrefactor d *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (54 * waveSharpUpperConst d ^ 2)) *
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) *
        ((3 : ℝ) ^ (-(1 / 40 : ℝ))) ^ n))
/-- Threshold paying the tuned decay and eighth-power reserve. -/
noncomputable def collarAfterBandTunedOutputConst (d : ℕ) : ℝ :=
  max (collarBandMeanDepthThreshold d)
    (1 + 2 * (collarAfterBandTunedTracePrefactor d + 8) *
      (collarBandMeanTunedDecayRate d)⁻¹)
private theorem cstarInv_mul_exp_neg_collarRate_le_halfRate
    {cstarInv rate E X : ℝ} (hrate : 0 < rate)
    (hE : 1 ≤ E) (hlarge : 2 * rate⁻¹ ≤ E)
    (hX : E ^ 3 ≤ X) (hcstarInvE : cstarInv ≤ E) :
    cstarInv * Real.exp (-(rate * X)) ≤
      Real.exp (-((rate / 2) * X)) := by
  exact cstarInv_mul_exp_neg_afterBandRate_le_halfRate
    hrate hE hlarge hX hcstarInvE

private theorem afterBandDepth_baseScale_le_reserve :
    ∀ {d : ℕ} (M : ABKModel d) {E : { E : ℝ // (1 : ℝ) ≤ E }}
      {sigma : ℝ},
      let X : ℝ := (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹;
      let rate : ℝ := collarBandMeanTunedDecayRate d;
      let K : ℝ := collarAfterBandTunedTracePrefactor d;
      let B : ℝ :=
        (↑d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
          (probeMeanGoodWaveConst M * ((5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ)) *
                ((4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                        probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) (collarBandMeanDepth M (↑E :
                          ℝ)) *
                      probeSharpCollarBandMeanMassQuarterConst d *
                    (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑(collarBandMeanDepth M (↑E : ℝ)) : ℝ)) *
                  (3 : ℝ) ^ (1 / 16 : ℝ)) *
              ((64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * ((54 : ℝ) * waveSharpUpperConst d ^
                (2 : ℕ))) *
            ∑' (n : ℕ), (↑(n + (1 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(1 / 40 : ℝ))) ^ n);
      (0 : ℝ) ≤ upperAfterBandRareTriangleConst →
        (0 : ℝ) ≤ probeMeanGoodWaveDimensionConst d →
          (0 : ℝ) ≤ (5 : ℝ) * (↑d : ℝ) ^ (2 : ℕ) →
            (0 : ℝ) ≤
                (4 : ℝ) * superposedGradConst d ^ (2 : ℕ) *
                  probeSharpCollarBandMeanMassQuarterConst d *
                  (3 : ℝ) ^ (1 / 16 : ℝ) →
              (0 : ℝ) ≤ (64 : ℝ) * superposedFluxHsepConst ^ (3 : ℝ) * ((54 : ℝ) *
                waveSharpUpperConst d ^ (2 : ℕ)) →
                (0 : ℝ) ≤ ∑' (n : ℕ), (↑(n + (1 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(1 / 40 : ℝ))) ^ n →
                  probeSharpCollarBandMeanCapQuarter M (↑E : ℝ) (collarBandMeanDepth M (↑E : ℝ)) *
                        (3 : ℝ) ^ ((2 : ℝ) * bfaProfileB * (↑(collarBandMeanDepth M (↑E : ℝ)) :
                          ℝ)) ≤
                      collarBandMeanTunedCapPrefactor d *
                        Real.exp (-(collarBandMeanTunedDecayRate d * ((↑E : ℝ)⁻¹ ^ (2 : ℕ) *
                          M.gamma⁻¹))) →
                    gammaTriangleConst (upperProfileTargetSigma sigma) ≤
                      upperAfterBandRareTriangleConst →
                      B ≤ K * (Disorder.cstar M)⁻¹ * Real.exp (-(rate * X)) := by
  intro d M E sigma X rate K B hTbar0 hmeanD0 hfive0 hfixed0 hrest0 hsum0 hcap hT
  dsimp only [B]
  rw [probeMeanGoodWaveConst_eq_dimension_mul_cstarInv M]
  let cinv : ℝ := (Algsuperdiff.Section3.Disorder.cstar M)⁻¹
  let capGrowth : ℝ :=
    probeSharpCollarBandMeanCapQuarter M (E : ℝ)
        (collarBandMeanDepth M (E : ℝ)) *
      (3 : ℝ) ^ (2 * bfaProfileB *
        (collarBandMeanDepth M (E : ℝ) : ℝ))
  let Z : ℝ := Real.exp (-(rate * X))
  have hcstar0 : 0 ≤ (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
    (inv_pos.mpr
      (Algsuperdiff.Section3.Disorder.cstar_characterization M).1).le
  have hcap0 : 0 ≤ capGrowth := by
    dsimp only [capGrowth]
    exact mul_nonneg
      (probeSharpCollarBandMeanCapQuarter_nonneg M (E : ℝ)
        (collarBandMeanDepth M (E : ℝ)))
      (Real.rpow_nonneg (by norm_num) _)
  have hZ0 : 0 ≤ Z := by dsimp only [Z]; positivity
  have hcap' : capGrowth ≤ collarBandMeanTunedCapPrefactor d * Z := by
    simpa only [capGrowth, Z, rate, X] using hcap
  let D : ℝ := probeMeanGoodWaveDimensionConst d * cinv * (5 * (d : ℝ) ^ 2) *
      (4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (1 / 16 : ℝ)) *
      (64 * superposedFluxHsepConst ^ (3 : ℝ) *
        (54 * waveSharpUpperConst d ^ 2)) *
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) *
        ((3 : ℝ) ^ (-(1 / 40 : ℝ))) ^ n)
  let C : ℝ := (d : ℝ) * upperAfterBandRareTriangleConst * D
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg hmeanD0 hcstar0) hfive0) hfixed0)
        hrest0)
      hsum0
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hTbar0) hD0
  have htriangle :
      (d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) * D ≤ C := by
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg d)) hD0
  calc
    _ = ((d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) * D) *
        capGrowth := by
      dsimp only [cinv, capGrowth, D]
      ring
    _ ≤ C * capGrowth := mul_le_mul_of_nonneg_right htriangle hcap0
    _ ≤ C * (collarBandMeanTunedCapPrefactor d * Z) :=
      mul_le_mul_of_nonneg_left hcap' hC0
    _ = K * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
        Real.exp (-(rate * X)) := by
      dsimp only [C, D, cinv, Z, K, collarAfterBandTunedTracePrefactor]
      ring

private theorem afterBandDepthScale_le_frozenReserve
    (M : ABKModel d) (k : ℕ) {E : {E : ℝ // 1 ≤ E}}
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hOutput : max (profileAuxiliaryConst d)
      (collarAfterBandTunedOutputConst d) ≤ Cup) :
    let eps := Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))
    let B := (d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
      ((probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
          (4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanCapQuarter M (E : ℝ)
              (collarBandMeanDepth M (E : ℝ)) *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (2 * bfaProfileB *
              (collarBandMeanDepth M (E : ℝ) : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ)) *
          (64 * superposedFluxHsepConst ^ (3 : ℝ) *
            (54 * waveSharpUpperConst d ^ 2))) *
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) *
          ((3 : ℝ) ^ (-(1 / 40 : ℝ))) ^ n))
    B * min 1 (M.gamma * ((k : ℝ) + 1)) ≤ eps ^ 8 := by
  dsimp only
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  let rate : ℝ := collarBandMeanTunedDecayRate d
  let K : ℝ := collarAfterBandTunedTracePrefactor d
  let B : ℝ :=
    (d : ℝ) * gammaTriangleConst (upperProfileTargetSigma sigma) *
      ((probeMeanGoodWaveConst M * (5 * (d : ℝ) ^ 2) *
          (4 * superposedGradConst d ^ 2 *
            probeSharpCollarBandMeanCapQuarter M (E : ℝ)
              (collarBandMeanDepth M (E : ℝ)) *
            probeSharpCollarBandMeanMassQuarterConst d *
            (3 : ℝ) ^ (2 * bfaProfileB *
              (collarBandMeanDepth M (E : ℝ) : ℝ)) *
            (3 : ℝ) ^ (1 / 16 : ℝ)) *
          (64 * superposedFluxHsepConst ^ (3 : ℝ) *
            (54 * waveSharpUpperConst d ^ 2))) *
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) *
          ((3 : ℝ) ^ (-(1 / 40 : ℝ))) ^ n))
  have hout : collarAfterBandTunedOutputConst d ≤ Cup :=
    (le_max_right _ _).trans hOutput
  have hrate : 0 < rate := by
    dsimp only [rate]
    exact collarBandMeanTunedDecayRate_pos d
  have hTbar0 : 0 ≤ upperAfterBandRareTriangleConst := by
    rw [upperAfterBandRareTriangleConst]
    positivity
  have hmeanD0 : 0 ≤ probeMeanGoodWaveDimensionConst d := by
    rw [probeMeanGoodWaveDimensionConst]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (simplexCrudeConst_nonneg d (s := (1 / 4 : ℝ)) (by norm_num)))
      (probeSimplexMeanSensitivityConst_nonneg hd)
  have hfive0 : 0 ≤ 5 * (d : ℝ) ^ 2 := by positivity
  have hfixed0 : 0 ≤ 4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (1 / 16 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
      (Real.rpow_nonneg (by norm_num) _)
  have hcapPref0 : 0 ≤ collarBandMeanTunedCapPrefactor d :=
    collarBandMeanTunedCapPrefactor_nonneg d
  have hrest0 : 0 ≤ 64 * superposedFluxHsepConst ^ (3 : ℝ) *
      (54 * waveSharpUpperConst d ^ 2) :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg superposedFluxHsepConst_pos.le _))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hsum0 : 0 ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) *
      ((3 : ℝ) ^ (-(1 / 40 : ℝ))) ^ n :=
    tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg (n + 1))
      (pow_nonneg (Real.rpow_nonneg (by norm_num) _) n)
  have hK0 : 0 ≤ K := by
    dsimp only [K, collarAfterBandTunedTracePrefactor]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d) hTbar0)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hmeanD0 hfive0) hfixed0) hcapPref0) hrest0)
        hsum0)
  have hthreshold : collarBandMeanDepthThreshold d ≤ Cup :=
    (le_max_left _ _).trans hout
  have hCup0 : 0 < Cup :=
    (collarBandMeanDepthThreshold_pos d).trans_le hthreshold
  have hchoiceRaw :
      1 + 2 * (K + 8) * rate⁻¹ ≤ Cup := by
    simpa only [collarAfterBandTunedOutputConst, K, rate] using
      (le_max_right _ _).trans hout
  have hlargeChoice : 2 * rate⁻¹ ≤ Cup := by
    have hinv : 0 < rate⁻¹ := inv_pos.mpr hrate
    linarith only [hchoiceRaw, hinv.le, mul_nonneg hK0 hinv.le]
  have hprefChoice : K + 8 ≤ (rate / 2) * Cup := by
    have hhalf : 0 ≤ rate / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hchoiceRaw hhalf
    have hcancel : (rate / 2) * (2 * (K + 8) * rate⁻¹) = K + 8 := by
      field_simp [ne_of_gt hrate]
    linarith only [hmul, hcancel, hhalf]
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hlarge : collarBandMeanDepthThreshold d ≤ X :=
    hthreshold.trans hX
  have hcap := probeSharpCollarBandMeanTunedCapGrowth_le_exp M
    (lt_of_lt_of_le zero_lt_one E.property) hlarge
  have hT : gammaTriangleConst (upperProfileTargetSigma sigma) ≤
      upperAfterBandRareTriangleConst :=
    gammaTriangleConst_upperProfileTarget_le hsigma0 hsigma
  have hbase := @afterBandDepth_baseScale_le_reserve (d) (M) (E) (sigma) (hTbar0) (hmeanD0)
    (hfive0) (hfixed0) (hrest0) (hsum0) (hcap) (hT)
  have hCupExp : Cup ≤ Real.exp (Cup / sigma) := by
    have hdiv : Cup ≤ Cup / sigma := by
      rw [le_div_iff₀ hsigma0]
      exact mul_le_of_le_one_right hCup0.le (by linarith only [hsigma])
    exact hdiv.trans ((le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp (Cup / sigma)))
  have hlargeE : 2 * rate⁻¹ ≤ (E : ℝ) :=
    hlargeChoice.trans (hCupExp.trans ((le_max_left _ _).trans hmax))
  have hXcube : (E : ℝ) ^ 3 ≤ X := by
    dsimp only [X]
    exact Algsuperdiff.Section3.Provider.Percolation.cube_le_invSq_mul_gammaInv
      M E.property hgamma
  have hcstarE : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    (le_max_right _ _).trans hmax
  have hcstarAbsorb :
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
          Real.exp (-(rate * X)) ≤
        Real.exp (-((rate / 2) * X)) :=
    cstarInv_mul_exp_neg_collarRate_le_halfRate
      hrate E.property hlargeE hXcube hcstarE
  have hreserve : K * Real.exp (-((rate / 2) * X)) ≤ eps ^ 8 := by
    dsimp only [eps]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hprefChoice
  have hbaseReserve : B ≤ eps ^ 8 :=
    hbase.trans (by simpa only [mul_assoc] using
      ((mul_le_mul_of_nonneg_left hcstarAbsorb hK0).trans hreserve))
  have hmin : min 1 (M.gamma * ((k : ℝ) + 1)) ≤ 1 := min_le_left _ _
  have hbase0 : 0 ≤ B := by
    dsimp only [B]
    have hwave0 : 0 ≤ probeMeanGoodWaveConst M :=
      probeMeanGoodWaveConst_nonneg hd M
    have hcapNow0 : 0 ≤ probeSharpCollarBandMeanCapQuarter M (E : ℝ)
        (collarBandMeanDepth M (E : ℝ)) :=
      probeSharpCollarBandMeanCapQuarter_nonneg M (E : ℝ)
        (collarBandMeanDepth M (E : ℝ))
    have hband0 : 0 ≤ 4 * superposedGradConst d ^ 2 *
        probeSharpCollarBandMeanCapQuarter M (E : ℝ)
          (collarBandMeanDepth M (E : ℝ)) *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (2 * bfaProfileB *
          (collarBandMeanDepth M (E : ℝ) : ℝ)) *
        (3 : ℝ) ^ (1 / 16 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) hcapNow0)
              (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
            (Real.rpow_nonneg (by norm_num) _))
          (Real.rpow_nonneg (by norm_num) _)
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d) gammaTriangleConst_pos.le)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hwave0 hfive0) hband0) hrest0)
        hsum0)
  have hscaleCore : B * min 1 (M.gamma * ((k : ℝ) + 1)) ≤ eps ^ 8 := by
    exact (mul_le_mul_of_nonneg_left hmin hbase0).trans (by
      simpa only [mul_one] using hbaseReserve)
  simpa only [B, eps, X] using hscaleCore
theorem collar_afterBand_trace_isBigOWith_frozenReserve
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hOutput : max (profileAuxiliaryConst d)
      (collarAfterBandTunedOutputConst d) ≤ Cup) :
    let eps := Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))
    (∀ omega, 0 ≤ probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ) omega) ∧
    Measurable (probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ)) ∧
    (∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure, ENNReal.ofReal
      (probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ) omega) =
      ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal (probeSharpFramedCollarWavePart M
        R.scale (E : ℝ) bfaProfileB (collarBandMeanDepth M (E : ℝ)) n (m - 1)
        (basisVec j) (superposedGradConst d) (fun eta => probeSharpAfterBandTerm M
          R.scale (probeSharpLayerAnchor R.scale bfaProfileB
            (collarBandMeanDepth M (E : ℝ)) n)
          (collarBandMeanDepth M (E : ℝ)) m eta ^ 2)
        (translateCutoffSample (triadicCubeShift R) omega))) ∧
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ))
      ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 8) := by
  dsimp only
  have hscale := afterBandDepthScale_le_frozenReserve
    M k hsigma0 hsigma hmax hEgamma hOutput
  dsimp only at hscale
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans hOutput
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hraw := collar_afterBand_trace_isBigOWith_depthProfile
    M hR hstate hsigma0 hsigma hmaxAux hEgamma
  rcases hraw with ⟨hbridge, hraw⟩
  refine ⟨probeSharpFramedCollarAfterBandTraceLane_nonneg M.shellPrefix.dimension M m R (E : ℝ),
    measurable_probeSharpFramedCollarAfterBandTraceLane M m R (E : ℝ),
    hbridge, hraw.mono_scale ?_⟩
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
  have hpow0 : 0 ≤ (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) :=
    Real.rpow_nonneg (by norm_num) _
  refine le_trans (le_of_eq ?_)
    ((mul_le_mul_of_nonneg_right hscale hpow0).trans_eq (mul_comm _ _))
  ring
end
end Algsuperdiff.Section3.Provider.CoarseEllipticity
