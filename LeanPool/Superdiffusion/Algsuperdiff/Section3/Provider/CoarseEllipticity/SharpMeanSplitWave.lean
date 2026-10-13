/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveSharpUpper
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DeepBandGroup

/-!
# SharpMeanSplitWave

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

theorem cubeStreamIncrementLpNorm_originCube_eq_probe {p : ℝ} (hp : 0 < p)
    (m n L : ℤ) (omega : ShellSeq d) :
    cubeStreamIncrementLpNorm p (originCube d m) n L omega =
      streamIncrementLpNorm p m n L omega := by
  rw [cubeStreamIncrementLpNorm, streamIncrementLpNorm,
    ← streamIncrementLpMass_eq_cubeAverage hp]

/-- The sharp ordinary wave term above the tuned deep band, rebased to the
lower edge of that band. -/
def probeSharpAfterBandTerm (M : ABKModel d) (m ell : ℤ) (k₀ : ℕ) (L : ℤ)
    (omega : CutoffSample d) : ℝ :=
  (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) *
    waveSharpUpperTerm M m (ell + (k₀ : ℤ)) L omega

theorem probeSharpAfterBandTerm_nonneg (M : ABKModel d) (m ell : ℤ)
    (k₀ : ℕ) (L : ℤ) (omega : CutoffSample d) :
    0 ≤ probeSharpAfterBandTerm M m ell k₀ L omega := by
  unfold probeSharpAfterBandTerm waveSharpUpperTerm
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (streamIncrementLpNorm_nonneg 4 m (ell + (k₀ : ℤ)) L omega.1))

theorem waveGauge_mul_upperNorm_eq_probe (M : ABKModel d) (m ell : ℤ)
    (k₀ : ℕ) (L : ℤ) (omega : CutoffSample d) :
    Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
        streamIncrementLpNorm 4 m (ell + (k₀ : ℤ)) L omega.1 =
      probeSharpAfterBandTerm M m ell k₀ L omega := by
  rw [probeSharpAfterBandTerm, waveSharpUpperTerm]
  have hpow :
      (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) *
          (3 : ℝ) ^ (-(M.gamma * (((ell + (k₀ : ℤ)) : ℤ) : ℝ))) =
        (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [← hpow]
  ring

/-- The exact root-cube deep-band split.  The carrier gap `g₀` is left
explicit so a Whitney layer can instantiate it with
`n + ⌈b(1-b)⁻¹n⌉₊`. -/
theorem streamIncrementLpNorm_deepBand_waveGauge_origin_probe
    (M : ABKModel d) (m ell : ℤ) {k₀ N g₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hN : k₀ < 3 ^ N)
    (hm : m = ell + (k₀ : ℤ) + (g₀ : ℤ)) :
    (∀ omega : CutoffSample d,
        Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
            streamIncrementLpNorm 4 m ell (ell + (k₀ : ℤ)) omega.1 ≤
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ +
            probeDeepBandGaugedTail M (originCube d m) ell k₀ N omega) ∧
      IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
        (IndependentSums.gammaSigma 2)
        (probeDeepBandGaugedTail M (originCube d m) ell k₀ N)
        (probeDeepBandGaugedFluct M ell k₀ g₀) ∧
      Measurable
        (probeDeepBandGaugedTail M (originCube d m) ell k₀ N) := by
  have hband := cubeStreamIncrementLpNorm_deepBand_waveGauge_probe
    M (originCube d m) ell hk₀ hN (by simpa using! hm)
  refine ⟨?_, hband.2⟩
  intro omega
  have h := hband.1 omega
  rw [cubeStreamIncrementLpNorm_originCube_eq_probe
    (d := d) (p := 4) (by norm_num) m ell (ell + (k₀ : ℤ)) omega.1] at h
  exact h

/-- The wave-gauged amplitude split at a root cube: random-depth head,
mean-split deep band, sharp macroscopic upper increment, and random-depth
tail.  No grid maximum or translated-cube penalty is introduced. -/
theorem waveL4Amplitude_le_head_deepBand_sharpUpper_tail_probe
    (M : ABKModel d) {m : ℤ} {E b : ℝ} {ell L : ℤ}
    {k₀ N g₀ : ℕ} (hk₀ : 2 ≤ k₀) (hN : k₀ < 3 ^ N)
    (hm : m = ell + (k₀ : ℤ) + (g₀ : ℤ))
    (htopL : ell + (k₀ : ℤ) ≤ L) (omega : CutoffSample d) :
    Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
        streamIncrementLpNorm 4 m
          (ell - (Percolation.hsep M m E b omega : ℤ)) L omega.1 ≤
      waveHeadTerm M m E b ell omega +
        waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ +
        probeDeepBandGaugedTail M (originCube d m) ell k₀ N omega +
        probeSharpAfterBandTerm M m ell k₀ L omega +
        waveTailTerm M m E b m ell omega := by
  let c : ℝ := Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ)))
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hstart : ell - (Percolation.hsep M m E b omega : ℤ) ≤ ell := by
    have h0 : (0 : ℤ) ≤ (Percolation.hsep M m E b omega : ℤ) :=
      Int.natCast_nonneg _
    omega
  have helltop : ell ≤ ell + (k₀ : ℤ) := by omega
  have hfirst := streamIncrementLpNorm_add_le (d := d) (p := 4) (by norm_num)
    m hstart (helltop.trans htopL) omega.1
  have hsecond := streamIncrementLpNorm_add_le (d := d) (p := 4) (by norm_num)
    m helltop htopL omega.1
  have hlower := streamIncrementLpNorm_le_waveL4Head_add_waveL4Tail M m ell
    (Percolation.hsep M m E b omega) omega
  have hsumle := waveL4Tail_le_range_sum M m ell
    (Percolation.hsep M m E b omega) omega
  have htotal :
      streamIncrementLpNorm 4 m
          (ell - (Percolation.hsep M m E b omega : ℤ)) L omega.1 ≤
        waveL4Head M ell (Percolation.hsep M m E b omega) +
          streamIncrementLpNorm 4 m ell (ell + (k₀ : ℤ)) omega.1 +
          streamIncrementLpNorm 4 m (ell + (k₀ : ℤ)) L omega.1 +
          ∑ i ∈ Finset.range (Percolation.hsep M m E b omega),
            waveL4Tail M m ell (i + 1) omega := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left htotal hc
  have hband :=
    (streamIncrementLpNorm_deepBand_waveGauge_origin_probe M m ell hk₀ hN hm).1 omega
  have hupper := waveGauge_mul_upperNorm_eq_probe M m ell k₀ L omega
  dsimp only [c] at hscaled
  simp only [mul_add] at hscaled
  rw [waveHeadTerm, waveTailTerm] at ⊢
  rw [hupper] at hscaled
  linarith

/-- The lower anchor scale for a sharp layer with its prescribed separation gap. -/
def probeSharpLayerAnchor (m : ℤ) (b : ℝ) (k₀ n : ℕ) : ℤ :=
  m - (n : ℤ) - (⌈b * (1 - b)⁻¹ * (n : ℝ)⌉₊ : ℤ) - (k₀ : ℤ)

/-- The natural-number separation gap assigned to a sharp layer. -/
def probeSharpLayerGap (b : ℝ) (n : ℕ) : ℕ :=
  n + ⌈b * (1 - b)⁻¹ * (n : ℝ)⌉₊

theorem probeSharpLayerAnchor_scale_eq (m : ℤ) (b : ℝ) (k₀ n : ℕ) :
    m = probeSharpLayerAnchor m b k₀ n + (k₀ : ℤ) +
      (probeSharpLayerGap b n : ℤ) := by
  unfold probeSharpLayerAnchor probeSharpLayerGap
  push_cast
  ring


theorem measurable_probeSharpAfterBandTerm (M : ABKModel d) (m ell : ℤ)
    (k₀ : ℕ) (L : ℤ) : Measurable (probeSharpAfterBandTerm M m ell k₀ L) := by
  unfold probeSharpAfterBandTerm waveSharpUpperTerm
  have hnorm : Measurable (streamIncrementLpNorm (d := d) 4 m (ell + (k₀ : ℤ)) L) :=
    (measurable_streamIncrementLpMass (d := d) (p := 4) (by norm_num)
      m (ell + (k₀ : ℤ)) L).pow_const _
  exact measurable_const.mul (measurable_const.mul (hnorm.comp measurable_subtype_coe))


theorem isBigOWith_gammaSigma_one_probeDeepBandGaugedTail_origin_sq
    (M : ABKModel d) (m ell : ℤ) {k₀ g₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hm : m = ell + (k₀ : ℤ) + (g₀ : ℤ)) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega => probeDeepBandGaugedTail M (originCube d m) ell k₀ k₀ omega ^ 2)
      (probeDeepBandGaugedFluct M ell k₀ g₀ ^ 2) := by
  have hN : k₀ < 3 ^ k₀ := Nat.lt_pow_self (by norm_num)
  have hbase :=
    (streamIncrementLpNorm_deepBand_waveGauge_origin_probe M m ell hk₀ hN hm).2.1
  have htail0 : ∀ omega : CutoffSample d,
      0 ≤ probeDeepBandGaugedTail M (originCube d m) ell k₀ k₀ omega := by
    intro omega
    unfold probeDeepBandGaugedTail
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (probeDeepBandTail_nonneg M (originCube d m) (ell + (k₀ : ℤ)) k₀ k₀ omega)
  have hscale0 : 0 ≤ probeDeepBandGaugedFluct M ell k₀ g₀ := by
    have hraw : 0 ≤ probeDeepBandRawFluct d M.gamma (ell + (k₀ : ℤ)) g₀ := by
      unfold probeDeepBandRawFluct
      exact mul_nonneg IndependentSums.gammaTriangleConst_pos.le
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (probeDeepBandGainRootConst_nonneg d) (by norm_num))
            (mul_nonneg (pow_nonneg (probeBandUnitGain_nonneg d) _)
              (Real.sqrt_nonneg 2)))
          (Real.rpow_nonneg (by norm_num) _))
    unfold probeDeepBandGaugedFluct
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)) hraw
  simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using
    (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg (σ := 2) hscale0 htail0).1 hbase

theorem waveTailGainScale_nonneg_probe (d : ℕ) (b sigma sigma2 : ℝ)
    (lout ell : ℤ) :
    0 ≤ waveTailGainScale d b sigma sigma2 lout ell := by
  have hK : 0 < Percolation.hsepAmplitude sigma b := by
    rw [Percolation.hsepAmplitude]
    positivity
  have hseries : 0 ≤
      ∑' i : ℕ, truncationIndicatorScale b sigma sigma2
        (Percolation.hsepAmplitude sigma b) i :=
    tsum_nonneg fun i => (truncationIndicatorScale_pos hK i).le
  have hgain : 0 ≤
      streamIncrementLpGainConst d (2 / 4) ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_nonneg (streamIncrementLpGainConst_pos d _).le _
  have hhead : 0 ≤ waveL4HeadConst d := waveL4HeadConst_nonneg d
  have htriangle : 0 ≤
      IndependentSums.gammaTriangleConst (2 * sigma2 / (2 + sigma2)) :=
    IndependentSums.gammaTriangleConst_pos.le
  have hproduct : 0 ≤ HCPolySupport.Book.Ch04.gammaProductConst 2 sigma2 :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hpow : 0 ≤
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((lout : ℝ) - (ell : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  rw [waveTailGainScale]
  positivity

/-- The active squared wave-tail leg derived from the raw bad-event gates. -/
theorem isBigOWith_gammaSigma_probeWaveTailTerm_sq_of_gates
    (M : ABKModel d) {m : ℤ} {E sigma sigma2 b : ℝ}
    (hd2 : 2 ≤ d) (hE : 1 ≤ E)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) ⟨E, hE⟩)
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hsigma2 : 0 < sigma2) (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    (hEexp : Real.exp (Percolation.badClustersConst d / sigma) ≤ E)
    (hE4 : 4 ≤ E) (hunit : BadEvents.unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : E⁻¹ ^ 2 ≤ Algsuperdiff.Section3.Disorder.cstar M)
    (hEb : Percolation.badClustersConst d / b ≤ E)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) (lout ell : ℤ) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma (sigma2 / (2 + sigma2)))
      (fun omega => waveTailTerm M m E b lout ell omega ^ 2)
      (waveTailGainScale d b sigma sigma2 lout ell ^ 2) := by
  have hleg :=
    (isBigOWith_gammaSigma_waveTailTerm_of_gates M hd2 hE hS hsigma0 hsigma
      hsigma2 hb0 hb1 hEexp hE4 hunit hgamma20 hinvSq hEb hgammaE lout ell).mono_scale
      (waveTailScale_le_waveTailGainScale M hb0 hsigma2 (by linarith) lout ell)
  have hsquared :=
    (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
      (σ := 2 * sigma2 / (2 + sigma2))
      (waveTailGainScale_nonneg_probe d b sigma sigma2 lout ell)
      (fun omega => waveTailTerm_nonneg M m E b lout ell omega)).1 hleg
  rwa [show 2 * sigma2 / (2 + sigma2) / 2 = sigma2 / (2 + sigma2) by ring]
    at hsquared

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
