/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SharpMeanSplitWave
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpMeanWaveBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionSeam1PerCube

/-!
# SharpLayerEnvelope

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
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

private theorem sq_five_sum_le_probe (a b c e f : ℝ) :
    (a + b + c + e + f) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e),
    sq_nonneg (a - f), sq_nonneg (b - c), sq_nonneg (b - e),
    sq_nonneg (b - f), sq_nonneg (c - e), sq_nonneg (c - f),
    sq_nonneg (e - f)]

theorem seamLayerObject_le_waveAmplitude_sq_root_probe
    (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (ell : ℤ) (h : ℕ) (L : ℤ) (omega : CutoffSample d) :
    seamLayerObject M m hn n ell h L omega ≤
      (Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
        streamIncrementLpNorm 4 m (ell - (h : ℤ)) L omega.1) ^ 2 := by
  have hlayer := sum_cubeMassRatio_mul_cubeAverage_le_streamIncrementLpMass
    (p := 4) (by norm_num) m (n + hn n)
    (S := whitneyLayer (d := d) m hn n)
    (fun _ hQ => mem_descendantsAtDepth_of_mem_whitneyLayer hQ)
    (ell - (h : ℤ)) L omega.1
  have hroot : Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn n,
      cubeMassRatio (originCube d m) Q *
        cubeAverage Q (streamIncrementLpDensity 4 (ell - (h : ℤ)) L omega.1)) ≤
      streamIncrementLpNorm 4 m (ell - (h : ℤ)) L omega.1 ^ 2 := by
    rw [← sqrt_streamIncrementLpMass_four_eq_streamIncrementLpNorm_sq]
    exact Real.sqrt_le_sqrt hlayer
  have hcoeff :
      M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) =
        (Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ)))) ^ 2 := by
    have hsqrt : Real.sqrt M.gamma ^ 2 = M.gamma :=
      Real.sq_sqrt M.shellPrefix.gamma_pos.le
    have hpow :
        ((3 : ℝ) ^ (-(M.gamma * (ell : ℝ)))) ^ 2 =
          (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) := by
      rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [mul_pow, hsqrt, hpow]
  have hc : 0 ≤ M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) :=
    mul_nonneg M.shellPrefix.gamma_pos.le (Real.rpow_nonneg (by norm_num) _)
  rw [seamLayerObject]
  calc
    M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) *
        Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn n,
          cubeMassRatio (originCube d m) Q *
            cubeAverage Q
              (streamIncrementLpDensity 4 (ell - (h : ℤ)) L omega.1)) ≤
      M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) *
        streamIncrementLpNorm 4 m (ell - (h : ℤ)) L omega.1 ^ 2 :=
      mul_le_mul_of_nonneg_left hroot hc
    _ = _ := by rw [hcoeff]; ring

theorem seamSimplexObject_le_waveAmplitude_sq_root_probe
    (M : ABKModel d) {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    (hstep : hn n ≤ hn (n + 1) + 1) (ell : ℤ) (h : ℕ) (L : ℤ)
    (omega : CutoffSample d) :
    seamSimplexObject M m hn n ell h L omega ≤
      (d : ℝ) ^ 2 *
        (Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
          streamIncrementLpNorm 4 m (ell - (h : ℤ)) L omega.1) ^ 2 := by
  exact (seamSimplexObject_le_mul_seamLayerObject M hstep ell h L omega).trans
    (mul_le_mul_of_nonneg_left
      (seamLayerObject_le_waveAmplitude_sq_root_probe M m hn n ell h L omega)
      (sq_nonneg (d : ℝ)))

theorem seamSimplexObject_le_five_sharp_terms_probe
    (M : ABKModel d) {m : ℤ} {E b : ℝ} {hn : ℕ → ℕ} {n : ℕ}
    (hstep : hn n ≤ hn (n + 1) + 1) {ell L : ℤ} {k₀ N g₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hN : k₀ < 3 ^ N)
    (hm : m = ell + (k₀ : ℤ) + (g₀ : ℤ))
    (htopL : ell + (k₀ : ℤ) ≤ L) (omega : CutoffSample d) :
    seamSimplexObject M m hn n ell (Percolation.hsep M m E b omega) L omega ≤
      5 * (d : ℝ) ^ 2 *
        (waveHeadTerm M m E b ell omega ^ 2 +
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2 +
          probeDeepBandGaugedTail M (originCube d m) ell k₀ N omega ^ 2 +
          probeSharpAfterBandTerm M m ell k₀ L omega ^ 2 +
          waveTailTerm M m E b m ell omega ^ 2) := by
  let A : ℝ := Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    streamIncrementLpNorm 4 m
      (ell - (Percolation.hsep M m E b omega : ℤ)) L omega.1
  let H : ℝ := waveHeadTerm M m E b ell omega
  let B : ℝ := waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀
  let T : ℝ := probeDeepBandGaugedTail M (originCube d m) ell k₀ N omega
  let U : ℝ := probeSharpAfterBandTerm M m ell k₀ L omega
  let V : ℝ := waveTailTerm M m E b m ell omega
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (streamIncrementLpNorm_nonneg 4 m _ L omega.1)
  have hH : 0 ≤ H := waveHeadTerm_nonneg M m E b ell omega
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact waveBandMean_nonneg (probeDeepBandMeanAmplitude_nonneg d) M.gamma k₀
  have hT : 0 ≤ T := probeDeepBandGaugedTail_nonneg M (originCube d m) ell k₀ N omega
  have hU : 0 ≤ U := probeSharpAfterBandTerm_nonneg M m ell k₀ L omega
  have hV : 0 ≤ V := waveTailTerm_nonneg M m E b m ell omega
  have hAmp : A ≤ H + B + T + U + V := by
    exact waveL4Amplitude_le_head_deepBand_sharpUpper_tail_probe
      M hk₀ hN hm htopL omega
  have hsum0 : 0 ≤ H + B + T + U + V := by positivity
  have hsq : A ^ 2 ≤ (H + B + T + U + V) ^ 2 :=
    (sq_le_sq₀ hA hsum0).2 hAmp
  have hfive := sq_five_sum_le_probe H B T U V
  have hroot := seamSimplexObject_le_waveAmplitude_sq_root_probe
    M (m := m) hstep ell (Percolation.hsep M m E b omega) L omega
  dsimp only [A, H, B, T, U, V] at hroot hsq hfive ⊢
  calc
    seamSimplexObject M m hn n ell (Percolation.hsep M m E b omega) L omega ≤
        (d : ℝ) ^ 2 * A ^ 2 := hroot
    _ ≤ (d : ℝ) ^ 2 * (H + B + T + U + V) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg (d : ℝ))
    _ ≤ (d : ℝ) ^ 2 *
        (5 * (H ^ 2 + B ^ 2 + T ^ 2 + U ^ 2 + V ^ 2)) :=
      mul_le_mul_of_nonneg_left hfive (sq_nonneg (d : ℝ))
    _ = _ := by ring

/-- The layer wave factor occurring in the mean decomposition, bounded by the
five-term split at the wave gauge used in the paper.  The factor `3^(2 * gamma
* hsep)` is retained explicitly: the layer's fourth-moment index is `ell -
hsep`, whereas this wave gauge is based at `ell`. -/
theorem probeLayerWaveFactor_actual_le_five_sharp_terms_probe
    (M : ABKModel d) {m : ℤ} {E b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 8)
    {k₀ : ℕ} (hk₀ : 2 ≤ k₀) {L : ℤ} (hmL : m ≤ L)
    (n : ℕ) (omega : CutoffSample d) :
    probeLayerWaveFactor M m
        (whitneyScale M m E b k₀ omega) n L omega ≤
      (3 : ℝ) ^ (2 * M.gamma *
          (Percolation.hsep M m E b omega : ℝ)) *
        (5 * (d : ℝ) ^ 2 *
          (waveHeadTerm M m E b (probeSharpLayerAnchor m b k₀ n) omega ^ 2 +
            waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2 +
            probeDeepBandGaugedTail M (originCube d m)
                (probeSharpLayerAnchor m b k₀ n) k₀ k₀ omega ^ 2 +
            probeSharpAfterBandTerm M m
                (probeSharpLayerAnchor m b k₀ n) k₀ L omega ^ 2 +
            waveTailTerm M m E b m
                (probeSharpLayerAnchor m b k₀ n) omega ^ 2)) := by
  let ell : ℤ := probeSharpLayerAnchor m b k₀ n
  have hstep : whitneyScale M m E b k₀ omega n ≤
      whitneyScale M m E b k₀ omega (n + 1) + 1 :=
    Algsuperdiff.Section3.Provider.Affine.step_of_monotone
      (whitneyScaleSeq_mono hb0.le (by linarith)
        (Percolation.hsep M m E b omega) k₀) n
  have hN : k₀ < 3 ^ k₀ := Nat.lt_pow_self (by norm_num)
  have hm : m = ell + (k₀ : ℤ) + (probeSharpLayerGap b n : ℤ) := by
    simpa only [ell] using probeSharpLayerAnchor_scale_eq m b k₀ n
  have htopL : ell + (k₀ : ℤ) ≤ L := by
    dsimp only [ell, probeSharpLayerAnchor]
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
    have hceil : (0 : ℤ) ≤
        (⌈b * (1 - b)⁻¹ * (n : ℝ)⌉₊ : ℤ) := Int.natCast_nonneg _
    omega
  have hseam := seamSimplexObject_le_five_sharp_terms_probe
    M (E := E) (b := b) hstep hk₀ hN hm htopL omega
  have hindex :
      m - (n : ℤ) - (whitneyScale M m E b k₀ omega n : ℤ) =
        ell - (Percolation.hsep M m E b omega : ℤ) := by
    dsimp only [ell, probeSharpLayerAnchor, whitneyScale, whitneyScaleSeq]
    omega
  have hindexReal :
      ((m - (n : ℤ) - (whitneyScale M m E b k₀ omega n : ℤ) : ℤ) : ℝ) =
        (ell : ℝ) - (Percolation.hsep M m E b omega : ℝ) := by
    exact_mod_cast hindex
  have hpow :
      (3 : ℝ) ^ (-(2 * M.gamma *
          ((m - (n : ℤ) - (whitneyScale M m E b k₀ omega n : ℤ) : ℤ) : ℝ))) =
        (3 : ℝ) ^ (2 * M.gamma *
            (Percolation.hsep M m E b omega : ℝ)) *
          (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) := by
    rw [hindexReal, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hfactor0 : 0 ≤ (3 : ℝ) ^ (2 * M.gamma *
      (Percolation.hsep M m E b omega : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [probeLayerWaveFactor, hpow, hindex]
  calc
    M.gamma *
          ((3 : ℝ) ^ (2 * M.gamma *
              (Percolation.hsep M m E b omega : ℝ)) *
            (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ)))) *
        Real.sqrt (layerSimplexFourthMass m
          (whitneyScale M m E b k₀ omega) n
          (ell - (Percolation.hsep M m E b omega : ℤ)) L omega) =
        (3 : ℝ) ^ (2 * M.gamma *
            (Percolation.hsep M m E b omega : ℝ)) *
          seamSimplexObject M m (whitneyScale M m E b k₀ omega) n ell
            (Percolation.hsep M m E b omega) L omega := by
      rw [seamSimplexObject]
      ring
    _ ≤ (3 : ℝ) ^ (2 * M.gamma *
            (Percolation.hsep M m E b omega : ℝ)) *
          (5 * (d : ℝ) ^ 2 *
            (waveHeadTerm M m E b ell omega ^ 2 +
              waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2 +
              probeDeepBandGaugedTail M (originCube d m) ell k₀ k₀ omega ^ 2 +
              probeSharpAfterBandTerm M m ell k₀ L omega ^ 2 +
              waveTailTerm M m E b m ell omega ^ 2)) :=
      mul_le_mul_of_nonneg_left hseam hfactor0
    _ = _ := rfl

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
