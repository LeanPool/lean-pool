/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanLayerProperties

/-!
# SharpFramedAfterBandScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Saturated after-band scale with the global frame retained

The ordinary after-band term is priced here at the exact
`streamIncrementLpNormScale M 4 (ell + k₀) L`.  In particular, its squared
scale retains the saturation factor
`min 1 (M.gamma * (L - (ell + k₀)))`; it is never relaxed to the linear
factor `M.gamma * (L - (ell + k₀))`.

The final identities specialize the observation-to-layer frame at a strict
descendant and expose the complete exponent after multiplication by the seam
factor.  These declarations are internal conditional obligations.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-- The exact `Gamma₂` scale of the rebased after-band term.  The cancellation
of the two `k₀` powers is built into the displayed gauge, while the stream
increment scale itself remains unchanged. -/
def probeSharpAfterBandExactScale (M : ABKModel d) (ell : ℤ)
    (k₀ : ℕ) (L : ℤ) : ℝ :=
  Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
    streamIncrementLpNormScale M 4 (ell + (k₀ : ℤ)) L

theorem probeSharpAfterBandExactScale_nonneg (M : ABKModel d) (ell : ℤ)
    (k₀ : ℕ) (L : ℤ) :
    0 ≤ probeSharpAfterBandExactScale M ell k₀ L := by
  have hmass : 0 ≤ streamIncrementLpMassScale M 4 (ell + (k₀ : ℤ)) L := by
    have hpoint : 0 ≤ streamPointScale M (ell + (k₀ : ℤ)) L := by
      rw [streamPointScale]
      exact mul_nonneg IndependentSums.gammaTriangleConst_pos.le
        (mul_nonneg (sq_nonneg (d : ℝ))
          (mul_nonneg
            (mul_nonneg geometricConcentrationConst_pos.le
              (le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
            (Real.rpow_nonneg (by norm_num) _)))
    rw [streamIncrementLpMassScale]
    exact mul_nonneg (Real.exp_pos 1).le
      (mul_nonneg
        (Real.rpow_nonneg
          (mul_nonneg
            (IndependentSums.gammaMomentConst_pos (by norm_num)).le hpoint) _)
        (Real.rpow_nonneg (by norm_num) _))
  have hnorm : 0 ≤ streamIncrementLpNormScale M 4 (ell + (k₀ : ℤ)) L := by
    rw [streamIncrementLpNormScale]
    exact Real.rpow_nonneg hmass _
  rw [probeSharpAfterBandExactScale]
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
    hnorm

/-- The after-band random variable is measurable at the exact scale. -/
theorem measurable_probeSharpAfterBandTerm_exactScale (M : ABKModel d)
    (m ell : ℤ) (k₀ : ℕ) (L : ℤ) :
    Measurable (probeSharpAfterBandTerm M m ell k₀ L) :=
  measurable_probeSharpAfterBandTerm M m ell k₀ L

/-- The exact after-band term has a `Gamma₂` bound without replacing the
stream increment scale by a square-root gap. -/
theorem isBigOWith_gammaSigma_probeSharpAfterBandTerm_exactScale
    (M : ABKModel d) {m ell L : ℤ} {k₀ : ℕ}
    (hL : ell + (k₀ : ℤ) < L) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (probeSharpAfterBandTerm M m ell k₀ L)
      (probeSharpAfterBandExactScale M ell k₀ L) := by
  have hbase := isBigOWith_cutoffSampleLaw_comp_val
    (isBigOWith_gammaSigma_streamIncrementLpNorm M
      (p := 4) (by norm_num) hL m)
  have hc : 0 ≤
      (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) *
        (Real.sqrt M.gamma *
          (3 : ℝ) ^ (-(M.gamma * (((ell + (k₀ : ℤ)) : ℤ) : ℝ)))) := by
    positivity
  have hscaled := hbase.const_mul hc
  have hpow :
      (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) *
          (3 : ℝ) ^ (-(M.gamma * (((ell + (k₀ : ℤ)) : ℤ) : ℝ))) =
        (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hc_eq :
      (3 : ℝ) ^ (M.gamma * (k₀ : ℝ)) *
          (Real.sqrt M.gamma *
            (3 : ℝ) ^ (-(M.gamma * (((ell + (k₀ : ℤ)) : ℤ) : ℝ)))) =
        Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) := by
    rw [← hpow]
    ring
  rw [hc_eq] at hscaled
  have hterm : probeSharpAfterBandTerm M m ell k₀ L =
      fun omega =>
        (Real.sqrt M.gamma * (3 : ℝ) ^ (-(M.gamma * (ell : ℝ)))) *
          streamIncrementLpNorm 4 m (ell + (k₀ : ℤ)) L omega.1 := by
    funext omega
    rw [probeSharpAfterBandTerm, waveSharpUpperTerm]
    rw [← hpow]
    ring
  rw [hterm]
  simpa only [probeSharpAfterBandExactScale] using hscaled

/-- Squaring the exact `Gamma₂` estimate gives the exact `Gamma₁` scale. -/
theorem isBigOWith_gammaSigma_one_probeSharpAfterBandTerm_sq_exactScale
    (M : ABKModel d) {m ell L : ℤ} {k₀ : ℕ}
    (hL : ell + (k₀ : ℤ) < L) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 1)
      (fun omega => probeSharpAfterBandTerm M m ell k₀ L omega ^ 2)
      (probeSharpAfterBandExactScale M ell k₀ L ^ 2) := by
  simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using
    (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg (σ := 2)
      (probeSharpAfterBandExactScale_nonneg M ell k₀ L)
      (fun omega => probeSharpAfterBandTerm_nonneg M m ell k₀ L omega)).1
        (isBigOWith_gammaSigma_probeSharpAfterBandTerm_exactScale M hL)

/-- At `p = 4`, the exact stream-norm scale is the point-scale carrier with
its `min` untouched. -/
theorem streamIncrementLpNormScale_four_eq_waveSharpUpperConst_min
    (M : ABKModel d) (n L : ℤ) :
    streamIncrementLpNormScale M 4 n L =
      waveSharpUpperConst d *
        min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((L : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (M.gamma * (L : ℝ)) := by
  have hbase : 0 ≤ IndependentSums.gammaMomentConst 2 *
      (IndependentSums.gammaTriangleConst 2 * ((d : ℝ) ^ 2 *
        (geometricConcentrationConst *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((L : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (L : ℝ))))) := by
    exact mul_nonneg
      (IndependentSums.gammaMomentConst_pos (by norm_num)).le
      (mul_nonneg IndependentSums.gammaTriangleConst_pos.le
        (mul_nonneg (sq_nonneg (d : ℝ))
          (mul_nonneg
            (mul_nonneg geometricConcentrationConst_pos.le
              (le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
            (Real.rpow_nonneg (by norm_num) _))))
  have hfour : 0 ≤ (4 : ℝ) ^ ((4 : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  rw [streamIncrementLpNormScale, streamIncrementLpMassScale,
    streamPointScale, waveSharpUpperConst]
  rw [Real.mul_rpow (Real.exp_pos 1).le
    (mul_nonneg (Real.rpow_nonneg hbase 4) hfour)]
  rw [Real.mul_rpow (Real.rpow_nonneg hbase 4) hfour]
  rw [← Real.rpow_mul hbase]
  norm_num
  ring

private theorem sqrt_mul_min_sqrt_inv_sq_eq_min_one_mul
    {gamma D : ℝ} (hgamma : 0 < gamma) (hD : 0 ≤ D) :
    (Real.sqrt gamma * min (Real.sqrt gamma⁻¹) (Real.sqrt D)) ^ 2 =
      min 1 (gamma * D) := by
  rcases le_total gamma⁻¹ D with hle | hle
  · have hsqrt : Real.sqrt gamma⁻¹ ≤ Real.sqrt D :=
      Real.sqrt_le_sqrt hle
    have hone : (1 : ℝ) ≤ gamma * D := by
      calc
        (1 : ℝ) = gamma * gamma⁻¹ := (mul_inv_cancel₀ hgamma.ne').symm
        _ ≤ gamma * D := mul_le_mul_of_nonneg_left hle hgamma.le
    have hcancel : Real.sqrt gamma * Real.sqrt gamma⁻¹ = 1 := by
      rw [← Real.sqrt_mul hgamma.le, mul_inv_cancel₀ hgamma.ne', Real.sqrt_one]
    rw [min_eq_left hsqrt, min_eq_left hone, hcancel, one_pow]
  · have hsqrt : Real.sqrt D ≤ Real.sqrt gamma⁻¹ :=
      Real.sqrt_le_sqrt hle
    have hone : gamma * D ≤ (1 : ℝ) := by
      calc
        gamma * D ≤ gamma * gamma⁻¹ :=
          mul_le_mul_of_nonneg_left hle hgamma.le
        _ = 1 := mul_inv_cancel₀ hgamma.ne'
    rw [min_eq_right hsqrt, min_eq_right hone, mul_pow,
      Real.sq_sqrt hgamma.le, Real.sq_sqrt hD]

/-- Exact normalization of the after-band scale: the short-gap saturation and
the global exponent are both visible. -/
theorem probeSharpAfterBandExactScale_eq_min
    (M : ABKModel d) {ell L : ℤ} {k₀ : ℕ} :
    probeSharpAfterBandExactScale M ell k₀ L =
      waveSharpUpperConst d * Real.sqrt M.gamma *
        min (Real.sqrt M.gamma⁻¹)
          (Real.sqrt ((L : ℝ) - (((ell + (k₀ : ℤ)) : ℤ) : ℝ))) *
        (3 : ℝ) ^ (M.gamma * ((L : ℝ) - (ell : ℝ))) := by
  rw [probeSharpAfterBandExactScale,
    streamIncrementLpNormScale_four_eq_waveSharpUpperConst_min]
  have hpow :
      (3 : ℝ) ^ (-(M.gamma * (ell : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (L : ℝ)) =
        (3 : ℝ) ^ (M.gamma * ((L : ℝ) - (ell : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [← hpow]
  ring

/-- The squared exact scale is exactly a dimension constant times the
saturated short-gap factor and the full global exponent. -/
theorem probeSharpAfterBandExactScale_sq_eq_min
    (M : ABKModel d) {ell L : ℤ} {k₀ : ℕ}
    (hL : ell + (k₀ : ℤ) < L) :
    probeSharpAfterBandExactScale M ell k₀ L ^ 2 =
      waveSharpUpperConst d ^ 2 *
        min 1 (M.gamma *
          ((L : ℝ) - (((ell + (k₀ : ℤ)) : ℤ) : ℝ))) *
        (3 : ℝ) ^ (2 * M.gamma * ((L : ℝ) - (ell : ℝ))) := by
  have hD : 0 ≤ (L : ℝ) - (((ell + (k₀ : ℤ)) : ℤ) : ℝ) := by
    have hcast : (((ell + (k₀ : ℤ)) : ℤ) : ℝ) < (L : ℝ) := by
      exact_mod_cast hL
    linarith
  have hmin := sqrt_mul_min_sqrt_inv_sq_eq_min_one_mul
    M.shellPrefix.gamma_pos hD
  have hpow :
      ((3 : ℝ) ^ (M.gamma * ((L : ℝ) - (ell : ℝ)))) ^ 2 =
        (3 : ℝ) ^ (2 * M.gamma * ((L : ℝ) - (ell : ℝ))) := by
    rw [← Real.rpow_natCast
      ((3 : ℝ) ^ (M.gamma * ((L : ℝ) - (ell : ℝ)))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [probeSharpAfterBandExactScale_eq_min M]
  calc
    (waveSharpUpperConst d * Real.sqrt M.gamma *
          min (Real.sqrt M.gamma⁻¹)
            (Real.sqrt ((L : ℝ) - (((ell + (k₀ : ℤ)) : ℤ) : ℝ))) *
          (3 : ℝ) ^ (M.gamma * ((L : ℝ) - (ell : ℝ)))) ^ 2 =
        waveSharpUpperConst d ^ 2 *
          (Real.sqrt M.gamma *
            min (Real.sqrt M.gamma⁻¹)
              (Real.sqrt ((L : ℝ) - (((ell + (k₀ : ℤ)) : ℤ) : ℝ)))) ^ 2 *
          ((3 : ℝ) ^ (M.gamma * ((L : ℝ) - (ell : ℝ)))) ^ 2 := by
      ring
    _ = _ := by rw [hmin, hpow]

/-- The random multiplier carried by the framed after-band square inside one
sharp Whitney layer. -/
def probeSharpFramedAfterBandMultiplier (M : ABKModel d) (root : ℤ)
    (E b : ℝ) (k₀ n : ℕ) (i : ℤ) (omega : CutoffSample d) : ℝ :=
  probeSharpLayerFrame M root E b k₀ n i omega *
    (3 : ℝ) ^ (2 * M.gamma * (hsep M root E b omega : ℝ))

theorem probeSharpFramedAfterBandMultiplier_nonneg
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ)
    (i : ℤ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedAfterBandMultiplier M root E b k₀ n i omega := by
  exact mul_nonneg
    (probeSharpLayerFrame_nonneg M root E b k₀ n i omega)
    (Real.rpow_nonneg (by norm_num) _)

theorem measurable_probeSharpFramedAfterBandMultiplier
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ) (i : ℤ) :
    Measurable (probeSharpFramedAfterBandMultiplier M root E b k₀ n i) := by
  have hframe := measurable_probeSharpLayerFrame M root E b k₀ n i
  have hhsep : Measurable fun omega : CutoffSample d =>
      (3 : ℝ) ^ (2 * M.gamma * (hsep M root E b omega : ℝ)) :=
    measurable_comp_hsep M root E b fun h : ℕ =>
      (3 : ℝ) ^ (2 * M.gamma * (h : ℝ))
  exact hframe.mul hhsep

/-- At a descendant observed from scale `m - 1`, the retained frame cancels
one of the two seam powers exactly. -/
theorem probeSharpFramedAfterBandMultiplier_descendant_eq
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E b : ℝ) (k₀ n : ℕ) (omega : CutoffSample d) :
    probeSharpFramedAfterBandMultiplier M R.scale E b k₀ n (m - 1) omega =
      (3 : ℝ) ^ (M.gamma *
        ((hsep M R.scale E b omega : ℝ) -
          ((k : ℝ) + (n : ℝ) +
            (⌈b * (1 - b)⁻¹ * (n : ℝ)⌉₊ : ℝ) + (k₀ : ℝ)))) := by
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  rw [probeSharpFramedAfterBandMultiplier, probeSharpLayerFrame,
    probeMeanLayerFrame, whitneyScale, whitneyScaleSeq,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  rw [hscale]
  push_cast
  ring


end

end Algsuperdiff.Section3.Provider.Multiscale
