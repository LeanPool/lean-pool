/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.WhitneyWeightGeometric

/-!
# SharpFramedAfterBandLayerProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Whitney-layer profile for the saturated after-band term

This file prices the deterministic `2` summand supplied by the pointwise `hsep`
reduction for the after-band square.  The carrier below includes the actual
sharp five-term coefficient, the good-layer mass envelope, the exact short-gap
saturation, and the tuned band depth.  The complementary random Orlicz summand
is deliberately not included here.  This is the normalized inner good-mass
branch before multiplication by `probeMeanGoodWaveConst M * vecNormSq p`;
consequently it is not the complete Whitney-layer mean contribution.  It omits
every other lane.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-! ## Scalar layer arithmetic -/

/-- The ceiling appearing in the fixed-slope Whitney layer. -/
def bfaAfterBandLayerCeil (n : ℕ) : ℕ :=
  ⌈bfaProfileB * (1 - bfaProfileB)⁻¹ * (n : ℝ)⌉₊

/-- At the fixed profile slope, the additional ceiling is at most the layer
index itself. -/
theorem bfaAfterBandLayerCeil_le (n : ℕ) :
    bfaAfterBandLayerCeil n ≤ n := by
  have hslope : bfaProfileB * (1 - bfaProfileB)⁻¹ ≤ 1 :=
    whitneyScaleSeq_slope_le_one bfaProfileB_pos bfaProfileB_le_one_eighth
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [bfaAfterBandLayerCeil]
  refine Nat.ceil_le.2 ?_
  calc
    bfaProfileB * (1 - bfaProfileB)⁻¹ * (n : ℝ) ≤ 1 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hslope hn
    _ = (n : ℝ) := one_mul _

/-- Scaling the argument of `min 1` by a factor at least one costs at most
that factor outside the minimum. -/
theorem min_one_mul_le_mul_min_one {a x : ℝ}
    (ha : 1 ≤ a) :
    min 1 (a * x) ≤ a * min 1 x := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    exact min_le_right _ _
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    rw [min_eq_left h1x]
    simpa using (min_le_left 1 (a * x)).trans ha

/-- The saturated gap at layer `n` costs only a linear `(n+1)` factor relative
to the target depth profile. -/
theorem bfaAfterBandSaturation_le
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (k n : ℕ) :
    min 1 (gamma *
        (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) ≤
      (2 * ((n + 1 : ℕ) : ℝ)) *
        min 1 (gamma * ((k + 1 : ℕ) : ℝ)) := by
  have hceilNat := bfaAfterBandLayerCeil_le n
  have hceil : (bfaAfterBandLayerCeil n : ℝ) ≤ n := by
    exact_mod_cast hceilNat
  have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfactor : (1 : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hgap :
      1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) ≤
        (2 * ((n + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have harg :
      gamma *
          (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)) ≤
        (2 * ((n + 1 : ℕ) : ℝ)) *
          (gamma * ((k + 1 : ℕ) : ℝ)) := by
    calc
      gamma *
          (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)) ≤
          gamma * ((2 * ((n + 1 : ℕ) : ℝ)) *
            ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hgap hgamma
      _ = (2 * ((n + 1 : ℕ) : ℝ)) *
          (gamma * ((k + 1 : ℕ) : ℝ)) := by ring
  exact (min_le_min_left 1 harg).trans
    (min_one_mul_le_mul_min_one hfactor)

/-- The tuned band depth costs at most `21/20` in its `gamma`-weighted
exponent when `E ≥ 1` and `gamma ≤ 1/20`. -/
theorem gamma_mul_waveBandDepth_one_le
    {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hgamma20 : gamma ≤ 1 / 20) :
    gamma * (waveBandDepth 1 E gamma : ℝ) ≤ 21 / 20 := by
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hE2 : 1 ≤ E ^ 2 := by nlinarith
  have hE2pos : 0 < E ^ 2 := sq_pos_of_pos hEpos
  have hinv : (E ^ 2)⁻¹ ≤ 1 := (inv_le_one₀ hE2pos).2 hE2
  have ht : 0 ≤ (1 : ℝ) * (E ^ 2)⁻¹ * gamma⁻¹ := by positivity
  have hdepth := waveBandDepth_spec (c := (1 : ℝ)) (E := E)
    (gamma := gamma) hgamma ht
  norm_num at hdepth ⊢
  linarith

/-- Exact square-root form of the good Whitney-layer mass envelope. -/
theorem sqrt_probeSharpLayerMassEnvelope_eq (d n : ℕ) :
    Real.sqrt (probeSharpLayerMassEnvelope d n) =
      Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (-(n : ℝ) / 2) := by
  rw [probeSharpLayerMassEnvelope,
    Real.sqrt_mul (mul_nonneg (by norm_num) (Nat.cast_nonneg d))]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- The good-mass square root absorbs all layer growth and the tuned band
depth, leaving the fixed geometric ratio. -/
theorem sqrt_mass_mul_afterBandGrowth_le
    {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hgamma20 : gamma ≤ 1 / 20) (d n : ℕ) :
    Real.sqrt (probeSharpLayerMassEnvelope d n) *
        (3 : ℝ) ^ (gamma *
          (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
            (waveBandDepth 1 E gamma : ℝ))) ≤
      Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (11 / 10 : ℝ) *
        whitneyDecayRatio ^ n := by
  have hceilNat := bfaAfterBandLayerCeil_le n
  have hceil : (bfaAfterBandLayerCeil n : ℝ) ≤ n := by
    exact_mod_cast hceilNat
  have hdepth := gamma_mul_waveBandDepth_one_le hE hgamma hgamma20
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp :
      -(n : ℝ) / 2 + gamma *
          (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
            (waveBandDepth 1 E gamma : ℝ)) ≤
        (11 / 10 : ℝ) + (-(1 / 8 : ℝ)) * (n : ℝ) := by
    have hgrowth : gamma *
          ((n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)) ≤
        (1 / 10 : ℝ) * (n : ℝ) := by
      calc
        gamma * ((n : ℝ) + (bfaAfterBandLayerCeil n : ℝ)) ≤
            gamma * (2 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hgamma.le
        _ ≤ (1 / 20 : ℝ) * (2 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hgamma20 (by positivity)
        _ = (1 / 10 : ℝ) * (n : ℝ) := by ring
    linarith
  have hthree : (0 : ℝ) < 3 := by norm_num
  rw [sqrt_probeSharpLayerMassEnvelope_eq]
  have hlhs :
      (3 : ℝ) ^ (-(n : ℝ) / 2) *
          (3 : ℝ) ^ (gamma *
            (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
              (waveBandDepth 1 E gamma : ℝ))) =
        (3 : ℝ) ^ (-(n : ℝ) / 2 + gamma *
          (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
            (waveBandDepth 1 E gamma : ℝ))) := by
    rw [← Real.rpow_add hthree]
  have hrhs :
      (3 : ℝ) ^ (11 / 10 : ℝ) * whitneyDecayRatio ^ n =
        (3 : ℝ) ^ ((11 / 10 : ℝ) +
          (-(1 / 8 : ℝ)) * (n : ℝ)) := by
    rw [whitneyDecayRatio, ← Real.rpow_natCast,
      ← Real.rpow_mul hthree.le, ← Real.rpow_add hthree]
  calc
    Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (-(n : ℝ) / 2) *
          (3 : ℝ) ^ (gamma *
            (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
              (waveBandDepth 1 E gamma : ℝ))) =
        Real.sqrt (6 * (d : ℝ)) *
          ((3 : ℝ) ^ (-(n : ℝ) / 2) *
            (3 : ℝ) ^ (gamma *
              (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
                (waveBandDepth 1 E gamma : ℝ)))) := by ring
    _ = Real.sqrt (6 * (d : ℝ)) *
          (3 : ℝ) ^ (-(n : ℝ) / 2 + gamma *
            (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
              (waveBandDepth 1 E gamma : ℝ))) := by rw [hlhs]
    _ ≤ Real.sqrt (6 * (d : ℝ)) *
          (3 : ℝ) ^ ((11 / 10 : ℝ) +
            (-(1 / 8 : ℝ)) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
        (Real.sqrt_nonneg _)
    _ = Real.sqrt (6 * (d : ℝ)) *
          ((3 : ℝ) ^ (11 / 10 : ℝ) * whitneyDecayRatio ^ n) := by
      rw [hrhs]
    _ = Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (11 / 10 : ℝ) *
          whitneyDecayRatio ^ n := by ring

/-! ## The concrete deterministic branch -/

/-- The literal deterministic `2` branch of the framed after-band square after
multiplication by the sharp five-term coefficient and the good-layer mass
square root.  It is the normalized inner branch before multiplication by
`probeMeanGoodWaveConst M * vecNormSq p`, not the complete layer. -/
def probeSharpAfterBandOrdinaryGoodMassLayer
    (M : ABKModel d) (E : ℝ) (k n : ℕ) : ℝ :=
  10 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
    Real.sqrt (probeSharpLayerMassEnvelope d n) *
    min 1 (M.gamma *
      (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) *
    (3 : ℝ) ^ (M.gamma *
      (2 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
        (waveBandDepth 1 E M.gamma : ℝ)))

/-- Dimension-only coefficient in the pointwise Whitney-layer profile. -/
def probeSharpAfterBandOrdinaryLayerConst (d : ℕ) : ℝ :=
  20 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
    Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (11 / 10 : ℝ)

/-- Dimension-only coefficient after summing the normalized inner branch over
all Whitney layers. -/
def probeSharpAfterBandOrdinarySumConst (d : ℕ) : ℝ :=
  probeSharpAfterBandOrdinaryLayerConst d /
    (1 - whitneyDecayRatio) ^ 2

theorem probeSharpAfterBandOrdinaryGoodMassLayer_nonneg
    (M : ABKModel d) (E : ℝ) (k n : ℕ) :
    0 ≤ probeSharpAfterBandOrdinaryGoodMassLayer M E k n := by
  rw [probeSharpAfterBandOrdinaryGoodMassLayer]
  have hgap : 0 ≤
      1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) := by
    positivity
  have hmin : 0 ≤ min 1 (M.gamma *
      (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) :=
    le_min zero_le_one (mul_nonneg M.shellPrefix.gamma_pos.le hgap)
  positivity

theorem probeSharpAfterBandOrdinaryLayerConst_nonneg (d : ℕ) :
    0 ≤ probeSharpAfterBandOrdinaryLayerConst d := by
  rw [probeSharpAfterBandOrdinaryLayerConst]
  positivity

/-- One deterministic after-band layer has the target saturated depth profile
times the fixed summable Whitney weight. -/
theorem probeSharpAfterBandOrdinaryGoodMassLayer_le
    (M : ABKModel d) {E : ℝ} (hE : 1 ≤ E)
    (hgamma20 : M.gamma ≤ 1 / 20) (k n : ℕ) :
    probeSharpAfterBandOrdinaryGoodMassLayer M E k n ≤
      probeSharpAfterBandOrdinaryLayerConst d *
        (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) *
        (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsat := bfaAfterBandSaturation_le hgamma.le k n
  have hgrowth := sqrt_mass_mul_afterBandGrowth_le
    hE hgamma hgamma20 d n
  have hA : 0 ≤
      10 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 := by positivity
  have hgap : 0 ≤
      1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) := by
    positivity
  have hsat0 : 0 ≤ min 1 (M.gamma *
      (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) :=
    le_min zero_le_one (mul_nonneg hgamma.le hgap)
  have htarget0 : 0 ≤ min 1
      (M.gamma * ((k + 1 : ℕ) : ℝ)) := by
    exact le_min zero_le_one
      (mul_nonneg hgamma.le (Nat.cast_nonneg (k + 1)))
  have hprofilePower0 : 0 ≤
      (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hgrowthRhs0 : 0 ≤
      Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (11 / 10 : ℝ) *
        whitneyDecayRatio ^ n := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
      (pow_nonneg whitneyDecayRatio_nonneg n)
  have hpow :
      (3 : ℝ) ^ (M.gamma *
          (2 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
            (waveBandDepth 1 E M.gamma : ℝ))) =
        (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma *
            (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
              (waveBandDepth 1 E M.gamma : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [probeSharpAfterBandOrdinaryGoodMassLayer, hpow]
  calc
    10 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
          Real.sqrt (probeSharpLayerMassEnvelope d n) *
          min 1 (M.gamma *
            (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) *
          ((3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ)) *
            (3 : ℝ) ^ (M.gamma *
              (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
                (waveBandDepth 1 E M.gamma : ℝ)))) =
        (10 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
            min 1 (M.gamma *
              (1 + (k : ℝ) + (n : ℝ) +
                (bfaAfterBandLayerCeil n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) *
          (Real.sqrt (probeSharpLayerMassEnvelope d n) *
            (3 : ℝ) ^ (M.gamma *
              (1 + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
                (waveBandDepth 1 E M.gamma : ℝ)))) := by ring
    _ ≤ (10 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
            min 1 (M.gamma *
              (1 + (k : ℝ) + (n : ℝ) +
                (bfaAfterBandLayerCeil n : ℝ))) *
            (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) *
          (Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (11 / 10 : ℝ) *
            whitneyDecayRatio ^ n) := by
      exact mul_le_mul_of_nonneg_left hgrowth
        (mul_nonneg (mul_nonneg hA hsat0) hprofilePower0)
    _ ≤ (10 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
            ((2 * ((n + 1 : ℕ) : ℝ)) *
              min 1 (M.gamma * ((k + 1 : ℕ) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) *
          (Real.sqrt (6 * (d : ℝ)) * (3 : ℝ) ^ (11 / 10 : ℝ) *
            whitneyDecayRatio ^ n) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsat hA) hprofilePower0)
        hgrowthRhs0
    _ = probeSharpAfterBandOrdinaryLayerConst d *
          (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) *
          (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
            (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) := by
      rw [probeSharpAfterBandOrdinaryLayerConst]
      ring

/-- The sum of the normalized deterministic inner branches retains the exact
saturated depth profile.  The outer mean coefficient and vector norm are not
part of either side. -/
theorem tsum_probeSharpAfterBandOrdinaryGoodMassLayer_le
    (M : ABKModel d) {E : ℝ} (hE : 1 ≤ E)
    (hgamma20 : M.gamma ≤ 1 / 20) (k : ℕ) :
    ∑' n : ℕ, probeSharpAfterBandOrdinaryGoodMassLayer M E k n ≤
      probeSharpAfterBandOrdinarySumConst d *
        (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
          (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) := by
  let target : ℝ := min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
    (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))
  let C : ℝ := probeSharpAfterBandOrdinaryLayerConst d
  have hterm : ∀ n : ℕ,
      probeSharpAfterBandOrdinaryGoodMassLayer M E k n ≤
        C * (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) * target := by
    intro n
    exact probeSharpAfterBandOrdinaryGoodMassLayer_le M hE hgamma20 k n
  have hright : Summable (fun n : ℕ =>
      C * (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) * target) :=
    (summable_succ_mul_whitneyDecayRatio.mul_left C).mul_right target
  have hleft : Summable (fun n : ℕ =>
      probeSharpAfterBandOrdinaryGoodMassLayer M E k n) :=
    Summable.of_nonneg_of_le
      (fun n => probeSharpAfterBandOrdinaryGoodMassLayer_nonneg M E k n)
      hterm hright
  calc
    ∑' n : ℕ, probeSharpAfterBandOrdinaryGoodMassLayer M E k n ≤
        ∑' n : ℕ,
          C * (((n + 1 : ℕ) : ℝ) * whitneyDecayRatio ^ n) * target :=
      Summable.tsum_le_tsum hterm hleft hright
    _ = C * (1 / (1 - whitneyDecayRatio) ^ 2) * target := by
      rw [tsum_mul_right, tsum_mul_left,
        hasSum_succ_mul_whitneyDecayRatio.tsum_eq]
    _ = probeSharpAfterBandOrdinarySumConst d *
          (min 1 (M.gamma * ((k + 1 : ℕ) : ℝ)) *
            (3 : ℝ) ^ (M.gamma * ((k + 1 : ℕ) : ℝ))) := by
      rw [probeSharpAfterBandOrdinarySumConst]
      dsimp only [C, target]
      ring

end

end Algsuperdiff.Section3.Provider.Multiscale
