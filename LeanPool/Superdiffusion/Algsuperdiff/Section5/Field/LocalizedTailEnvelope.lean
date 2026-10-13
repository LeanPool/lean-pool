/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.LocalizedTailProfile

/-!
# LocalizedTailEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Spatial envelopes for the localized stream-field tail constants

The local field bounds are logarithmic in the Euclidean observation radius.
This file converts them to the ambient `Vec d` norm and combines them with the
polynomial freezing radius.  The resulting amplitude has polynomial growth,
while the decay rate loses one logarithmic weight.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open DivergenceFormProcess.Decay
open HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- A dimension factor comparing the Euclidean and ambient norms. -/
def streamTailDimensionFactor (d : ℕ) : ℝ := 1 + d

/-- The effective upper constant before the spatial logarithmic weight. -/
def streamTailRawUpperConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ :=
  Real.sqrt 2 * (M.nu + streamFieldSmallBallConst M omega +
    2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega) *
      Real.sqrt M.nu)

/-- The effective upper constant enlarged by the norm-comparison logarithm. -/
def streamTailUpperConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ :=
  streamTailRawUpperConst M omega * streamLogWeight (streamTailDimensionFactor d)

/-- The spatially uniform part of the polynomial freezing-radius lower bound. -/
def streamTailFloorConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ :=
  min
    (Real.rpow (streamFreezingAmplitude M omega M.nu (streamLocalizedTailDelta d))
        (streamFreezingExponent M) *
      Real.rpow (streamTailDimensionFactor d) (-streamFreezingExponent M))
    (1 / 2 : ℝ)

/-- The coefficient multiplying the effective upper constant in the two
non-forcing terms of the tail amplitude. -/
def streamTailLinearConst (M : ABKModel d) : ℝ  :=
  agmonTailL2Coefficient d M.nu 1 +
    agmonTailGradientCoefficient d M.nu 1 (1 / 2 : ℝ)

/-- The polynomial exponent contributed by one logarithmic field factor and
the `d`-dimensional inverse freezing volume. -/
def streamTailAmplitudeExponent (M : ABKModel d) : ℝ :=
  1 + (d : ℝ) * streamFreezingExponent M

/-- A point-independent polynomial envelope constant for the tail amplitude. -/
def streamTailAmplitudeConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ  :=
  streamTailLinearConst M * streamTailUpperConst M omega /
      streamTailFloorConst M omega ^ d +
    4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / M.nu

/-- A point-independent numerator for the logarithmic lower envelope on the
decay rate. -/
def streamTailDecayConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ :=
  agmonTailRate d M.nu (streamTailUpperConst M omega) (1 / 2 : ℝ)

private theorem one_le_streamTailDimensionFactor (d : ℕ) :
    1 ≤ streamTailDimensionFactor d := by
  unfold streamTailDimensionFactor
  exact le_add_of_nonneg_right (Nat.cast_nonneg d)

private theorem streamTailDimensionFactor_pos (d : ℕ) :
    0 < streamTailDimensionFactor d :=
  lt_of_lt_of_le zero_lt_one (one_le_streamTailDimensionFactor d)

private theorem streamTailUpperConst_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) : 0 < streamTailUpperConst M omega := by
  unfold streamTailUpperConst streamTailRawUpperConst
  have hCg : 0 ≤ Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (streamFieldLargeGradientConst_nonneg M omega)
  have hrest : 0 ≤ streamFieldSmallBallConst M omega +
      2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega) *
        Real.sqrt M.nu :=
    add_nonneg (streamFieldSmallBallConst_nonneg M omega)
      (mul_nonneg (mul_nonneg (by norm_num) hCg) (Real.sqrt_nonneg M.nu))
  exact mul_pos
    (mul_pos (Real.sqrt_pos.2 (by norm_num)) (by
      linarith only [M.nu_pos, hrest]))
    (streamLogWeight_pos (one_le_streamTailDimensionFactor d))

private theorem one_add_euclideanNorm_le_mul (x : Vec d) :
    1 + euclideanNorm x ≤ streamTailDimensionFactor d * (1 + ‖x‖) := by
  have hE := euclideanNorm_le_dimension_mul_norm x
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  unfold streamTailDimensionFactor
  nlinarith only [hE, hd, hx, mul_nonneg hd hx]

private theorem streamPointLogWeight_le (x : Vec d) :
    streamPointLogWeight x ≤
      streamLogWeight (streamTailDimensionFactor d) *
        (1 + Real.log (1 + ‖x‖)) := by
  have hD := one_le_streamTailDimensionFactor d
  have hq : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have hprodPos : 0 < streamTailDimensionFactor d * (1 + ‖x‖) :=
    mul_pos (streamTailDimensionFactor_pos d) (lt_of_lt_of_le zero_lt_one hq)
  have hleftPos : 0 < 1 + euclideanNorm x :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (euclideanNorm_nonneg x))
  have hlog := Real.strictMonoOn_log.monotoneOn hleftPos hprodPos
    (one_add_euclideanNorm_le_mul x)
  rw [Real.log_mul (streamTailDimensionFactor_pos d).ne'
    (lt_of_lt_of_le zero_lt_one hq).ne'] at hlog
  have hlogD : 0 ≤ Real.log (streamTailDimensionFactor d) := Real.log_nonneg hD
  have hlogq : 0 ≤ Real.log (1 + ‖x‖) := Real.log_nonneg hq
  unfold streamPointLogWeight streamLogWeight
  nlinarith only [hlog, hlogD, hlogq, mul_nonneg hlogD hlogq]

private theorem streamPointLogWeight_ambient_le (x : Vec d) :
    streamPointLogWeight x ≤
      streamLogWeight (streamTailDimensionFactor d) * (1 + ‖x‖) := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (1 : ℝ) + ‖x‖ by positivity)
  have hD : 0 ≤ streamLogWeight (streamTailDimensionFactor d) :=
    (streamLogWeight_pos (one_le_streamTailDimensionFactor d)).le
  exact (streamPointLogWeight_le x).trans
    (mul_le_mul_of_nonneg_left (by linarith only [hlog]) hD)

private theorem streamLocalizedUpperBase_le_of_weight (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) {W : ℝ}
    (hone : 1 ≤ W) (hw : streamPointLogWeight x ≤ W) :
    streamLocalizedUpperBase M omega x ≤
      streamTailRawUpperConst M omega * W := by
  have hCs := streamFieldSmallBallConst_nonneg M omega
  have hCg : 0 ≤ Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d))
      (streamFieldLargeGradientConst_nonneg M omega)
  have hnu := M.nu_pos.le
  have hsqrt := Real.sqrt_nonneg M.nu
  unfold streamLocalizedUpperBase localizedAgmonUpper streamFieldSmallLocalConst
    streamFieldLargeDivLocalConst streamSplitObservationRadius streamTailRawUpperConst
  simp only [add_zero, div_one]
  change Real.sqrt 2 *
      (M.nu + streamFieldSmallBallConst M omega * streamPointLogWeight x +
        2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega *
          streamPointLogWeight x) * Real.sqrt M.nu) ≤
    Real.sqrt 2 *
      (M.nu + streamFieldSmallBallConst M omega +
        2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega) *
          Real.sqrt M.nu) * W
  have hnuScale : M.nu ≤ M.nu * W := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hnu
  have hCsScale := mul_le_mul_of_nonneg_left hw hCs
  have hCgScale := mul_le_mul_of_nonneg_left hw hCg
  have hsmooth :
      2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega *
          streamPointLogWeight x) * Real.sqrt M.nu ≤
        2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega * W) *
          Real.sqrt M.nu :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCgScale (by norm_num)) hsqrt
  have hinside := add_le_add (add_le_add hnuScale hCsScale) hsmooth
  calc
    _ ≤ Real.sqrt 2 * (M.nu * W +
        streamFieldSmallBallConst M omega * W +
        2 * (Real.sqrt d * (d : ℝ) * streamFieldLargeGradientConst M omega * W) *
          Real.sqrt M.nu) :=
      mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg 2)
    _ = _ := by ring

private theorem streamLocalizedUpperBase_le (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    streamLocalizedUpperBase M omega x ≤
      streamTailUpperConst M omega * (1 + ‖x‖) := by
  let W := streamLogWeight (streamTailDimensionFactor d) * (1 + ‖x‖)
  have hlogD : 0 ≤ Real.log (streamTailDimensionFactor d) :=
    Real.log_nonneg (one_le_streamTailDimensionFactor d)
  have hWone : 1 ≤ W := by
    unfold W streamLogWeight
    have hx := norm_nonneg x
    nlinarith only [hlogD, hx, mul_nonneg hlogD hx]
  have hbase := streamLocalizedUpperBase_le_of_weight M omega x hWone
    (streamPointLogWeight_ambient_le (d := d) x)
  simpa only [streamTailUpperConst, W, mul_assoc] using hbase

private theorem streamTailFloorConst_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) : 0 < streamTailFloorConst M omega := by
  unfold streamTailFloorConst
  apply lt_min
  · exact mul_pos
      (Real.rpow_pos_of_pos (streamFreezingAmplitude_pos M omega M.nu_pos
        (streamLocalizedTailDelta_pos d)) _)
      (Real.rpow_pos_of_pos (streamTailDimensionFactor_pos d) _)
  · norm_num

private theorem streamTailInnerFloor_lower (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    streamTailFloorConst M omega *
        Real.rpow (1 + ‖x‖) (-streamFreezingExponent M) ≤
      streamTailInnerFloor M omega x := by
  let A := streamFreezingAmplitude M omega M.nu (streamLocalizedTailDelta d)
  let e := streamFreezingExponent M
  let D := streamTailDimensionFactor d
  let q : ℝ := 1 + ‖x‖
  have hA : 0 < A := streamFreezingAmplitude_pos M omega M.nu_pos
    (streamLocalizedTailDelta_pos d)
  have he : 0 < e := streamFreezingExponent_pos M
  have hD : 0 < D := streamTailDimensionFactor_pos d
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg x)
  change streamTailFloorConst M omega * Real.rpow q (-e) ≤
    streamTailInnerFloor M omega x
  have hED : (1 : ℝ) + euclideanNorm x ≤ D * q := by
    simpa only [D, q] using one_add_euclideanNorm_le_mul x
  have hpow : Real.rpow (D * q) (-e) ≤
      Real.rpow (1 + euclideanNorm x) (-e) := by
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (euclideanNorm_nonneg x)))
      hED (by linarith only [he])
  have hfactor :
      Real.rpow D (-e) * Real.rpow q (-e) ≤
        Real.rpow (1 + euclideanNorm x) (-e) := by
    calc
      Real.rpow D (-e) * Real.rpow q (-e) = Real.rpow (D * q) (-e) :=
        (Real.mul_rpow hD.le (zero_le_one.trans hq)).symm
      _ ≤ _ := hpow
  have hqpow : Real.rpow q (-e) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith only [he])
  have hqpow0 : 0 ≤ Real.rpow q (-e) :=
    Real.rpow_nonneg (zero_le_one.trans hq) _
  rw [streamTailInnerFloor, streamFreezingRadius_eq_polynomial M omega M.nu_pos
    (streamLocalizedTailDelta_pos d) x]
  apply le_min
  · calc
      streamTailFloorConst M omega * Real.rpow q (-e) ≤
          (Real.rpow A e * Real.rpow D (-e)) * Real.rpow q (-e) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hqpow0
      _ ≤ Real.rpow A e * Real.rpow (1 + euclideanNorm x) (-e) :=
        by simpa only [mul_assoc] using!
          mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hA.le _)
      _ = _ := by rfl
  · calc
      streamTailFloorConst M omega * Real.rpow q (-e) ≤
          streamTailFloorConst M omega * 1 :=
        mul_le_mul_of_nonneg_left hqpow (streamTailFloorConst_pos M omega).le
      _ ≤ 1 / 2 := by simpa only [mul_one] using! (min_le_right _ _)

private theorem streamTailLinearConst_nonneg (M : ABKModel d) : 0 ≤ streamTailLinearConst M  := by
  unfold streamTailLinearConst
  exact add_nonneg
    (agmonTailL2Coefficient_nonneg d (lam := M.nu) (by norm_num))
    (agmonTailGradientCoefficient_nonneg d (lam := M.nu)
      (alpha := (1 / 2 : ℝ)) M.nu_pos (by norm_num))

private theorem tail_coefficients_eq_mul (M : ABKModel d) (L : ℝ) :
    agmonTailL2Coefficient d M.nu L +
        agmonTailGradientCoefficient d M.nu L (1 / 2 : ℝ) =
      streamTailLinearConst M * L  := by
  unfold streamTailLinearConst agmonTailL2Coefficient agmonTailGradientCoefficient
  ring

/-- The polynomial envelope amplitude is nonnegative. -/
theorem streamTailAmplitudeConst_nonneg (M : ABKModel d) (omega : FullSample d M.gamma) :
    0 ≤ streamTailAmplitudeConst M omega  := by
  have hU : 0 ≤ streamTailUpperConst M omega := by
    exact (streamTailUpperConst_pos M omega).le
  have hF := (streamTailFloorConst_pos M omega).le
  have hforce := agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)
  unfold streamTailAmplitudeConst
  exact add_nonneg
    (div_nonneg (mul_nonneg (streamTailLinearConst_nonneg M) hU) (pow_nonneg hF d))
    (div_nonneg (mul_nonneg (by norm_num) hforce) M.nu_pos.le)

/-- The logarithmic envelope decay numerator is strictly positive. -/
theorem streamTailDecayConst_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) : 0 < streamTailDecayConst M omega := by
  apply agmonTailRate_pos d M.nu_pos _ (by norm_num)
  exact streamTailUpperConst_pos M omega

/-- A polynomial envelope for the per-point algebraic amplitude. -/
theorem streamTailAlgebraicAmplitude_le (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    streamTailAlgebraicAmplitude M omega x ≤
      streamTailAmplitudeConst M omega *
        (1 + ‖x‖) ^ streamTailAmplitudeExponent M  := by
  let q : ℝ := 1 + ‖x‖
  let e := streamFreezingExponent M
  let F := streamTailFloorConst M omega
  let U := streamTailUpperConst M omega
  let P := streamTailLinearConst M
  let G := 4 * agmonTailForcingCoefficient d (1 / 2 : ℝ) / M.nu
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg x)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have he : 0 < e := streamFreezingExponent_pos M
  have hF : 0 < F := streamTailFloorConst_pos M omega
  have hfloor := streamTailInnerFloor_lower M omega x
  have hfloor' : F * Real.rpow q (-e) ≤ streamTailInnerFloor M omega x := by
    simpa only [F, q, e] using hfloor
  have hfloorPow :
      (F * Real.rpow q (-e)) ^ d ≤ streamTailInnerFloor M omega x ^ d :=
    pow_le_pow_left₀ (mul_nonneg hF.le (Real.rpow_nonneg (zero_le_one.trans hq) _))
      hfloor' d
  have hnum :
      agmonTailL2Coefficient d M.nu (streamLocalizedUpperBase M omega x) +
          agmonTailGradientCoefficient d M.nu
            (streamLocalizedUpperBase M omega x) (1 / 2 : ℝ) ≤
        P * (U * q) := by
    rw [tail_coefficients_eq_mul]
    exact mul_le_mul_of_nonneg_left (streamLocalizedUpperBase_le M omega x)
      (streamTailLinearConst_nonneg M)
  have hsmallDenPos : 0 < (F * Real.rpow q (-e)) ^ d :=
    pow_pos (mul_pos hF (Real.rpow_pos_of_pos hqpos _)) d
  have hright : 0 ≤ P * (U * q) := by
    exact mul_nonneg (streamTailLinearConst_nonneg M)
      (mul_nonneg (streamTailUpperConst_pos M omega).le (zero_le_one.trans hq))
  have hquot :
      (agmonTailL2Coefficient d M.nu (streamLocalizedUpperBase M omega x) +
          agmonTailGradientCoefficient d M.nu
            (streamLocalizedUpperBase M omega x) (1 / 2 : ℝ)) /
            streamTailInnerFloor M omega x ^ d ≤
        (P * (U * q)) / (F * Real.rpow q (-e)) ^ d := by
    exact div_le_div₀ hright hnum hsmallDenPos hfloorPow
  have hpowIdentity :
      (P * (U * q)) / (F * Real.rpow q (-e)) ^ d =
        (P * U / F ^ d) * Real.rpow q (1 + (d : ℝ) * e) := by
    simp only [Real.rpow_eq_pow]
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hq) (-e) d,
      show (-e) * (d : ℝ) = -(e * (d : ℝ)) by ring,
      Real.rpow_neg hqpos.le,
      show 1 + (d : ℝ) * e = 1 + e * (d : ℝ) by ring,
      Real.rpow_add hqpos, Real.rpow_one]
    field_simp
  have hqExponent : 1 ≤ Real.rpow q (1 + (d : ℝ) * e) := by
    exact Real.one_le_rpow hq (by positivity)
  have hG : 0 ≤ G := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (agmonTailForcingCoefficient_nonneg d (1 / 2 : ℝ)))
      M.nu_pos.le
  unfold streamTailAlgebraicAmplitude streamTailAmplitudeConst
    streamTailAmplitudeExponent
  change _ ≤ (P * U / F ^ d + G) * Real.rpow q (1 + (d : ℝ) * e)
  calc
    _ ≤ (P * (U * q)) / (F * Real.rpow q (-e)) ^ d + G :=
      add_le_add hquot le_rfl
    _ = (P * U / F ^ d) * Real.rpow q (1 + (d : ℝ) * e) + G := by
      rw [hpowIdentity]
    _ ≤ (P * U / F ^ d) * Real.rpow q (1 + (d : ℝ) * e) +
        G * Real.rpow q (1 + (d : ℝ) * e) :=
      add_le_add le_rfl (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hqExponent hG)
    _ = _ := by ring

/-- A logarithmic envelope for the per-point decay rate. -/
theorem streamTailDecayRate_ge (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    streamTailDecayConst M omega / (1 + Real.log (1 + ‖x‖)) ≤
      streamTailDecayRate M omega x := by
  have hW : 0 < 1 + Real.log (1 + ‖x‖) := by
    have hlog := Real.log_nonneg (le_add_of_nonneg_right (norm_nonneg x))
    linarith only [hlog]
  have hU : 0 < streamTailUpperConst M omega := by
    exact streamTailUpperConst_pos M omega
  have hbase : streamLocalizedUpperBase M omega x ≤
      streamTailUpperConst M omega * (1 + Real.log (1 + ‖x‖)) := by
    have hw := streamPointLogWeight_le (d := d) x
    let W := streamLogWeight (streamTailDimensionFactor d) *
      (1 + Real.log (1 + ‖x‖))
    have hlogD : 0 ≤ Real.log (streamTailDimensionFactor d) :=
      Real.log_nonneg (one_le_streamTailDimensionFactor d)
    have hone : 1 ≤ W := by
      unfold W streamLogWeight
      have hlogx := Real.log_nonneg (le_add_of_nonneg_right (norm_nonneg x))
      nlinarith only [hlogD, hlogx, mul_nonneg hlogD hlogx]
    have hlocal := streamLocalizedUpperBase_le_of_weight M omega x hone hw
    simpa only [streamTailUpperConst, W, mul_assoc] using hlocal
  unfold streamTailDecayConst streamTailDecayRate agmonTailRate
  have hLpos := streamLocalizedUpperBase_pos M omega x
  have hUWpos : 0 < streamTailUpperConst M omega *
      (1 + Real.log (1 + ‖x‖)) := mul_pos hU hW
  have hrecip : 1 / (streamTailUpperConst M omega *
      (1 + Real.log (1 + ‖x‖))) ≤
      1 / streamLocalizedUpperBase M omega x := by
    exact one_div_le_one_div_of_le hLpos hbase
  have hcoef : 0 ≤
      3 * Real.sqrt M.nu / (16 * Real.sqrt 2) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2)) := by positivity
  calc
    (3 * Real.sqrt M.nu / (16 * Real.sqrt 2 * streamTailUpperConst M omega) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2))) /
          (1 + Real.log (1 + ‖x‖)) =
      (3 * Real.sqrt M.nu / (16 * Real.sqrt 2) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2))) *
          (1 / (streamTailUpperConst M omega *
            (1 + Real.log (1 + ‖x‖))) ) := by field_simp
    _ ≤ (3 * Real.sqrt M.nu / (16 * Real.sqrt 2) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2))) *
          (1 / streamLocalizedUpperBase M omega x) :=
      mul_le_mul_of_nonneg_left hrecip hcoef
    _ = 3 * Real.sqrt M.nu /
          (16 * Real.sqrt 2 * streamLocalizedUpperBase M omega x) *
        ((1 / 2 : ℝ) / ((1 / 2 : ℝ) + (d : ℝ) / 2)) := by field_simp

end

end Algsuperdiff.Section5.Field
