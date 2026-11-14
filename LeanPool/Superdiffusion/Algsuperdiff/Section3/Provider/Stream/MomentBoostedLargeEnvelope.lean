/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLargeTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpSquared

/-!
# MomentBoostedLargeEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Dimension-only envelope arithmetic for the sharp large-cube route

The finite-family transport leaves explicit numerical, color, and partition
normalization factors.  This module records the deterministic algebra showing
how those factors fit the manuscript's single `C(d)` before the model and
indices are quantified.  It is internal support for the exact frozen export.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The number of available scale-zero colors, as a real dimension-only
quantity. -/
noncomputable def momentBoostedColorEnvelope (d : ℕ) : ℝ :=
  (scaleColorPeriod 0 : ℝ) ^ (d : ℝ)

theorem one_le_momentBoostedColorEnvelope (d : ℕ) :
    1 ≤ momentBoostedColorEnvelope d := by
  unfold momentBoostedColorEnvelope
  have hperiod : (1 : ℝ) ≤ (scaleColorPeriod 0 : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (scaleColorPeriod_pos 0)
  exact Real.one_le_rpow hperiod (by positivity)

theorem card_used_scaleZero_colors_le_momentBoostedColorEnvelope
    (j : ℤ) :
    (((descendantsAtScale (originCube d j) 0).image (cubeScaleColor 0)).card : ℝ) ≤
      momentBoostedColorEnvelope d := by
  unfold momentBoostedColorEnvelope
  have h := card_image_cubeScaleColor_descendantsAtScale_le (originCube d j) 0
  exact_mod_cast h

/-- The fixed geometric loss incurred by shifting the partition down to scale
zero. -/
noncomputable def momentBoostedPartitionShiftEnvelope (d : ℕ) : ℝ :=
  (3 : ℝ) ^ ((d : ℝ) * (incrementPartitionShift d : ℝ))

theorem one_le_momentBoostedPartitionShiftEnvelope (d : ℕ) :
    1 ≤ momentBoostedPartitionShiftEnvelope d := by
  unfold momentBoostedPartitionShiftEnvelope
  exact Real.one_le_rpow (by norm_num) (by positivity)

/-- The source-scale coefficient carried by `streamPointScale`. -/
noncomputable def momentBoostedStreamPointEnvelope (d : ℕ) : ℝ :=
  2 * (gammaMomentConst 2 * gammaTriangleConst 2 * (d : ℝ) ^ 2 *
    geometricConcentrationConst) ^ (2 : ℕ)

theorem momentBoostedStreamPointEnvelope_nonneg (d : ℕ) :
    0 ≤ momentBoostedStreamPointEnvelope d := by
  unfold momentBoostedStreamPointEnvelope
  positivity

/-- A single positive dimension-only envelope for the strict `p > 2` branch.
It is intentionally generous so the deterministic branch comparison remains
transparent and no `p`-dependent concentration constant is hidden in it. -/
noncomputable def momentBoostedLargeCubeEnvelope (d : ℕ) : ℝ :=
  max 1
    (32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) *
      momentBoostedPartitionShiftEnvelope d * momentBoostedStreamPointEnvelope d)

theorem one_le_momentBoostedLargeCubeEnvelope (d : ℕ) :
    1 ≤ momentBoostedLargeCubeEnvelope d :=
  le_max_left _ _

theorem momentBoostedLargeCubeEnvelope_pos (d : ℕ) :
    0 < momentBoostedLargeCubeEnvelope d :=
  lt_of_lt_of_le zero_lt_one (one_le_momentBoostedLargeCubeEnvelope d)

/-- Exact normal form of the local moment-boosted scale.  The sole
`p`-dependent factor is the displayed source factor `p`; every other factor
is the square of a dimension-only point scale times the manuscript amplitude.
-/
private theorem streamIncrementLpMomentBoostScale_normal_form
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMomentBoostScale M p n m =
      (momentBoostedStreamPointEnvelope d * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) ^ (p / 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ha : 0 < gammaMomentConst 2 * streamPointScale M n m :=
    mul_pos (gammaMomentConst_pos (by norm_num)) (streamPointScale_pos M hnm)
  have hpoint := streamPointScale_sq M hnm
  rw [streamIncrementLpMomentBoostScale]
  have htwo : (2 : ℝ) ^ (p / 2) = ((2 : ℝ) * 1) ^ (p / 2) := by ring_nf
  rw [htwo, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) zero_le_one]
  simp only [Real.one_rpow, mul_one]
  have hmain :
      (gammaMomentConst 2 * streamPointScale M n m) ^ p * p ^ (p / 2) =
        ((gammaMomentConst 2 * streamPointScale M n m) ^ (2 : ℕ) * p) ^ (p / 2) := by
    rw [Real.mul_rpow (pow_nonneg ha.le 2) hp0.le]
    have hpow : (gammaMomentConst 2 * streamPointScale M n m) ^ p =
        ((gammaMomentConst 2 * streamPointScale M n m) ^ (2 : ℕ)) ^ (p / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      congr 1
      ring
    rw [hpow]
  rw [hmain, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (mul_nonneg (pow_nonneg ha.le 2) hp0.le)]
  congr 1
  rw [show (2 : ℝ) * ((gammaMomentConst 2 * streamPointScale M n m) ^ (2 : ℕ) * p) =
      (2 * (gammaMomentConst 2) ^ (2 : ℕ) * streamPointScale M n m ^ (2 : ℕ)) * p by ring,
    hpoint, momentBoostedStreamPointEnvelope]
  ring_nf

private theorem momentBoosted_color_factor_le_envelope
    {p q Q : ℝ} (hp_two : 2 < p) (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    32 * q * q ^ (p / 2) * (8192 : ℝ) ^ (p / 2) ≤
      (32 * Q ^ (2 : ℕ) * 8192) ^ (p / 2) := by
  have hp_half : 1 ≤ p / 2 := by linarith
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hQ : 1 ≤ Q := hq.trans hqQ
  have hqpow : q ≤ q ^ (p / 2) :=
    by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq hp_half
  have hq_sq : q ^ (2 : ℕ) ≤ Q ^ (2 : ℕ) := by nlinarith
  have hq_sq_nonneg : 0 ≤ q ^ (2 : ℕ) := by positivity
  have hQ_sq_nonneg : 0 ≤ Q ^ (2 : ℕ) := by positivity
  have hqprod : q ^ (2 : ℕ) * 8192 ≤ Q ^ (2 : ℕ) * 8192 :=
    mul_le_mul_of_nonneg_right hq_sq (by norm_num)
  have hpowprod :
      (q ^ (2 : ℕ) * 8192) ^ (p / 2) ≤
        (Q ^ (2 : ℕ) * 8192) ^ (p / 2) :=
    Real.rpow_le_rpow (mul_nonneg hq_sq_nonneg (by norm_num)) hqprod (by positivity)
  have h32 : (32 : ℝ) ≤ 32 ^ (p / 2) :=
    by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 32) hp_half
  calc
    32 * q * q ^ (p / 2) * 8192 ^ (p / 2) ≤
        32 * q ^ (p / 2) * q ^ (p / 2) * 8192 ^ (p / 2) := by
          gcongr
    _ = 32 * (q ^ (2 : ℕ) * 8192) ^ (p / 2) := by
          have hqq : q ^ (p / 2) * q ^ (p / 2) =
              (q ^ (2 : ℕ)) ^ (p / 2) := by
            rw [← Real.rpow_add hqpos]
            have hexp : p / 2 + p / 2 = (2 : ℝ) * (p / 2) := by ring
            rw [hexp, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
            norm_num
          calc
            32 * q ^ (p / 2) * q ^ (p / 2) * 8192 ^ (p / 2) =
                32 * (q ^ (p / 2) * q ^ (p / 2)) * 8192 ^ (p / 2) := by ring
            _ = 32 * (q ^ (2 : ℕ)) ^ (p / 2) * 8192 ^ (p / 2) := by rw [hqq]
            _ = 32 * (q ^ (2 : ℕ) * 8192) ^ (p / 2) := by
              rw [Real.mul_rpow (pow_nonneg hq0 2) (by norm_num : (0 : ℝ) ≤ 8192)]
              ring
    _ ≤ 32 * (Q ^ (2 : ℕ) * 8192) ^ (p / 2) :=
      mul_le_mul_of_nonneg_left hpowprod (by norm_num)
    _ ≤ 32 ^ (p / 2) * (Q ^ (2 : ℕ) * 8192) ^ (p / 2) :=
      mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg (by positivity) _)
    _ = (32 * Q ^ (2 : ℕ) * 8192) ^ (p / 2) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32)
        (mul_nonneg hQ_sq_nonneg (by norm_num))]
      ring_nf

private theorem partition_scale_le_momentBoosted_shift_envelope
    {p : ℝ} (hp_two : 2 < p) {l m : ℤ}
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.partitionCardinalityScale (d := d) 0
        (l - (m + (incrementPartitionShift d : ℤ))) ≤
      (momentBoostedPartitionShiftEnvelope d) ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
  have hj : 0 ≤ l - (m + (incrementPartitionShift d : ℤ)) := by omega
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hc : 0 ≤ (incrementPartitionShift d : ℝ) := by positivity
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hp_half : 1 ≤ p / 2 := by linarith
  have hshift :
      (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) ≤
        (momentBoostedPartitionShiftEnvelope d) ^ (p / 2) := by
    rw [momentBoostedPartitionShiftEnvelope, ← Real.rpow_mul h3.le]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdc : 0 ≤ (d : ℝ) * (incrementPartitionShift d : ℝ) :=
      mul_nonneg hd hc
    calc
      ((d : ℝ) / 2) * (incrementPartitionShift d : ℝ) =
          ((d : ℝ) * (incrementPartitionShift d : ℝ)) * ((1 : ℝ) / 2) := by ring
      _ ≤ ((d : ℝ) * (incrementPartitionShift d : ℝ)) * (p / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hdc
  have hsplit :
      (3 : ℝ) ^ (-((d : ℝ) / 2) *
          ((l - (m + (incrementPartitionShift d : ℤ)) : ℤ) : ℝ)) =
        (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    rw [← Real.rpow_add h3]
    congr 1
    push_cast
    ring
  rw [partitionCardinalityScale_originCube_zero (d := d) hj, hsplit]
  exact mul_le_mul_of_nonneg_right hshift (Real.rpow_nonneg h3.le _)

theorem momentBoosted_sharp_scale_le_source_shape
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l)
    {q : ℝ} (hq : 1 ≤ q) (hqQ : q ≤ momentBoostedColorEnvelope d) :
    let sigma : ℝ := 2 / p
    let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
    16 * q * q ^ (1 / sigma) *
        Real.sqrt (momentBoostedIndependentVariance sigma) *
        streamIncrementLpMomentBoostScale M p n m *
        Book.Ch04.partitionCardinalityScale (d := d) 0 j ≤
      (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
  dsimp
  let sigma : ℝ := 2 / p
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let Q : ℝ := momentBoostedColorEnvelope d
  let S : ℝ := momentBoostedPartitionShiftEnvelope d
  let P0 : ℝ := momentBoostedStreamPointEnvelope d
  let B : ℝ := min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
  let C0 : ℝ := 32 * Q ^ (2 : ℕ) * 8192
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    positivity
  have hinv : 1 / sigma = p / 2 := by
    dsimp [sigma]
    field_simp [hp0.ne']
  have hsqrt : Real.sqrt (momentBoostedIndependentVariance sigma) =
      2 * (8192 : ℝ) ^ (p / 2) := by
    rw [sqrt_momentBoostedIndependentVariance hsigma, hinv]
  have hcolor :
      16 * q * q ^ (1 / sigma) * Real.sqrt (momentBoostedIndependentVariance sigma) ≤
        C0 ^ (p / 2) := by
    rw [hinv, hsqrt]
    rw [show 16 * q * q ^ (p / 2) * (2 * 8192 ^ (p / 2)) =
      32 * q * q ^ (p / 2) * 8192 ^ (p / 2) by ring]
    simpa [C0] using momentBoosted_color_factor_le_envelope hp_two hq (by simpa [Q] using hqQ)
  have hpart : Book.Ch04.partitionCardinalityScale (d := d) 0 j ≤
      S ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    simpa [j, S] using partition_scale_le_momentBoosted_shift_envelope
      (d := d) hp_two hsl
  have hV : streamIncrementLpMomentBoostScale M p n m = (P0 * p * B) ^ (p / 2) := by
    simpa [P0, B] using streamIncrementLpMomentBoostScale_normal_form M hp hnm
  have hB : 0 ≤ B := by
    dsimp [B]
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hP0 : 0 ≤ P0 := by simpa [P0] using momentBoostedStreamPointEnvelope_nonneg d
  have hS : 0 ≤ S := zero_le_one.trans (by
    simpa [S] using one_le_momentBoostedPartitionShiftEnvelope d)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0, Q]
    positivity
  have hbase : C0 * S * P0 ≤ momentBoostedLargeCubeEnvelope d := by
    unfold momentBoostedLargeCubeEnvelope
    change 32 * Q ^ (2 : ℕ) * 8192 *
        momentBoostedPartitionShiftEnvelope d * momentBoostedStreamPointEnvelope d ≤
      max 1 (32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) *
        momentBoostedPartitionShiftEnvelope d * momentBoostedStreamPointEnvelope d)
    change 32 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) * 8192 *
        momentBoostedPartitionShiftEnvelope d * momentBoostedStreamPointEnvelope d ≤ _
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (le_max_right (1 : ℝ)
        (32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) *
          momentBoostedPartitionShiftEnvelope d * momentBoostedStreamPointEnvelope d))
  have hinner : C0 * S * P0 * p * B ≤ momentBoostedLargeCubeEnvelope d * p * B := by
    have hpb : 0 ≤ p * B := mul_nonneg hp0.le hB
    calc
      C0 * S * P0 * p * B = (C0 * S * P0) * (p * B) := by ring
      _ ≤ momentBoostedLargeCubeEnvelope d * (p * B) :=
        mul_le_mul_of_nonneg_right hbase hpb
      _ = momentBoostedLargeCubeEnvelope d * p * B := by ring
  have hsource :
      (C0 * S * P0 * p * B) ^ (p / 2) ≤
        (momentBoostedLargeCubeEnvelope d * p * B) ^ (p / 2) :=
    Real.rpow_le_rpow (by positivity) hinner (by positivity)
  calc
    16 * q * q ^ (1 / sigma) * Real.sqrt (momentBoostedIndependentVariance sigma) *
        streamIncrementLpMomentBoostScale M p n m *
        Book.Ch04.partitionCardinalityScale 0 j ≤
        (C0 ^ (p / 2) * (P0 * p * B) ^ (p / 2)) *
          (S ^ (p / 2) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := by
          rw [hV]
          have hVpow : 0 ≤ (P0 * p * B) ^ (p / 2) :=
            Real.rpow_nonneg (mul_nonneg (mul_nonneg hP0 hp0.le) hB) _
          have hpart0 : 0 ≤ Book.Ch04.partitionCardinalityScale (d := d) 0 j := by
            rw [Book.Ch04.partitionCardinalityScale]
            positivity
          have hcolorV :
              (16 * q * q ^ (1 / sigma) * Real.sqrt (momentBoostedIndependentVariance sigma)) *
                (P0 * p * B) ^ (p / 2) ≤
              C0 ^ (p / 2) * (P0 * p * B) ^ (p / 2) :=
            mul_le_mul_of_nonneg_right hcolor hVpow
          calc
            16 * q * q ^ (1 / sigma) * Real.sqrt (momentBoostedIndependentVariance sigma) *
                (P0 * p * B) ^ (p / 2) * Book.Ch04.partitionCardinalityScale 0 j ≤
                C0 ^ (p / 2) * (P0 * p * B) ^ (p / 2) *
                  Book.Ch04.partitionCardinalityScale 0 j :=
              mul_le_mul_of_nonneg_right hcolorV hpart0
            _ ≤ (C0 ^ (p / 2) * (P0 * p * B) ^ (p / 2)) *
                (S ^ (p / 2) *
                  (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) :=
              mul_le_mul_of_nonneg_left hpart (mul_nonneg (Real.rpow_nonneg hC0 _) hVpow)
    _ = (C0 * S * P0 * p * B) ^ (p / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
          have hfactor : C0 ^ (p / 2) * (P0 * p * B) ^ (p / 2) * S ^ (p / 2) =
              (C0 * S * P0 * p * B) ^ (p / 2) := by
            rw [show C0 * S * P0 * p * B = (C0 * S) * (P0 * p * B) by ring,
              Real.mul_rpow (mul_nonneg hC0 hS) (by positivity),
              Real.mul_rpow hC0 hS]
            ring
          rw [show C0 ^ (p / 2) * (P0 * p * B) ^ (p / 2) *
              (S ^ (p / 2) * (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) =
              (C0 ^ (p / 2) * (P0 * p * B) ^ (p / 2) * S ^ (p / 2)) *
                (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) by ring,
            hfactor]
    _ ≤ (momentBoostedLargeCubeEnvelope d * p * B) ^ (p / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) :=
      mul_le_mul_of_nonneg_right hsource (Real.rpow_nonneg (by norm_num) _)
    _ = (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) * B ^ (p / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
      rw [Real.mul_rpow
        (mul_nonneg (zero_le_one.trans (one_le_momentBoostedLargeCubeEnvelope d)) hp0.le) hB]

theorem momentBoosted_direct_scale_le_source_shape
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m) (hml : m ≤ l)
    (hwindow : ¬ m + (incrementPartitionShift d : ℤ) ≤ l) :
    streamIncrementLpMomentBoostScale M p n m ≤
      (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
  let P0 : ℝ := momentBoostedStreamPointEnvelope d
  let S : ℝ := momentBoostedPartitionShiftEnvelope d
  let B : ℝ := min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
  let G : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_half : 1 ≤ p / 2 := by linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hP0 : 0 ≤ P0 := by simpa [P0] using momentBoostedStreamPointEnvelope_nonneg d
  have hS : 1 ≤ S := by simpa [S] using one_le_momentBoostedPartitionShiftEnvelope d
  have hG : 0 ≤ G := Real.rpow_nonneg (by norm_num) _
  have hlt : l < m + (incrementPartitionShift d : ℤ) := lt_of_not_ge hwindow
  have hgap : 0 ≤ (l : ℝ) - (m : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hml)
  have hshift_gain : 1 ≤ S ^ (p / 2) * G := by
    dsimp [S, G, momentBoostedPartitionShiftEnvelope]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [← Real.rpow_zero (3 : ℝ)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    have hdiff : (l : ℝ) - (m : ℝ) ≤ (incrementPartitionShift d : ℝ) := by
      have hcast : (l : ℝ) < (m : ℝ) + (incrementPartitionShift d : ℝ) := by
        exact_mod_cast hlt
      linarith [hgap]
    have hdc : 0 ≤ (d : ℝ) * (incrementPartitionShift d : ℝ) := by positivity
    have hpc : (d : ℝ) * (incrementPartitionShift d : ℝ) ≤
        (d : ℝ) * (incrementPartitionShift d : ℝ) * (p / 2) := by
      calc
        (d : ℝ) * (incrementPartitionShift d : ℝ) =
            ((d : ℝ) * (incrementPartitionShift d : ℝ)) * 1 := by ring
        _ ≤ ((d : ℝ) * (incrementPartitionShift d : ℝ)) * (p / 2) :=
          mul_le_mul_of_nonneg_left hp_half hdc
    have hsmall : ((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)) ≤
        ((d : ℝ) / 2) * (incrementPartitionShift d : ℝ) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    nlinarith
  have hC : S * P0 ≤ momentBoostedLargeCubeEnvelope d := by
    have hC0 : 1 ≤ 32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) := by
      have hQ := one_le_momentBoostedColorEnvelope d
      have hQsq : 1 ≤ (momentBoostedColorEnvelope d) ^ (2 : ℕ) := by nlinarith
      nlinarith
    have hSP0 : 0 ≤ S * P0 := mul_nonneg (zero_le_one.trans hS) hP0
    have hmain : S * P0 ≤
        32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) * S * P0 := by
      calc
        S * P0 = 1 * (S * P0) := by ring
        _ ≤ (32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ)) * (S * P0) :=
          mul_le_mul_of_nonneg_right hC0 hSP0
        _ = 32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) * S * P0 := by ring
    calc
      S * P0 ≤ 32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) * S * P0 := hmain
      _ = 32 * 8192 * (momentBoostedColorEnvelope d) ^ (2 : ℕ) *
          momentBoostedPartitionShiftEnvelope d * momentBoostedStreamPointEnvelope d := by
            simp only [S, P0]
      _ ≤ momentBoostedLargeCubeEnvelope d := le_max_right _ _
  have hCpow : (S * P0) ^ (p / 2) ≤
      (momentBoostedLargeCubeEnvelope d) ^ (p / 2) :=
    Real.rpow_le_rpow (mul_nonneg (zero_le_one.trans hS) hP0) hC (by positivity)
  have hpoint :
      streamIncrementLpMomentBoostScale M p n m = (P0 * p * B) ^ (p / 2) := by
    simpa [P0, B] using streamIncrementLpMomentBoostScale_normal_form M hp hnm
  rw [hpoint]
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hC0 : 0 ≤ momentBoostedLargeCubeEnvelope d :=
    zero_le_one.trans (one_le_momentBoostedLargeCubeEnvelope d)
  have hPB0 : 0 ≤ p * B := mul_nonneg hp0.le hB
  calc
    (P0 * p * B) ^ (p / 2) ≤
        ((S * P0) ^ (p / 2) * (p * B) ^ (p / 2)) * G := by
          have hpow : (P0 * p * B) ^ (p / 2) =
              P0 ^ (p / 2) * (p * B) ^ (p / 2) := by
            rw [show P0 * p * B = P0 * (p * B) by ring,
              Real.mul_rpow hP0 hPB0]
          rw [hpow]
          have hbase : 0 ≤ P0 ^ (p / 2) * (p * B) ^ (p / 2) := by positivity
          calc
            P0 ^ (p / 2) * (p * B) ^ (p / 2) ≤
                (P0 ^ (p / 2) * (p * B) ^ (p / 2)) *
                  (S ^ (p / 2) * G) :=
              calc
                P0 ^ (p / 2) * (p * B) ^ (p / 2) =
                    (P0 ^ (p / 2) * (p * B) ^ (p / 2)) * 1 := by ring
                _ ≤ (P0 ^ (p / 2) * (p * B) ^ (p / 2)) *
                    (S ^ (p / 2) * G) :=
                  mul_le_mul_of_nonneg_left hshift_gain hbase
            _ = (S * P0) ^ (p / 2) * (p * B) ^ (p / 2) * G := by
              rw [Real.mul_rpow hS0 hP0]
              ring
    _ ≤ ((momentBoostedLargeCubeEnvelope d) ^ (p / 2) * (p * B) ^ (p / 2)) * G :=
      by
        calc
          (S * P0) ^ (p / 2) * (p * B) ^ (p / 2) * G =
              (S * P0) ^ (p / 2) * ((p * B) ^ (p / 2) * G) := by ring
          _ ≤ (momentBoostedLargeCubeEnvelope d) ^ (p / 2) *
              ((p * B) ^ (p / 2) * G) :=
            mul_le_mul_of_nonneg_right hCpow
              (mul_nonneg (Real.rpow_nonneg hPB0 _) hG)
          _ = (momentBoostedLargeCubeEnvelope d) ^ (p / 2) *
              (p * B) ^ (p / 2) * G := by ring
    _ = (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) * B ^ (p / 2) * G := by
      rw [← Real.mul_rpow hC0 hPB0,
        show momentBoostedLargeCubeEnvelope d * (p * B) =
          (momentBoostedLargeCubeEnvelope d * p) * B by ring,
        Real.mul_rpow (mul_nonneg hC0 hp0.le) hB]

end

end Algsuperdiff.Section3.Provider.Stream
