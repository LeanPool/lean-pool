/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLowPowerTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLargeProvider
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# MomentBoostedLowPowerProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Low-power assembly for the moment-boosted large-cube route

This module turns the deterministic two-regime low-power concentration result
into the source-scale one-sided tail used by the final all-`p` provider.  It
keeps the `1 ≤ p ≤ 2` Jensen/Bernstein argument internal: no low-power
comparison, partition condition, or moment statement becomes a premise of a
source-facing declaration.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Dimension-only envelope for the `1 ≤ p ≤ 2` branch.  Squaring the fixed
color and partition losses is exactly what permits their absorption through
the concave exponent `p / 2 ≥ 1 / 2`. -/
noncomputable def momentBoostedLowPowerEnvelope (d : ℕ) : ℝ :=
  max 1 (4 * Real.exp 1 *
    (momentBoostedLowPowerColorConst (momentBoostedColorEnvelope d)) ^ (2 : ℕ) *
    (momentBoostedPartitionShiftEnvelope d) ^ (2 : ℕ) *
    momentBoostedStreamPointEnvelope d)

theorem one_le_momentBoostedLowPowerEnvelope (d : ℕ) :
    1 ≤ momentBoostedLowPowerEnvelope d :=
  le_max_left _ _

theorem momentBoostedLowPowerEnvelope_pos (d : ℕ) :
    0 < momentBoostedLowPowerEnvelope d :=
  lt_of_lt_of_le zero_lt_one (one_le_momentBoostedLowPowerEnvelope d)

private theorem streamIncrementLpMassScale_two_normal_form
    (M : ABKModel d) {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMassScale M 2 n m =
      Real.exp 1 * momentBoostedStreamPointEnvelope d *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
  rw [streamIncrementLpMassScale_eq_exp_mul_head M (by norm_num : (1 : ℝ) ≤ 2) hnm,
    streamIncrementLpMassHead]
  have hpoint := streamPointScale_sq M hnm
  rw [show (2 : ℝ) ^ ((2 : ℝ)⁻¹) = Real.sqrt 2 by
      rw [Real.sqrt_eq_rpow]
      congr 1
      norm_num]
  have hsqrt : Real.sqrt 2 ^ (2 : ℕ) = 2 := by norm_num
  have hsq : (gammaMomentConst 2 * streamPointScale M n m * Real.sqrt 2) ^ (2 : ℕ) =
      2 * (gammaMomentConst 2) ^ (2 : ℕ) * streamPointScale M n m ^ (2 : ℕ) := by
    rw [pow_two]
    calc
      (gammaMomentConst 2 * streamPointScale M n m * Real.sqrt 2) *
          (gammaMomentConst 2 * streamPointScale M n m * Real.sqrt 2) =
          ((gammaMomentConst 2 * streamPointScale M n m) ^ (2 : ℕ)) *
            (Real.sqrt 2 ^ (2 : ℕ)) := by ring
      _ = 2 * (gammaMomentConst 2) ^ (2 : ℕ) * streamPointScale M n m ^ (2 : ℕ) := by
        rw [hsqrt, pow_two]
        ring
  rw [Real.rpow_two]
  calc
    Real.exp 1 * (gammaMomentConst 2 * streamPointScale M n m * Real.sqrt 2) ^ (2 : ℕ) =
        Real.exp 1 * (2 * (gammaMomentConst 2) ^ (2 : ℕ) *
          streamPointScale M n m ^ (2 : ℕ)) := by rw [hsq]
    _ = Real.exp 1 * momentBoostedStreamPointEnvelope d *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
      rw [hpoint, momentBoostedStreamPointEnvelope]
      ring_nf

private theorem lowPower_partition_scale_le_shift
    {p : ℝ} (hp : 1 ≤ p) {l m : ℤ}
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    Book.Ch04.partitionCardinalityScale (d := d) 0
        (l - (m + (incrementPartitionShift d : ℤ))) ≤
      (momentBoostedPartitionShiftEnvelope d) ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
  have hj : 0 ≤ l - (m + (incrementPartitionShift d : ℤ)) := by omega
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hc : 0 ≤ (incrementPartitionShift d : ℝ) := by positivity
  have hr : (1 : ℝ) / 2 ≤ p / 2 := by linarith
  have hshift :
      (3 : ℝ) ^ (((d : ℝ) / 2) * (incrementPartitionShift d : ℝ)) ≤
        (momentBoostedPartitionShiftEnvelope d) ^ (p / 2) := by
    rw [momentBoostedPartitionShiftEnvelope, ← Real.rpow_mul h3.le]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdc : 0 ≤ (d : ℝ) * (incrementPartitionShift d : ℝ) := mul_nonneg hd hc
    calc
      ((d : ℝ) / 2) * (incrementPartitionShift d : ℝ) =
          ((d : ℝ) * (incrementPartitionShift d : ℝ)) * ((1 : ℝ) / 2) := by ring
      _ ≤ ((d : ℝ) * (incrementPartitionShift d : ℝ)) * (p / 2) :=
        mul_le_mul_of_nonneg_left hr hdc
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

private theorem lowPower_factor_le_square_rpow {x r : ℝ}
    (hx : 1 ≤ x) (hr : (1 : ℝ) / 2 ≤ r) :
    x ≤ (x ^ (2 : ℕ)) ^ r := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have htwo : 1 ≤ 2 * r := by linarith
  calc
    x = x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ ≤ x ^ (2 * r) := Real.rpow_le_rpow_of_exponent_le hx htwo
    _ = (x ^ (2 : ℕ)) ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
      congr 1

/-- The low-power colored endpoint in one-sided wrapper form before its
dimension-only source-scale envelope is applied. -/
theorem isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_lowPower_partition_raw
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : p ≤ 2)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    let K : ℝ := streamIncrementLpMassScale M 2 n m
    let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
    let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
    let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      (K ^ (p / 2))
      (momentBoostedLowPowerColorConst ((S.image color).card : ℝ) * K ^ (p / 2) /
        Real.sqrt (S.card : ℝ)) := by
  dsimp
  let K : ℝ := streamIncrementLpMassScale M 2 n m
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
  let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsigma : 0 < 2 / p := by positivity
  have hK : 0 < K := streamIncrementLpMassScale_pos M (by norm_num) hnm
  have hj : 0 ≤ j := by
    dsimp [j]
    omega
  have hS : S.Nonempty := by
    dsimp [S]
    exact descendantsAtScale_nonempty (originCube d j) hj
  have hq : 0 < ((S.image color).card : ℝ) := by
    exact_mod_cast (hS.image color).card_pos
  have hN : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have htail := isBigOWith_gammaSigma_streamIncrementLpMass_lowPower_partition
    M hp hp_two hnm hsl
  refine ⟨Probability.isAdmissibleTail_gammaSigma hsigma,
    div_pos
      (mul_pos (momentBoostedLowPowerColorConst_pos hq)
        (Real.rpow_pos_of_pos hK _))
      (Real.sqrt_pos.2 hN),
    measurable_streamIncrementLpMass_for_momentBoosted hp0 l n m, ?_⟩
  simpa [K, j, S, color] using htail

/-- The source-shaped scale used to absorb the deterministic low-power branch.
It is parameterized only by the model and indices; its constant is fixed by
the ambient dimension before any model is chosen. -/
noncomputable def momentBoostedLowPowerTargetScale
    (M : ABKModel d) (p : ℝ) (l n m : ℤ) : ℝ :=
  (momentBoostedLowPowerEnvelope d * p) ^ (p / 2) *
    (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
    (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))

private theorem momentBoostedLowPowerHeadTargetScale_pos
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    0 < (momentBoostedLowPowerEnvelope d * p) ^ (p / 2) *
      (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hgamma : 0 < M.gamma⁻¹ := inv_pos.mpr M.shellPrefix.gamma_pos
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  exact mul_pos
    (Real.rpow_pos_of_pos
      (mul_pos (momentBoostedLowPowerEnvelope_pos d) hp0) _)
    (Real.rpow_pos_of_pos
      (mul_pos (lt_min hgamma hmn) (Real.rpow_pos_of_pos (by norm_num) _)) _)

private theorem momentBoostedLowPowerTargetScale_pos
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {l n m : ℤ} (hnm : n < m) :
    0 < momentBoostedLowPowerTargetScale M p l n m := by
  unfold momentBoostedLowPowerTargetScale
  exact mul_pos (momentBoostedLowPowerHeadTargetScale_pos M hp hnm)
    (Real.rpow_pos_of_pos (by norm_num) _)

private theorem momentBoostedLowPowerEnvelope_absorbs_fixed_factor
    {p : ℝ} (hp : 1 ≤ p) :
    let r : ℝ := p / 2
    let L : ℝ := momentBoostedLowPowerColorConst (momentBoostedColorEnvelope d)
    let S : ℝ := momentBoostedPartitionShiftEnvelope d
    let P0 : ℝ := momentBoostedStreamPointEnvelope d
    L * (Real.exp 1) ^ r * S ^ r * P0 ^ r ≤
      (momentBoostedLowPowerEnvelope d) ^ r := by
  dsimp
  let r : ℝ := p / 2
  let L : ℝ := momentBoostedLowPowerColorConst (momentBoostedColorEnvelope d)
  let S : ℝ := momentBoostedPartitionShiftEnvelope d
  let P0 : ℝ := momentBoostedStreamPointEnvelope d
  let E : ℝ := momentBoostedLowPowerEnvelope d
  have hr : (1 : ℝ) / 2 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hL : 1 ≤ L := by
    dsimp [L]
    exact one_le_momentBoostedLowPowerColorConst
      (one_le_momentBoostedColorEnvelope d)
  have hS : 1 ≤ S := by
    dsimp [S]
    exact one_le_momentBoostedPartitionShiftEnvelope d
  have hP0 : 0 ≤ P0 := by
    dsimp [P0]
    exact momentBoostedStreamPointEnvelope_nonneg d
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hLpow : L ≤ (L ^ (2 : ℕ)) ^ r :=
    lowPower_factor_le_square_rpow hL hr
  have hSpow : S ^ r ≤ (S ^ (2 : ℕ)) ^ r := by
    apply Real.rpow_le_rpow (zero_le_one.trans hS) ?_ hr0
    nlinarith
  have hcore0 : 0 ≤ Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 := by
    positivity
  have hfour : Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 ≤
      4 * Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 := by
    calc
      Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 =
          1 * (Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0) := by ring
      _ ≤ 4 * (Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0) :=
        mul_le_mul_of_nonneg_right (by norm_num) hcore0
      _ = 4 * Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 := by ring
  have hbase : 4 * Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 ≤ E := by
    dsimp [E, L, S, P0, momentBoostedLowPowerEnvelope]
    exact le_max_right _ _
  have hcore :
      L * (Real.exp 1) ^ r * S ^ r * P0 ^ r ≤
        (Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0) ^ r := by
    have hfirst : L * (Real.exp 1) ^ r ≤
        (L ^ (2 : ℕ)) ^ r * (Real.exp 1) ^ r :=
      mul_le_mul_of_nonneg_right hLpow (Real.rpow_nonneg he _)
    have hsecond : ((L ^ (2 : ℕ)) ^ r * (Real.exp 1) ^ r) * S ^ r ≤
        ((L ^ (2 : ℕ)) ^ r * (Real.exp 1) ^ r) * (S ^ (2 : ℕ)) ^ r := by
      exact mul_le_mul_of_nonneg_left hSpow
        (mul_nonneg (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hL) _) _)
          (Real.rpow_nonneg he _))
    calc
      L * (Real.exp 1) ^ r * S ^ r * P0 ^ r ≤
          (L ^ (2 : ℕ)) ^ r * (Real.exp 1) ^ r * S ^ r * P0 ^ r := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfirst
          (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hS) _)
            (Real.rpow_nonneg hP0 _))
      _ ≤ (L ^ (2 : ℕ)) ^ r * (Real.exp 1) ^ r *
          (S ^ (2 : ℕ)) ^ r * P0 ^ r := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsecond
          (Real.rpow_nonneg hP0 _)
      _ = (Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0) ^ r := by
        rw [show Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 =
            (Real.exp 1 * L ^ (2 : ℕ)) * (S ^ (2 : ℕ) * P0) by ring,
          Real.mul_rpow
            (mul_nonneg he (pow_nonneg (zero_le_one.trans hL) _))
            (mul_nonneg (pow_nonneg (zero_le_one.trans hS) _) hP0),
          Real.mul_rpow he (pow_nonneg (zero_le_one.trans hL) _),
          Real.mul_rpow (pow_nonneg (zero_le_one.trans hS) _) hP0]
        ring
  have hfour0 : 0 ≤ 4 * Real.exp 1 * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 := by
    positivity
  exact hcore.trans
    ((Real.rpow_le_rpow hcore0 hfour hr0).trans
      (Real.rpow_le_rpow hfour0 hbase hr0))

private theorem lowPower_partition_tail_scale_le_target
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    momentBoostedLowPowerColorConst
        (((descendantsAtScale
          (originCube d (l - (m + (incrementPartitionShift d : ℤ)))) 0).image
          (cubeScaleColor 0)).card : ℝ) *
        streamIncrementLpMassScale M 2 n m ^ (p / 2) /
          Real.sqrt ((descendantsAtScale
            (originCube d (l - (m + (incrementPartitionShift d : ℤ)))) 0).card : ℝ) ≤
      momentBoostedLowPowerTargetScale M p l n m := by
  let r : ℝ := p / 2
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let S : Finset (TriadicCube d) := descendantsAtScale (originCube d j) 0
  let color : TriadicCube d → ScaleColor d 0 := cubeScaleColor 0
  let q : ℝ := ((S.image color).card : ℝ)
  let Lq : ℝ := momentBoostedLowPowerColorConst q
  let Q : ℝ := momentBoostedColorEnvelope d
  let L : ℝ := momentBoostedLowPowerColorConst Q
  let K : ℝ := streamIncrementLpMassScale M 2 n m
  let P0 : ℝ := momentBoostedStreamPointEnvelope d
  let S0 : ℝ := momentBoostedPartitionShiftEnvelope d
  let E : ℝ := momentBoostedLowPowerEnvelope d
  let B : ℝ := min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
  let G : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  change Lq * K ^ r / Real.sqrt (S.card : ℝ) ≤
    (E * p) ^ r * B ^ r * G
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr : (1 : ℝ) / 2 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hj : 0 ≤ j := by
    dsimp [j]
    omega
  have hS : S.Nonempty := by
    dsimp [S]
    exact descendantsAtScale_nonempty (originCube d j) hj
  have hN : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_of_lt (hS.image color).card_pos
  have hqQ : q ≤ Q := by
    dsimp [q, Q, S, color]
    exact card_used_scaleZero_colors_le_momentBoostedColorEnvelope (d := d) j
  have hLq : 0 ≤ Lq := zero_le_one.trans
    (one_le_momentBoostedLowPowerColorConst hq)
  have hLqL : Lq ≤ L := by
    dsimp [Lq, L]
    exact momentBoostedLowPowerColorConst_mono (zero_le_one.trans hq) hqQ
  have hK : 0 < K := by
    dsimp [K]
    exact streamIncrementLpMassScale_pos M (by norm_num) hnm
  have hB : 0 < B := by
    dsimp [B]
    have hgamma : 0 < M.gamma⁻¹ := inv_pos.mpr M.shellPrefix.gamma_pos
    have hmn : 0 < (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_pos (lt_min hgamma hmn) (Real.rpow_pos_of_pos (by norm_num) _)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact Real.rpow_nonneg (by norm_num) _
  have hpart : Book.Ch04.partitionCardinalityScale (d := d) 0 j ≤ S0 ^ r * G := by
    simpa [r, j, S0, G] using lowPower_partition_scale_le_shift (d := d) hp hsl
  have hdenom : Lq * K ^ r / Real.sqrt (S.card : ℝ) =
      Lq * K ^ r * Book.Ch04.partitionCardinalityScale (d := d) 0 j := by
    unfold Book.Ch04.partitionCardinalityScale
    dsimp [S]
    field_simp [hN.ne', (Real.sqrt_pos.2 hN).ne']
    rw [Real.sq_sqrt hN.le]
  have hfirst : Lq * K ^ r / Real.sqrt (S.card : ℝ) ≤
      Lq * K ^ r * (S0 ^ r * G) := by
    rw [hdenom]
    exact mul_le_mul_of_nonneg_left hpart
      (mul_nonneg hLq (Real.rpow_nonneg hK.le _))
  have hcolor : Lq * K ^ r * (S0 ^ r * G) ≤
      L * K ^ r * (S0 ^ r * G) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hLqL (Real.rpow_nonneg hK.le _))
      (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans
        (one_le_momentBoostedPartitionShiftEnvelope d)) _) hG)
  have hKform : K = Real.exp 1 * P0 * B := by
    dsimp [K, P0, B]
    exact streamIncrementLpMassScale_two_normal_form M hnm
  have hfixed : L * (Real.exp 1) ^ r * S0 ^ r * P0 ^ r ≤ E ^ r := by
    simpa [r, L, S0, P0, E] using
      momentBoostedLowPowerEnvelope_absorbs_fixed_factor (d := d) hp
  have hEp : E ^ r ≤ (E * p) ^ r := by
    have hE : 0 < E := by
      dsimp [E]
      exact momentBoostedLowPowerEnvelope_pos d
    apply Real.rpow_le_rpow hE.le ?_ hr0
    simpa only [mul_comm] using le_mul_of_one_le_left hE.le hp
  have hmain : L * K ^ r * (S0 ^ r * G) ≤ (E * p) ^ r * B ^ r * G := by
    rw [hKform]
    have hpow : (Real.exp 1 * P0 * B) ^ r =
        (Real.exp 1) ^ r * P0 ^ r * B ^ r := by
      rw [show Real.exp 1 * P0 * B = (Real.exp 1 * P0) * B by ring,
        Real.mul_rpow (mul_nonneg (Real.exp_pos 1).le
          (momentBoostedStreamPointEnvelope_nonneg d)) hB.le,
        Real.mul_rpow (Real.exp_pos 1).le
          (momentBoostedStreamPointEnvelope_nonneg d)]
    rw [hpow]
    calc
      L * ((Real.exp 1) ^ r * P0 ^ r * B ^ r) * (S0 ^ r * G) =
          (L * (Real.exp 1) ^ r * S0 ^ r * P0 ^ r) * (B ^ r * G) := by ring
      _ ≤ E ^ r * (B ^ r * G) :=
        mul_le_mul_of_nonneg_right hfixed
          (mul_nonneg (Real.rpow_nonneg hB.le _) hG)
      _ ≤ (E * p) ^ r * (B ^ r * G) :=
        mul_le_mul_of_nonneg_right hEp
          (mul_nonneg (Real.rpow_nonneg hB.le _) hG)
      _ = (E * p) ^ r * B ^ r * G := by ring
  exact hfirst.trans (hcolor.trans hmain)

private theorem lowPower_raw_shift_le_head_target
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMassScale M 2 n m ^ (p / 2) ≤
      (momentBoostedLowPowerEnvelope d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) := by
  let r : ℝ := p / 2
  let L : ℝ := momentBoostedLowPowerColorConst (momentBoostedColorEnvelope d)
  let S : ℝ := momentBoostedPartitionShiftEnvelope d
  let P0 : ℝ := momentBoostedStreamPointEnvelope d
  let E : ℝ := momentBoostedLowPowerEnvelope d
  let B : ℝ := min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
  let K : ℝ := streamIncrementLpMassScale M 2 n m
  change K ^ r ≤ (E * p) ^ r * B ^ r
  have hr : (1 : ℝ) / 2 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hL : 1 ≤ L := by
    dsimp [L]
    exact one_le_momentBoostedLowPowerColorConst
      (one_le_momentBoostedColorEnvelope d)
  have hS : 1 ≤ S := by
    dsimp [S]
    exact one_le_momentBoostedPartitionShiftEnvelope d
  have hSr : 1 ≤ S ^ r := Real.one_le_rpow hS hr0
  have hLS : 1 ≤ L * S ^ r := one_le_mul_of_one_le_of_one_le hL hSr
  have hP0 : 0 ≤ P0 := by
    dsimp [P0]
    exact momentBoostedStreamPointEnvelope_nonneg d
  have hB : 0 < B := by
    dsimp [B]
    have hgamma : 0 < M.gamma⁻¹ := inv_pos.mpr M.shellPrefix.gamma_pos
    have hmn : 0 < (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_pos (lt_min hgamma hmn) (Real.rpow_pos_of_pos (by norm_num) _)
  have hbare : (Real.exp 1) ^ r * P0 ^ r ≤
      L * (Real.exp 1) ^ r * S ^ r * P0 ^ r := by
    calc
      (Real.exp 1) ^ r * P0 ^ r =
          1 * ((Real.exp 1) ^ r * P0 ^ r) := by ring
      _ ≤ (L * S ^ r) * ((Real.exp 1) ^ r * P0 ^ r) :=
        mul_le_mul_of_nonneg_right hLS
          (mul_nonneg (Real.rpow_nonneg (Real.exp_pos 1).le _)
            (Real.rpow_nonneg hP0 _))
      _ = L * (Real.exp 1) ^ r * S ^ r * P0 ^ r := by ring
  have hfixed : L * (Real.exp 1) ^ r * S ^ r * P0 ^ r ≤ E ^ r := by
    simpa [r, L, S, P0, E] using
      momentBoostedLowPowerEnvelope_absorbs_fixed_factor (d := d) hp
  have hEp : E ^ r ≤ (E * p) ^ r := by
    have hE : 0 < E := by
      dsimp [E]
      exact momentBoostedLowPowerEnvelope_pos d
    apply Real.rpow_le_rpow hE.le ?_ hr0
    simpa only [mul_comm] using le_mul_of_one_le_left hE.le hp
  have hKform : K = Real.exp 1 * P0 * B := by
    dsimp [K, P0, B]
    exact streamIncrementLpMassScale_two_normal_form M hnm
  rw [hKform]
  have hpow : (Real.exp 1 * P0 * B) ^ r =
      (Real.exp 1) ^ r * P0 ^ r * B ^ r := by
    rw [show Real.exp 1 * P0 * B = (Real.exp 1 * P0) * B by ring,
      Real.mul_rpow (mul_nonneg (Real.exp_pos 1).le hP0) hB.le,
      Real.mul_rpow (Real.exp_pos 1).le hP0]
  rw [hpow]
  calc
    (Real.exp 1) ^ r * P0 ^ r * B ^ r ≤ E ^ r * B ^ r :=
      mul_le_mul_of_nonneg_right (hbare.trans hfixed) (Real.rpow_nonneg hB.le _)
    _ ≤ (E * p) ^ r * B ^ r :=
      mul_le_mul_of_nonneg_right hEp (Real.rpow_nonneg hB.le _)

/-- The `1 ≤ p ≤ 2` partition carrier after both the deterministic shift and
tail have been enlarged to the fixed dimension-only low-power envelope.  The
exponent split and partition condition are internal case-split data. -/
theorem isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_lowPower_partition_envelope
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : p ≤ 2)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      ((momentBoostedLowPowerEnvelope d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2))
      (momentBoostedLowPowerTargetScale M p l n m) := by
  have hraw := isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_lowPower_partition_raw
    M hp hp_two hnm hsl
  refine ⟨hraw.1, momentBoostedLowPowerTargetScale_pos M hp hnm,
    hraw.2.2.1, ?_⟩
  have htail := hraw.2.2.2.mono_scale
    (lowPower_partition_tail_scale_le_target M hp hnm hsl)
  have hshift := lowPower_raw_shift_le_head_target M hp hnm
  exact htail.of_le fun omega => by
    linarith

end

end Algsuperdiff.Section3.Provider.Stream
