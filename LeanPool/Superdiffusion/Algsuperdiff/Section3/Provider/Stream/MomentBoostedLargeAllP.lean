/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLowPowerProvider

/-!
# MomentBoostedLargeAllP

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# All-exponent assembly for the moment-boosted large-cube route

This module joins the strict high-power carrier and the concave low-power
carrier under one dimension-only envelope.  Partition/window distinctions and
the two exponent ranges are discharged here; the public result below this
module has no such proof-engineering premises.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory ProbabilityTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Extra fixed window margin for the low-power branch. -/
noncomputable def momentBoostedLowPowerWindowEnvelope (d : ℕ) : ℝ :=
  16 * (Real.exp 1) ^ (2 : ℕ) *
    (momentBoostedLowPowerColorConst (momentBoostedColorEnvelope d)) ^ (2 : ℕ) *
    (momentBoostedPartitionShiftEnvelope d) ^ (2 : ℕ) *
    momentBoostedStreamPointEnvelope d

/-- The common dimension-only constant selected before the model, exponent,
and scales. -/
noncomputable def momentBoostedLargeCubeAllPConst (d : ℕ) : ℝ :=
  max (4 * momentBoostedLargeCubeEnvelope d)
    (max (momentBoostedLowPowerEnvelope d) (momentBoostedLowPowerWindowEnvelope d))

theorem momentBoostedLargeCubeAllPConst_pos (d : ℕ) :
    0 < momentBoostedLargeCubeAllPConst d := by
  unfold momentBoostedLargeCubeAllPConst
  have hhigh : 0 < 4 * momentBoostedLargeCubeEnvelope d :=
    mul_pos (by norm_num) (momentBoostedLargeCubeEnvelope_pos d)
  exact lt_of_lt_of_le hhigh (le_max_left _ _)

private theorem lowPowerWindowEnvelope_nonneg (d : ℕ) :
    0 ≤ momentBoostedLowPowerWindowEnvelope d := by
  unfold momentBoostedLowPowerWindowEnvelope
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (Real.exp_pos 1).le _))
        (pow_nonneg (zero_le_one.trans
          (one_le_momentBoostedLowPowerColorConst
            (one_le_momentBoostedColorEnvelope d))) _))
      (pow_nonneg (zero_le_one.trans
        (one_le_momentBoostedPartitionShiftEnvelope d)) _))
    (momentBoostedStreamPointEnvelope_nonneg d)

private theorem lowPowerEnvelope_le_allPConst (d : ℕ) :
    momentBoostedLowPowerEnvelope d ≤ momentBoostedLargeCubeAllPConst d := by
  unfold momentBoostedLargeCubeAllPConst
  exact le_trans (le_max_left _ _) (le_max_right _ _)

private theorem highPowerEnvelope_le_allPConst (d : ℕ) :
    4 * momentBoostedLargeCubeEnvelope d ≤ momentBoostedLargeCubeAllPConst d := by
  unfold momentBoostedLargeCubeAllPConst
  exact le_max_left _ _

private theorem lowPowerWindowEnvelope_le_allPConst (d : ℕ) :
    momentBoostedLowPowerWindowEnvelope d ≤ momentBoostedLargeCubeAllPConst d := by
  unfold momentBoostedLargeCubeAllPConst
  exact le_trans (le_max_right _ _) (le_max_right _ _)

private theorem momentBoostedStreamPointEnvelope_le_allPConst (d : ℕ) :
    momentBoostedStreamPointEnvelope d ≤ momentBoostedLargeCubeAllPConst d := by
  let L : ℝ := momentBoostedLowPowerColorConst (momentBoostedColorEnvelope d)
  let S : ℝ := momentBoostedPartitionShiftEnvelope d
  let P0 : ℝ := momentBoostedStreamPointEnvelope d
  let W : ℝ := momentBoostedLowPowerWindowEnvelope d
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
  have hfactor : 1 ≤ 16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ) := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have h16 : 1 ≤ (16 : ℝ) := by norm_num
    have hLsq : 1 ≤ L ^ (2 : ℕ) := by nlinarith
    have hSsq : 1 ≤ S ^ (2 : ℕ) := by nlinarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le h16 (by nlinarith [sq_nonneg (Real.exp 1 - 1)]))
        hLsq) hSsq
  have hPW : P0 ≤ W := by
    change P0 ≤ 16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0
    calc
      P0 = 1 * P0 := by ring
      _ ≤ (16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ)) * P0 :=
        mul_le_mul_of_nonneg_right hfactor hP0
      _ = 16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ) * P0 := by ring
  exact hPW.trans (lowPowerWindowEnvelope_le_allPConst d)

/-- The head moment budget for a stream increment on a large cube. -/
def momentBoostedLargeCubeAllPHead
    (M : ABKModel d) (p : ℝ) (n m : ℤ) : ℝ :=
  (momentBoostedLargeCubeAllPConst d * p) ^ (p / 2) *
    (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2)

/-- The head moment budget with the spatial averaging decay factor. -/
def momentBoostedLargeCubeAllPTail
    (M : ABKModel d) (p : ℝ) (l n m : ℤ) : ℝ :=
  momentBoostedLargeCubeAllPHead M p n m *
    (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))

private theorem momentBoostedLargeCubeAllPHead_pos
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    0 < momentBoostedLargeCubeAllPHead M p n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hgamma : 0 < M.gamma⁻¹ := inv_pos.mpr M.shellPrefix.gamma_pos
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  unfold momentBoostedLargeCubeAllPHead
  exact mul_pos
    (Real.rpow_pos_of_pos
      (mul_pos (momentBoostedLargeCubeAllPConst_pos d) hp0) _)
    (Real.rpow_pos_of_pos
      (mul_pos (lt_min hgamma hmn) (Real.rpow_pos_of_pos (by norm_num) _)) _)

private theorem momentBoostedLargeCubeAllPTail_pos
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {l n m : ℤ} (hnm : n < m) :
    0 < momentBoostedLargeCubeAllPTail M p l n m := by
  unfold momentBoostedLargeCubeAllPTail
  exact mul_pos (momentBoostedLargeCubeAllPHead_pos M hp hnm)
    (Real.rpow_pos_of_pos (by norm_num) _)

private theorem streamIncrementLpMassHead_normal_form_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMassHead M p n m =
      ((momentBoostedStreamPointEnvelope d / 2) * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) ^ (p / 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ha : 0 < gammaMomentConst 2 * streamPointScale M n m :=
    mul_pos (gammaMomentConst_pos (by norm_num)) (streamPointScale_pos M hnm)
  have hpoint := streamPointScale_sq M hnm
  unfold streamIncrementLpMassHead
  rw [show gammaMomentConst 2 * streamPointScale M n m * p ^ ((2 : ℝ)⁻¹) =
      (gammaMomentConst 2 * streamPointScale M n m) * p ^ ((2 : ℝ)⁻¹) by ring,
    Real.mul_rpow ha.le (Real.rpow_nonneg hp0.le _)]
  have ha_pow : (gammaMomentConst 2 * streamPointScale M n m) ^ p =
      ((gammaMomentConst 2 * streamPointScale M n m) ^ (2 : ℕ)) ^ (p / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    ring
  have hp_pow : (p ^ ((2 : ℝ)⁻¹)) ^ p = p ^ (p / 2) := by
    rw [← Real.rpow_mul hp0.le]
    congr 1
    ring
  rw [ha_pow, hp_pow, ← Real.mul_rpow (pow_nonneg ha.le 2) hp0.le]
  congr 1
  rw [show (gammaMomentConst 2 * streamPointScale M n m) ^ (2 : ℕ) * p =
      (momentBoostedStreamPointEnvelope d / 2) * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) by
      rw [mul_pow, hpoint, momentBoostedStreamPointEnvelope]
      ring_nf]

private theorem isDeterministicShiftOneSidedOrlicz_mono_shift_and_scale
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {Psi : ℝ → ℝ} {X : Omega → ℝ} {b b' A B : ℝ}
    (h : Probability.IsDeterministicShiftOneSidedOrlicz mu Psi X b A)
    (hbb' : b ≤ b') (hAB : A ≤ B) :
    Probability.IsDeterministicShiftOneSidedOrlicz mu Psi X b' B := by
  have htail := h.2.2.2.mono_scale hAB
  exact ⟨h.1, lt_of_lt_of_le h.2.1 hAB, h.2.2.1,
    htail.of_le (fun omega => by linarith)⟩

private theorem lowPower_partition_head_le_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    (momentBoostedLowPowerEnvelope d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) ≤
      momentBoostedLargeCubeAllPHead M p n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hB : 0 ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hbase : momentBoostedLowPowerEnvelope d * p ≤
      momentBoostedLargeCubeAllPConst d * p :=
    mul_le_mul_of_nonneg_right (lowPowerEnvelope_le_allPConst d) hp0.le
  have hpow := Real.rpow_le_rpow
    (mul_nonneg (momentBoostedLowPowerEnvelope_pos d).le hp0.le) hbase
    (by positivity : 0 ≤ p / 2)
  unfold momentBoostedLargeCubeAllPHead
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hB _)

private theorem lowPower_partition_tail_le_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {l n m : ℤ} (hnm : n < m) :
    momentBoostedLowPowerTargetScale M p l n m ≤
      momentBoostedLargeCubeAllPTail M p l n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hB : 0 ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hbase : momentBoostedLowPowerEnvelope d * p ≤
      momentBoostedLargeCubeAllPConst d * p :=
    mul_le_mul_of_nonneg_right (lowPowerEnvelope_le_allPConst d) hp0.le
  have hpow := Real.rpow_le_rpow
    (mul_nonneg (momentBoostedLowPowerEnvelope_pos d).le hp0.le) hbase
    (by positivity : 0 ≤ p / 2)
  unfold momentBoostedLowPowerTargetScale momentBoostedLargeCubeAllPTail
    momentBoostedLargeCubeAllPHead
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hB _))
    (Real.rpow_nonneg (by norm_num) _)

private theorem lowPower_partition_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : p ≤ 2)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      (momentBoostedLargeCubeAllPHead M p n m)
      (momentBoostedLargeCubeAllPTail M p l n m) := by
  apply isDeterministicShiftOneSidedOrlicz_mono_shift_and_scale
    (isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_lowPower_partition_envelope
      M hp hp_two hnm hsl)
  · exact lowPower_partition_head_le_allP M hp hnm
  · exact lowPower_partition_tail_le_allP M hp hnm

private theorem highPower_head_le_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) :
    streamIncrementLpMassHead M p n m ≤ momentBoostedLargeCubeAllPHead M p n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hB : 0 ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hP0 : 0 ≤ momentBoostedStreamPointEnvelope d :=
    momentBoostedStreamPointEnvelope_nonneg d
  have hhalf : momentBoostedStreamPointEnvelope d / 2 ≤
      momentBoostedLargeCubeAllPConst d := by
    calc
      momentBoostedStreamPointEnvelope d / 2 ≤ momentBoostedStreamPointEnvelope d := by
        nlinarith
      _ ≤ momentBoostedLargeCubeAllPConst d :=
        momentBoostedStreamPointEnvelope_le_allPConst d
  have hbase : (momentBoostedStreamPointEnvelope d / 2) * p *
      (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ≤
      (momentBoostedLargeCubeAllPConst d * p) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hhalf hp0.le) hB
  rw [streamIncrementLpMassHead_normal_form_allP M hp hnm]
  unfold momentBoostedLargeCubeAllPHead
  have hpow := Real.rpow_le_rpow
    (mul_nonneg (mul_nonneg (by positivity) hp0.le) hB) hbase
    (by positivity : 0 ≤ p / 2)
  calc
    (momentBoostedStreamPointEnvelope d / 2 * p *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) ^ (p / 2) ≤
        (momentBoostedLargeCubeAllPConst d * p *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) ^ (p / 2) := hpow
    _ = (momentBoostedLargeCubeAllPConst d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) := by
      rw [show momentBoostedLargeCubeAllPConst d * p *
          (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) =
          (momentBoostedLargeCubeAllPConst d * p) *
            (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) by ring,
        Real.mul_rpow
          (mul_nonneg (momentBoostedLargeCubeAllPConst_pos d).le hp0.le) hB]

private theorem highPower_tail_le_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {l n m : ℤ} (hnm : n < m) :
    momentBoostedLargeCubeTargetScale M p l n m ≤
      momentBoostedLargeCubeAllPTail M p l n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hB : 0 ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hbase : (4 * momentBoostedLargeCubeEnvelope d) * p ≤
      momentBoostedLargeCubeAllPConst d * p :=
    mul_le_mul_of_nonneg_right (highPowerEnvelope_le_allPConst d) hp0.le
  have hpow := Real.rpow_le_rpow
    (mul_nonneg (mul_nonneg (by norm_num) (momentBoostedLargeCubeEnvelope_pos d).le) hp0.le)
    hbase (by positivity : 0 ≤ p / 2)
  unfold momentBoostedLargeCubeTargetScale momentBoostedLargeCubeAllPTail
    momentBoostedLargeCubeAllPHead
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hB _))
    (Real.rpow_nonneg (by norm_num) _)

private theorem highPower_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m) (hml : m ≤ l) :
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      (momentBoostedLargeCubeAllPHead M p n m)
      (momentBoostedLargeCubeAllPTail M p l n m) := by
  apply isDeterministicShiftOneSidedOrlicz_mono_shift_and_scale
    (isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_p_gt_two
      M hp hp_two hnm hml)
  · exact highPower_head_le_allP M hp hnm
  · exact highPower_tail_le_allP M hp hnm

private theorem lowPower_window_gain
    {p : ℝ} (hp : 1 ≤ p) {l m : ℤ} (hml : m ≤ l)
    (hwindow : ¬ m + (incrementPartitionShift d : ℤ) ≤ l) :
    1 ≤ (momentBoostedPartitionShiftEnvelope d) ^ (2 * (p / 2)) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
  let r : ℝ := p / 2
  let S : ℝ := momentBoostedPartitionShiftEnvelope d
  let G : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  have hr : (1 : ℝ) / 2 ≤ r := by dsimp [r]; linarith
  have htwo_r : 1 ≤ 2 * r := by linarith
  have hlt : l < m + (incrementPartitionShift d : ℤ) := lt_of_not_ge hwindow
  have hgap : 0 ≤ (l : ℝ) - (m : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hml)
  have hdiff : (l : ℝ) - (m : ℝ) ≤ (incrementPartitionShift d : ℝ) := by
    have hcast : (l : ℝ) < (m : ℝ) + (incrementPartitionShift d : ℝ) := by
      exact_mod_cast hlt
    linarith
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hExp : 0 ≤ (d : ℝ) * (incrementPartitionShift d : ℝ) * (2 * r) +
      -((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)) := by
    have hdc : 0 ≤ (d : ℝ) * (incrementPartitionShift d : ℝ) := by positivity
    have hmul : (d : ℝ) * (incrementPartitionShift d : ℝ) ≤
        (d : ℝ) * (incrementPartitionShift d : ℝ) * (2 * r) := by
      calc
        (d : ℝ) * (incrementPartitionShift d : ℝ) =
            ((d : ℝ) * (incrementPartitionShift d : ℝ)) * 1 := by ring
        _ ≤ ((d : ℝ) * (incrementPartitionShift d : ℝ)) * (2 * r) :=
          mul_le_mul_of_nonneg_left htwo_r hdc
    have hhalf : ((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)) ≤
        (d : ℝ) * (incrementPartitionShift d : ℝ) := by
      have hleft : ((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)) ≤
          ((d : ℝ) / 2) * (incrementPartitionShift d : ℝ) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
      have hright : ((d : ℝ) / 2) * (incrementPartitionShift d : ℝ) ≤
          (d : ℝ) * (incrementPartitionShift d : ℝ) := by
        have hc : 0 ≤ (incrementPartitionShift d : ℝ) := by positivity
        nlinarith
      exact hleft.trans hright
    linarith
  change 1 ≤ S ^ (2 * r) * G
  dsimp [S, G, momentBoostedPartitionShiftEnvelope]
  rw [← Real.rpow_mul h3.le, ← Real.rpow_add h3]
  rw [← Real.rpow_zero (3 : ℝ)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  simpa only [mul_assoc] using hExp

private theorem lowPower_window_scale_le_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m l : ℤ} (hnm : n < m) (hml : m ≤ l)
    (hwindow : ¬ m + (incrementPartitionShift d : ℤ) ≤ l) :
    streamIncrementLpMassScale M p n m ≤
      momentBoostedLargeCubeAllPTail M p l n m := by
  let r : ℝ := p / 2
  let L : ℝ := momentBoostedLowPowerColorConst (momentBoostedColorEnvelope d)
  let S : ℝ := momentBoostedPartitionShiftEnvelope d
  let P0 : ℝ := momentBoostedStreamPointEnvelope d
  let W : ℝ := momentBoostedLowPowerWindowEnvelope d
  let C : ℝ := momentBoostedLargeCubeAllPConst d
  let B : ℝ := min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))
  let G : ℝ := (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
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
  have hB : 0 ≤ B := by
    dsimp [B]
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact Real.rpow_nonneg (by norm_num) _
  have hgain : 1 ≤ S ^ (2 * r) * G := by
    simpa [r, S, G] using lowPower_window_gain (d := d) hp hml hwindow
  have heone : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hepow : Real.exp 1 ≤ (Real.exp 1) ^ (2 * r) := by
    have htmp := Real.rpow_le_rpow_of_exponent_le heone (by linarith : 1 ≤ 2 * r)
    simpa only [Real.rpow_one] using htmp
  have h16pow : 1 ≤ (16 : ℝ) ^ r :=
    Real.one_le_rpow (by norm_num) hr0
  have hnum : Real.exp 1 ≤ (16 : ℝ) ^ r * (Real.exp 1) ^ (2 * r) := by
    calc
      Real.exp 1 = 1 * Real.exp 1 := by ring
      _ ≤ (16 : ℝ) ^ r * Real.exp 1 :=
        mul_le_mul_of_nonneg_right h16pow (Real.exp_pos 1).le
      _ ≤ (16 : ℝ) ^ r * (Real.exp 1) ^ (2 * r) :=
        mul_le_mul_of_nonneg_left hepow (Real.rpow_nonneg (by norm_num) _)
  have hnum' : Real.exp 1 ≤ (16 * (Real.exp 1) ^ (2 : ℕ)) ^ r := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16)
      (pow_nonneg (Real.exp_pos 1).le _), ← Real.rpow_natCast,
      ← Real.rpow_mul (Real.exp_pos 1).le]
    exact hnum
  have hD : 16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ) ≤
      16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ) := by
    have hLsq : 1 ≤ L ^ (2 : ℕ) := by nlinarith
    have hleft : 0 ≤ 16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ) := by positivity
    calc
      16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ) =
          1 * (16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ)) := by ring
      _ ≤ L ^ (2 : ℕ) * (16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hLsq hleft
      _ = 16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ) := by ring
  have hDpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ 16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ)) hD hr0
  have hsmall : Real.exp 1 ≤
      (16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ)) ^ r * G := by
    have hsplit : (16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ)) ^ r =
        (16 * (Real.exp 1) ^ (2 : ℕ)) ^ r * S ^ (2 * r) := by
      rw [show 16 * (Real.exp 1) ^ (2 : ℕ) * S ^ (2 : ℕ) =
          (16 * (Real.exp 1) ^ (2 : ℕ)) * S ^ (2 : ℕ) by ring,
        Real.mul_rpow (by positivity) (pow_nonneg (zero_le_one.trans hS) _),
        ← Real.rpow_natCast S 2, ← Real.rpow_mul (zero_le_one.trans hS)]
      norm_num
    rw [hsplit]
    calc
      Real.exp 1 = Real.exp 1 * 1 := by ring
      _ ≤ (16 * (Real.exp 1) ^ (2 : ℕ)) ^ r * 1 :=
        mul_le_mul_of_nonneg_right hnum' zero_le_one
      _ ≤ (16 * (Real.exp 1) ^ (2 : ℕ)) ^ r * (S ^ (2 * r) * G) :=
        mul_le_mul_of_nonneg_left hgain (Real.rpow_nonneg (by positivity) _)
      _ = (16 * (Real.exp 1) ^ (2 : ℕ)) ^ r * S ^ (2 * r) * G := by ring
  have hsmallD : Real.exp 1 ≤
      (16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ)) ^ r * G := by
    exact hsmall.trans
      (mul_le_mul_of_nonneg_right hDpow hG)
  have hW : W =
      (16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ)) * P0 := by
    rfl
  have hWsplit : W ^ r =
      (16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ)) ^ r * P0 ^ r := by
    rw [hW, Real.mul_rpow (by positivity) hP0]
  have hWP0 : Real.exp 1 * P0 ^ r ≤ W ^ r * G := by
    rw [hWsplit]
    calc
      Real.exp 1 * P0 ^ r ≤
          ((16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ)) ^ r * G) *
            P0 ^ r :=
        mul_le_mul_of_nonneg_right hsmallD (Real.rpow_nonneg hP0 _)
      _ = (16 * (Real.exp 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * S ^ (2 : ℕ)) ^ r *
          P0 ^ r * G := by ring
  have hWC : W ≤ C := by
    dsimp [W, C]
    exact lowPowerWindowEnvelope_le_allPConst d
  have hCpow : W ^ r ≤ C ^ r :=
    Real.rpow_le_rpow (lowPowerWindowEnvelope_nonneg d) hWC hr0
  have hCP0 : Real.exp 1 * P0 ^ r ≤ C ^ r * G :=
    hWP0.trans (mul_le_mul_of_nonneg_right hCpow hG)
  have hP0half : (P0 / 2) ^ r ≤ P0 ^ r := by
    apply Real.rpow_le_rpow (by positivity) ?_ hr0
    nlinarith
  have hhead : Real.exp 1 * ((P0 / 2) * p * B) ^ r ≤
      (C * p) ^ r * B ^ r * G := by
    have hsplit : ((P0 / 2) * p * B) ^ r =
        (P0 / 2) ^ r * p ^ r * B ^ r := by
      rw [show (P0 / 2) * p * B = (P0 / 2) * (p * B) by ring,
        Real.mul_rpow (by positivity) (mul_nonneg hp0.le hB),
        Real.mul_rpow hp0.le hB]
      ring
    rw [hsplit]
    have hpBr : 0 ≤ p ^ r * B ^ r :=
      mul_nonneg (Real.rpow_nonneg hp0.le _) (Real.rpow_nonneg hB _)
    calc
      Real.exp 1 * ((P0 / 2) ^ r * p ^ r * B ^ r) ≤
          (Real.exp 1 * P0 ^ r) * (p ^ r * B ^ r) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP0half (Real.exp_pos 1).le) hpBr
      _ ≤ (C ^ r * G) * (p ^ r * B ^ r) :=
        mul_le_mul_of_nonneg_right hCP0 hpBr
      _ = (C * p) ^ r * B ^ r * G := by
        rw [Real.mul_rpow (momentBoostedLargeCubeAllPConst_pos d).le hp0.le]
        ring
  rw [streamIncrementLpMassScale_eq_exp_mul_head M hp hnm,
    streamIncrementLpMassHead_normal_form_allP M hp hnm]
  unfold momentBoostedLargeCubeAllPTail momentBoostedLargeCubeAllPHead
  simpa [r, C, B, G, P0] using hhead

private theorem lowPower_window_allP
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p)
    {n m l : ℤ} (hnm : n < m) (hml : m ≤ l)
    (hwindow : ¬ m + (incrementPartitionShift d : ℤ) ≤ l) :
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      (momentBoostedLargeCubeAllPHead M p n m)
      (momentBoostedLargeCubeAllPTail M p l n m) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hraw := isBigOWith_gammaSigma_streamIncrementLpMass M hp hnm l
  have htail := hraw.mono_scale
    (lowPower_window_scale_le_allP M hp hnm hml hwindow)
  refine ⟨Probability.isAdmissibleTail_gammaSigma (by positivity),
    momentBoostedLargeCubeAllPTail_pos M hp hnm,
    measurable_streamIncrementLpMass_for_momentBoosted hp0 l n m, ?_⟩
  exact htail.of_le fun omega => by
    have hhead : 0 ≤ momentBoostedLargeCubeAllPHead M p n m :=
      (momentBoostedLargeCubeAllPHead_pos M hp hnm).le
    linarith

/-- The all-exponent provider behind the frozen large-cube source declaration.
All range and partition cases are discharged internally; the sole displayed
constant depends only on the dimension and is selected before the model and
all scale parameters. -/
theorem stream_increment_lp_large_cube_bound_provider (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (p : ℝ), 1 ≤ p →
        ∀ l m n : ℤ, n < m → m ≤ l →
          Probability.IsDeterministicShiftOneSidedOrlicz
            M.P.toMeasure
            (gammaSigma (2 / p))
            (streamIncrementLpMass p l n m)
            ((C * p) ^ (p / 2) *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2))
            ((C * p) ^ (p / 2) *
              (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
                (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) := by
  refine ⟨momentBoostedLargeCubeAllPConst d, momentBoostedLargeCubeAllPConst_pos d, ?_⟩
  intro M p hp l m n hnm hml
  change Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
    (gammaSigma (2 / p)) (streamIncrementLpMass p l n m)
    (momentBoostedLargeCubeAllPHead M p n m)
    (momentBoostedLargeCubeAllPTail M p l n m)
  by_cases hp_two : p ≤ 2
  · by_cases hsl : m + (incrementPartitionShift d : ℤ) ≤ l
    · exact lowPower_partition_allP M hp hp_two hnm hsl
    · exact lowPower_window_allP M hp hnm hml hsl
  · exact highPower_allP M hp (by linarith) hnm hml

end

end Algsuperdiff.Section3.Provider.Stream
