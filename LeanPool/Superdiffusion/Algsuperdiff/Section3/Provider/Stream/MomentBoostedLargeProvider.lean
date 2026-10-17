/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.MomentBoostedLargeEnvelope
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# MomentBoostedLargeProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal wrapper for the strict `p > 2` large-partition branch

This module packages the fully discharged sharp branch in the exact
one-sided-Orlicz shape used by the frozen large-cube theorem.  Its additional
partition-window and strict-exponent conditions are internal case-split data;
they are discharged by the final all-`p` assembly and do not appear in the
source-facing export.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The target scale combining the large-cube moment budget and spatial decay. -/
noncomputable def momentBoostedLargeCubeTargetScale
    (M : ABKModel d) (p : ℝ) (l n m : ℤ) : ℝ :=
  ((4 * momentBoostedLargeCubeEnvelope d) * p) ^ (p / 2) *
    (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
    (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))

private theorem momentBoostedLargeCubeTargetScale_pos
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {l n m : ℤ} (hnm : n < m) :
    0 < momentBoostedLargeCubeTargetScale M p l n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hgamma : 0 < M.gamma⁻¹ := inv_pos.mpr M.shellPrefix.gamma_pos
  have hmn : 0 < (m : ℝ) - (n : ℝ) := by
    have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  unfold momentBoostedLargeCubeTargetScale
  exact mul_pos
    (mul_pos
      (Real.rpow_pos_of_pos
        (mul_pos (mul_pos (by norm_num) (momentBoostedLargeCubeEnvelope_pos d)) hp0) _)
      (Real.rpow_pos_of_pos
        (mul_pos (lt_min hgamma hmn) (Real.rpow_pos_of_pos (by norm_num) _)) _))
    (Real.rpow_pos_of_pos (by norm_num) _)

private theorem momentBoostedLargeCubeOldScale_le_target
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {l n m : ℤ} (hnm : n < m) :
    (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) ≤
      momentBoostedLargeCubeTargetScale M p l n m := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hE0 : 0 ≤ momentBoostedLargeCubeEnvelope d :=
    (momentBoostedLargeCubeEnvelope_pos d).le
  have hB0 : 0 ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hpow4 : 1 ≤ (4 : ℝ) ^ (p / 2) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hrest : 0 ≤ (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) *
      (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    positivity
  have hscale : ((4 * momentBoostedLargeCubeEnvelope d) * p) ^ (p / 2) =
      (4 : ℝ) ^ (p / 2) * (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) := by
    rw [show (4 * momentBoostedLargeCubeEnvelope d) * p =
      (4 : ℝ) * (momentBoostedLargeCubeEnvelope d * p) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_nonneg hE0 hp0.le)]
  unfold momentBoostedLargeCubeTargetScale
  rw [hscale]
  simpa only [mul_assoc] using le_mul_of_one_le_left hrest hpow4

private theorem four_mul_momentBoostedLargeCubeOldScale_le_target
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {l n m : ℤ} (hnm : n < m) :
    4 * ((momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) *
        (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) ≤
      momentBoostedLargeCubeTargetScale M p l n m := by
  have hp_half : 1 ≤ p / 2 := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hE0 : 0 ≤ momentBoostedLargeCubeEnvelope d :=
    (momentBoostedLargeCubeEnvelope_pos d).le
  have hB0 : 0 ≤ min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
      (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    have hgamma : 0 ≤ M.gamma⁻¹ := (inv_pos.2 M.shellPrefix.gamma_pos).le
    have hmn : 0 ≤ (m : ℝ) - (n : ℝ) := by
      have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
      linarith
    exact mul_nonneg (le_min hgamma hmn) (Real.rpow_nonneg (by norm_num) _)
  have hpow4 : 4 ≤ (4 : ℝ) ^ (p / 2) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hp_half
  have hrest : 0 ≤ (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) *
      (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ))) := by
    positivity
  have hscale : ((4 * momentBoostedLargeCubeEnvelope d) * p) ^ (p / 2) =
      (4 : ℝ) ^ (p / 2) * (momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) := by
    rw [show (4 * momentBoostedLargeCubeEnvelope d) * p =
      (4 : ℝ) * (momentBoostedLargeCubeEnvelope d * p) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_nonneg hE0 hp0.le)]
  unfold momentBoostedLargeCubeTargetScale
  rw [hscale]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpow4 hrest

/-- The genuinely sharp `p > 2` partition branch, already in the exact
one-sided wrapper shape.  `hsl` is an internal partition normalization
condition, not a source premise. -/
theorem isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_p_gt_two_partition
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m)
    (hsl : m + (incrementPartitionShift d : ℤ) ≤ l) :
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      (streamIncrementLpMassHead M p n m)
      (momentBoostedLargeCubeTargetScale M p l n m) := by
  let sigma : ℝ := 2 / p
  let j : ℤ := l - (m + (incrementPartitionShift d : ℤ))
  let q : ℝ :=
    ((descendantsAtScale (originCube d j) 0).image (cubeScaleColor 0)).card
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    positivity
  have hq : 1 ≤ q := by
    have hj : 0 ≤ j := by
      dsimp [j]
      omega
    have hnonempty : ((descendantsAtScale (originCube d j) 0).image
        (cubeScaleColor 0)).Nonempty :=
      (descendantsAtScale_nonempty (originCube d j) hj).image (cubeScaleColor 0)
    dsimp [q]
    exact_mod_cast Nat.succ_le_of_lt hnonempty.card_pos
  have hqQ : q ≤ momentBoostedColorEnvelope d := by
    dsimp [q]
    exact card_used_scaleZero_colors_le_momentBoostedColorEnvelope (d := d) j
  have hraw := isBigOWith_gammaSigma_streamIncrementLpMass_sub_originMean_momentBoosted
    M hp hp_two hnm hsl
  have hscale := momentBoosted_sharp_scale_le_source_shape M hp hp_two hnm hsl hq hqQ
  have hcentered : IsBigOWith M.P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d => streamIncrementLpMass p l n m omega -
        ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
          ∂M.P.toMeasure)
      (momentBoostedLargeCubeTargetScale M p l n m) := by
    refine hraw.mono_scale (hscale.trans ?_)
    simpa [sigma, momentBoostedLargeCubeTargetScale,
      mul_assoc, mul_left_comm, mul_comm] using
      momentBoostedLargeCubeOldScale_le_target M hp hnm (l := l)
  have hmean :
      ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
          ∂M.P.toMeasure ≤ streamIncrementLpMassHead M p n m :=
    integral_streamIncrementLpMass_le_head M hp hnm _
  have htail : IsBigOWith M.P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d =>
        streamIncrementLpMass p l n m omega - streamIncrementLpMassHead M p n m)
      (momentBoostedLargeCubeTargetScale M p l n m) :=
    hcentered.of_le fun omega => by linarith
  refine ⟨Probability.isAdmissibleTail_gammaSigma hsigma,
    momentBoostedLargeCubeTargetScale_pos M hp hnm,
    measurable_streamIncrementLpMass_for_momentBoosted
      (lt_of_lt_of_le zero_lt_one hp) l n m, ?_⟩
  simpa [sigma] using htail

private theorem isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_p_gt_two_window
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m) (hml : m ≤ l)
    (hwindow : ¬ m + (incrementPartitionShift d : ℤ) ≤ l) :
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      (streamIncrementLpMassHead M p n m)
      (momentBoostedLargeCubeTargetScale M p l n m) := by
  let sigma : ℝ := 2 / p
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    positivity
  have hraw := isBigOWith_centered_streamIncrementLpMass_momentBoosted M hp hnm l
  have hsigma_one : sigma ≤ 1 := by
    dsimp [sigma]
    rw [div_le_one hp0]
    linarith
  have hrawGamma := isBigOWith_gammaSigma_of_momentBoostedGammaSigma
    hsigma hsigma_one hraw
  have hscale := momentBoosted_direct_scale_le_source_shape M hp hp_two hnm hml hwindow
  have hcentered : IsBigOWith M.P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d => streamIncrementLpMass p l n m omega -
        ∫ w, streamIncrementLpMass p l n m w ∂M.P.toMeasure)
      (momentBoostedLargeCubeTargetScale M p l n m) := by
    refine hrawGamma.mono_scale ?_
    calc
      4 * streamIncrementLpMomentBoostScale M p n m ≤
          4 * ((momentBoostedLargeCubeEnvelope d * p) ^ (p / 2) *
            (min M.gamma⁻¹ ((m : ℝ) - (n : ℝ)) *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) ^ (p / 2) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l : ℝ) - (m : ℝ)))) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ momentBoostedLargeCubeTargetScale M p l n m := by
        simpa [sigma, momentBoostedLargeCubeTargetScale,
          mul_assoc, mul_left_comm, mul_comm] using
          four_mul_momentBoostedLargeCubeOldScale_le_target M hp hp_two hnm (l := l)
  have hmean : ∫ w, streamIncrementLpMass p l n m w ∂M.P.toMeasure ≤
      streamIncrementLpMassHead M p n m :=
    integral_streamIncrementLpMass_le_head M hp hnm l
  have htail : IsBigOWith M.P.toMeasure (gammaSigma sigma)
      (fun omega : ShellSeq d =>
        streamIncrementLpMass p l n m omega - streamIncrementLpMassHead M p n m)
      (momentBoostedLargeCubeTargetScale M p l n m) :=
    hcentered.of_le fun omega => by linarith
  refine ⟨Probability.isAdmissibleTail_gammaSigma hsigma,
    momentBoostedLargeCubeTargetScale_pos M hp hnm,
    measurable_streamIncrementLpMass_for_momentBoosted
      (lt_of_lt_of_le zero_lt_one hp) l n m, ?_⟩
  simpa [sigma] using htail

/-- The strict-exponent branch with the manuscript's `m ≤ l` source window.
Both internal partition regimes are discharged here. -/
theorem isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_p_gt_two
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) (hp_two : 2 < p)
    {n m l : ℤ} (hnm : n < m) (hml : m ≤ l) :
    Probability.IsDeterministicShiftOneSidedOrlicz M.P.toMeasure
      (gammaSigma (2 / p))
      (streamIncrementLpMass p l n m)
      (streamIncrementLpMassHead M p n m)
      (momentBoostedLargeCubeTargetScale M p l n m) := by
  by_cases hsl : m + (incrementPartitionShift d : ℤ) ≤ l
  · exact isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_p_gt_two_partition
      M hp hp_two hnm hsl
  · exact isDeterministicShiftOneSidedOrlicz_streamIncrementLpMass_p_gt_two_window
      M hp hp_two hnm hml hsl

end

end Algsuperdiff.Section3.Provider.Stream
