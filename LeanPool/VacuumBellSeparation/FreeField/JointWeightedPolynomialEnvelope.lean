/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointWeightedPolynomialBounds

/-!
# Mass-uniform weighted polynomial prefactor

The midpoint radius T=s/2+1 is at most s and at least s/2. These two
inequalities cancel every dimensional polynomial factor against the
actual weighted moment denominators. The reserve exponent is unchanged.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian

theorem joint_midpoint_weighted_ratios {μ s : ℝ} (hμ : 0 < μ) (hs : 2 ≤ s) :
    (jointMidpointMomentRadius s / s) ^ 2 *
        (Real.sqrt (1 + μ * s) / (1 + μ * jointMidpointMomentRadius s) ^ 2) ≤ 2 ∧
      (jointMidpointMomentRadius s / s) ^ 4 *
        ((1 + μ * s) * Real.sqrt (1 + μ * s) /
          (1 + μ * jointMidpointMomentRadius s) ^ 4) ≤ 4 := by
  let T := jointMidpointMomentRadius s
  let d := 1 + μ * T
  let X := 1 + μ * s
  have hs₀ : 0 < s := by linarith
  have hT : 0 < T := jointMidpointMomentRadius_pos hs
  have hd : 1 ≤ d := le_add_of_nonneg_right (mul_nonneg hμ.le hT.le)
  have hd₀ : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hX : 1 ≤ X := le_add_of_nonneg_right (mul_nonneg hμ.le hs₀.le)
  have hX₀ : 0 ≤ X := le_trans zero_le_one hX
  have hTX : X ≤ 2 * d := by
    dsimp only [X, d, T, jointMidpointMomentRadius]
    nlinarith
  have hsqrt : Real.sqrt X ≤ X := Real.sqrt_le_self_iff.mpr (Or.inr hX)
  have hratio₀ : 0 ≤ T / s := by positivity
  have hratio₁ : T / s ≤ 1 := (div_le_one hs₀).mpr (jointMidpointMomentRadius_le hs)
  have hp (n : ℕ) : (T / s) ^ n ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hratio₀ hratio₁ n
  have hsf : Real.sqrt X / d ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (pow_pos hd₀ 2)).mpr
    have hdd : d ≤ d ^ 2 := by nlinarith
    exact hsqrt.trans (hTX.trans (mul_le_mul_of_nonneg_left hdd (by norm_num)))
  have hsg : X * Real.sqrt X / d ^ 4 ≤ 4 := by
    apply (div_le_iff₀ (pow_pos hd₀ 4)).mpr
    calc
      X * Real.sqrt X ≤ X ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsqrt hX₀]
      _ ≤ (2 * d) ^ 2 := pow_le_pow_left₀ hX₀ hTX 2
      _ ≤ 4 * d ^ 4 := by
        have hpow := pow_le_pow_right₀ hd (show 2 ≤ 4 by norm_num)
        nlinarith
  constructor
  · change (T / s) ^ 2 * (Real.sqrt X / d ^ 2) ≤ 2
    calc
      _ ≤ 1 * 2 := mul_le_mul (hp 2) hsf (by positivity) zero_le_one
      _ = _ := by norm_num
  · change (T / s) ^ 4 * (X * Real.sqrt X / d ^ 4) ≤ 4
    calc
      _ ≤ 1 * 4 := mul_le_mul (hp 4) hsg (by positivity) zero_le_one
      _ = _ := by norm_num

theorem jointWeightedPolynomialScale_le {C b μ s : ℝ}
    (hμ : 0 < μ) (hs : 2 ≤ s) :
    jointWeightedPolynomialScale C b μ s ≤
      67072 * C ^ 2 * Real.exp (-μ * s / 2) *
        Real.exp (2 * sourceMomentLambda b * μ * jointMidpointMomentRadius s) := by
  let T := jointMidpointMomentRadius s
  have hs₀ : 0 < s := by linarith
  have hT : 0 < T := jointMidpointMomentRadius_pos hs
  have hd : 0 < 1 + μ * T := by positivity
  have he : Real.exp (sourceMomentLambda b * μ * T) ^ 2 =
      Real.exp (2 * sourceMomentLambda b * μ * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  obtain ⟨hf, hg⟩ := joint_midpoint_weighted_ratios hμ hs
  have hfeq : jointWeightedFieldScale C b μ s ^ 2 * jointFieldEnvelope μ s =
      (6 * C ^ 2 * Real.exp (-μ * s / 2) * Real.exp (2 * sourceMomentLambda b * μ * T)) *
        ((T / s) ^ 2 * (Real.sqrt (1 + μ * s) / (1 + μ * T) ^ 2)) := by
    change (C * T / (1 + μ * T) * Real.exp (sourceMomentLambda b * μ * T)) ^ 2 *
      ((6 / s ^ 2) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s / 2)) = _
    simp only [mul_pow, div_pow, he]
    field_simp [hs₀.ne', hd.ne']
  have hgeq : jointWeightedMomentumScale C b μ s ^ 2 * jointMomentumEnvelope μ s =
      (128 * C ^ 2 * Real.exp (-μ * s / 2) * Real.exp (2 * sourceMomentLambda b * μ * T)) *
        ((T / s) ^ 4 * ((1 + μ * s) * Real.sqrt (1 + μ * s) / (1 + μ * T) ^ 4)) := by
    change (C * T ^ 2 / (1 + μ * T) ^ 2 * Real.exp (sourceMomentLambda b * μ * T)) ^ 2 *
      ((128 / s ^ 4) * (1 + μ * s) * Real.sqrt (1 + μ * s) * Real.exp (-μ * s / 2)) = _
    simp only [mul_pow, div_pow, he]
    field_simp [hs₀.ne', hd.ne']
  have hff := mul_le_mul_of_nonneg_left hf
    (show 0 ≤ 6 * C ^ 2 * Real.exp (-μ * s / 2) *
      Real.exp (2 * sourceMomentLambda b * μ * T) by positivity)
  have hgg := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ 128 * C ^ 2 * Real.exp (-μ * s / 2) *
      Real.exp (2 * sourceMomentLambda b * μ * T) by positivity)
  rw [← hfeq] at hff
  rw [← hgeq] at hgg
  unfold jointWeightedPolynomialScale
  nlinarith

end VacuumBellSeparation
