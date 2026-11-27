/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointNormalizedKernels

/-! # The common physical envelope for the two joint polynomial errors -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

/-- Joint common envelope given by `(1 / s ^ 2) * (1 + μ * s) ^ 2 * Real.exp (-μ * s / 2)`. -/
def jointCommonEnvelope (μ s : ℝ) : ℝ :=
  (1 / s ^ 2) * (1 + μ * s) ^ 2 * Real.exp (-μ * s / 2)

theorem jointCommonEnvelope_nonneg (μ s : ℝ) : 0 ≤ jointCommonEnvelope μ s := by
  unfold jointCommonEnvelope
  positivity

theorem jointFieldEnvelope_mass_le {μ s : ℝ} (hμ : 0 < μ) (hs : 1 ≤ s) :
    max 1 μ * jointFieldEnvelope μ s ≤ 6 * jointCommonEnvelope μ s := by
  have hs₀ : 0 < s := by linarith
  have ht : 1 ≤ 1 + μ * s := le_add_of_nonneg_right (mul_nonneg hμ.le hs₀.le)
  have ht₀ : 0 ≤ 1 + μ * s := by positivity
  have hroot : Real.sqrt (1 + μ * s) ≤ 1 + μ * s := by
    nlinarith [Real.sq_sqrt ht₀, Real.sqrt_nonneg (1 + μ * s)]
  have hm : max 1 μ ≤ 1 + μ * s := max_le ht (by nlinarith)
  unfold jointFieldEnvelope jointCommonEnvelope
  calc
    _ = (6 / s ^ 2) * (max 1 μ * Real.sqrt (1 + μ * s)) * Real.exp (-μ * s / 2) := by ring
    _ ≤ (6 / s ^ 2) * ((1 + μ * s) * (1 + μ * s)) * Real.exp (-μ * s / 2) := by gcongr
    _ = _ := by ring

theorem jointMomentumEnvelope_le {μ s : ℝ} (hμ : 0 < μ) (hs : 1 ≤ s) :
    jointMomentumEnvelope μ s ≤ 128 * jointCommonEnvelope μ s := by
  have hs₀ : 0 < s := by linarith
  have ht : 1 ≤ 1 + μ * s := le_add_of_nonneg_right (mul_nonneg hμ.le hs₀.le)
  have ht₀ : 0 ≤ 1 + μ * s := by positivity
  have hroot : Real.sqrt (1 + μ * s) ≤ 1 + μ * s := by
    nlinarith [Real.sq_sqrt ht₀, Real.sqrt_nonneg (1 + μ * s)]
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hpow : s ^ 2 ≤ s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 1)]
  have hden : 128 / s ^ 4 ≤ 128 / s ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
  unfold jointMomentumEnvelope jointCommonEnvelope
  calc
    _ ≤ (128 / s ^ 2) * (1 + μ * s) * (1 + μ * s) * Real.exp (-μ * s / 2) := by gcongr
    _ = _ := by ring

end VacuumBellSeparation
