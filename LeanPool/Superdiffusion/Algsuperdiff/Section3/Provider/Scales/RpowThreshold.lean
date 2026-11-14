/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform exponential growth as a positive parameter tends to zero

Extracted from scottnarmstrong/Superdiffusion at
7f20476385d4af418f110303085ad0740c9eba46, with shared dependency placement.
-/

@[expose] public section

namespace Algsuperdiff

/-- Every real target lies below `b^(a/γ)` for all sufficiently small positive
`γ`, with any prescribed positive upper cap on the threshold. -/
theorem exists_rpow_inverse_threshold {b a cap C : ℝ} (hb : 1 < b) (ha : 0 < a)
    (hcap : 0 < cap) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ cap ∧
      ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 → C ≤ b ^ (a * gamma⁻¹) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C < b ^ N :=
    ((tendsto_pow_atTop_atTop_of_one_lt (r := b) hb).eventually_gt_atTop C).exists
  refine ⟨min cap (a / ((N : ℝ) + 1)), lt_min hcap (by positivity), min_le_left _ _, ?_⟩
  intro gamma hgamma hle
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hbound : gamma ≤ a / ((N : ℝ) + 1) := hle.trans (min_le_right _ _)
  have hmul : gamma * ((N : ℝ) + 1) ≤ a := (le_div_iff₀ hNpos).mp hbound
  have hscaled := mul_le_mul_of_nonneg_left hmul (inv_pos.mpr hgamma).le
  rw [← mul_assoc, inv_mul_cancel₀ hgamma.ne', one_mul] at hscaled
  have hexp : (N : ℝ) ≤ a * gamma⁻¹ := by
    calc (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
      _ ≤ gamma⁻¹ * a := hscaled
      _ = a * gamma⁻¹ := mul_comm _ _
  refine hN.le.trans ?_
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hb.le hexp

end Algsuperdiff
