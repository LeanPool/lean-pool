/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTargetBoxIntegrable

/-!
# Small scale for the Gaussian estimate

A positive time fraction absorbs the normalized lower order term.
-/

public section


noncomputable section

namespace ESS

/-- One time fraction works for all output points in the Gaussian estimate. -/
theorem uc_gaussian_small_scale
    (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 3 / 16 ∧
      ∀ (T t scale : ℝ), 0 < T → T ≤ 1 → 0 < t →
        t ≤ γ * T → scale ^ 2 = 2 * t →
        c₀ * 54 * (c₁ * scale) ^ 2 ≤ 1 / 40 := by
  let A : ℝ := 108 * c₀ * c₁ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 0 < A + 1 := by linarith only [hA]
  let γ : ℝ := min (1 / 8) (1 / (40 * (A + 1)))
  have hγpos : 0 < γ := by dsimp [γ]; positivity
  have hγsmall : γ < 3 / 16 := by
    have hγone : γ ≤ 1 / 8 := min_le_left _ _
    linarith only [hγone]
  have hγbound : γ ≤ 1 / (40 * (A + 1)) := min_le_right _ _
  have hAbound : A * γ ≤ 1 / 40 := by
    calc
      A * γ ≤ A * (1 / (40 * (A + 1))) :=
        mul_le_mul_of_nonneg_left hγbound hA
      _ ≤ (A + 1) * (1 / (40 * (A + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith only [hA]) (by positivity)
      _ = 1 / 40 := by field_simp
  refine ⟨γ, hγpos, hγsmall, ?_⟩
  intro T t scale hT hT1 ht htγ hscaleSq
  have htbound : t ≤ γ := by
    have hmul : γ * T ≤ γ := mul_le_of_le_one_right hγpos.le hT1
    exact htγ.trans hmul
  have hproduct : c₀ * 54 * (c₁ * scale) ^ 2 = A * t := by
    dsimp [A]
    rw [mul_pow, hscaleSq]
    ring
  rw [hproduct]
  exact (mul_le_mul_of_nonneg_left htbound hA).trans hAbound

end ESS
