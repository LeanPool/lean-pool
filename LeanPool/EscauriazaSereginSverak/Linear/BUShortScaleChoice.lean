/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAbsorption

/-!
# Choosing the short-time parabolic scale

The rescaling parameter is chosen from the fixed Carleman constant and
the lower-order coefficient, while remaining below the Gaussian time
threshold of `lem:bu-gaussian`.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A positive Gaussian time threshold admits a smaller scale that
absorbs the weak differential inequality uniformly over all cutoffs. -/
theorem bu_short_scale_choice
    (c c₁ γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    ∃ γ₁ : ℝ, 0 < γ₁ ∧ γ₁ ≤ γ / 2 ∧
      0 < Real.sqrt (2 * γ₁) ∧ Real.sqrt (2 * γ₁) ≤ 1 ∧
      c * 36 * (c₁ * Real.sqrt (2 * γ₁)) ^ 2 ≤ 1 / 2 := by
  let q : ℝ := 1 / (144 * c * (1 + c₁ ^ 2))
  have hq : 0 < q := by
    dsimp [q]
    positivity
  let γ₁ : ℝ := min (γ / 2) (min (1 / 2) q)
  have hγ₁ : 0 < γ₁ := by
    dsimp [γ₁]
    exact lt_min (by positivity) (lt_min (by norm_num) hq)
  have hγ₁γ : γ₁ ≤ γ / 2 := min_le_left _ _
  have hγ₁half : γ₁ ≤ 1 / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hγ₁q : γ₁ ≤ q :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hscale0 : 0 < 2 * γ₁ := by positivity
  have hscale1 : 2 * γ₁ ≤ 1 := by linarith only [hγ₁half]
  have hsqrtpos : 0 < Real.sqrt (2 * γ₁) := Real.sqrt_pos.mpr hscale0
  have hsqrtle : Real.sqrt (2 * γ₁) ≤ 1 := by
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hscale1]⟩)
  have hsqrtSq : Real.sqrt (2 * γ₁) ^ 2 = 2 * γ₁ :=
    Real.sq_sqrt hscale0.le
  have hden : 0 < 144 * c * (1 + c₁ ^ 2) := by positivity
  have hqmul : 144 * c * (1 + c₁ ^ 2) * γ₁ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hγ₁q hden.le
    dsimp [q] at h
    field_simp at h
    exact h
  have hc₁sq : c₁ ^ 2 ≤ 1 + c₁ ^ 2 := by linarith only []
  have hcoef : 144 * c * c₁ ^ 2 * γ₁ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hc₁sq (by positivity : 0 ≤ 144 * c * γ₁)
    nlinarith only [h, hqmul]
  refine ⟨γ₁, hγ₁, hγ₁γ, hsqrtpos, hsqrtle, ?_⟩
  rw [mul_pow, hsqrtSq]
  nlinarith only [hcoef]

end ESS
