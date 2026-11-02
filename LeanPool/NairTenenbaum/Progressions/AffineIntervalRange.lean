/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyAffineReduction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform interval ranges under finitely many affine substitutions -/

@[expose] public section

namespace NairTenenbaum

open Real Filter

theorem exists_affine_interval_range {M : ℕ} (hM : 0 < M) {α : ℝ} (hα : 0 < α) (u₀ : ℝ) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ (M : ℝ) ≤ x₀ ∧ ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x / 2 →
      ∀ a : ℕ, a < M →
        u₀ < (x - a) / M ∧ ((x - a) / M) ^ (α / 2) ≤ y / M ∧
          y / M ≤ (x - a) / M ∧ (x - a) / M ≤ x := by
  have hM₀ : (0 : ℝ) < M := by exact_mod_cast hM
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨z, hz⟩ := eventually_atTop.mp ((tendsto_rpow_atTop (half_pos hα)).eventually
      (eventually_ge_atTop (M : ℝ)))
  let x₀ := max 2 (max z (max (2 * M) (M * u₀ + M)))
  have hx₀M : 2 * (M : ℝ) ≤ x₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right
      _ _))
  refine ⟨x₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), by linarith, ?_⟩
  intro x y hx hy hyx a ha
  have hxpos : 0 < x := by linarith
  have ha' : (a : ℝ) < M := by exact_mod_cast ha
  have hu : 0 ≤ (x - a) / M := div_nonneg (by linarith) hM₀.le
  have hux : (x - a) / M ≤ x := by
    apply (div_le_iff₀ hM₀).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) a]
  have hp : (M : ℝ) ≤ x ^ (α / 2) := hz x
    ((le_max_left _ _).trans ((le_max_right _ _).trans hx.le))
  have hpow : x ^ (α / 2) * x ^ (α / 2) = x ^ α := by
    rw [← Real.rpow_add hxpos, add_halves]
  refine ⟨?_, ?_, ?_, hux⟩
  · apply (lt_div_iff₀ hM₀).mpr
    have HL : (M : ℝ) * u₀ + M < x :=
      (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hx))
    nlinarith
  · apply (le_div_iff₀ hM₀).mpr
    have H₁ := Real.rpow_le_rpow hu hux (half_pos hα).le
    have H₂ : x ^ (α / 2) * M ≤ x ^ α := by
      rw [← hpow]
      exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hxpos.le _)
    exact ((mul_le_mul_of_nonneg_right H₁ hM₀.le).trans H₂).trans hy
  · apply (div_le_div_iff_of_pos_right hM₀).mpr
    linarith

end NairTenenbaum
