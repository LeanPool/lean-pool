/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.NumericalConditions

/-!
First and second derivative budgets for the next perturbation.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963.Iteration.InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem next_perturbation_power (s : ℕ) :
    perturbation n δ₁ (s + 1) = (delta δ₁ s : ℝ) ^ (12 * n + 36) := by
  have hh := remainder_eq_next b.delta_pos n s
  change ((delta δ₁ s : ℝ) ^ iterationExponent n) ^ 2 /
    ((delta δ₁ s : ℝ) ^ (2 * stepExponent n) * ((delta δ₁ s : ℝ) ^ 3) ^ 2) = _ at hh
  rw [budget_step_eq (δ := (delta δ₁ s : ℝ)) (b.delta_step_pos s) n] at hh
  exact hh.symm

theorem beta_next_lower (s : ℕ) : (delta δ₁ s : ℝ) ^ 6 ≤ (beta δ₁ (s + 1) : ℝ) := by
  have hd := b.delta_step_pos s
  have hd1 := (b.delta_step_le s).trans b.delta_one.le
  have hh : delta δ₁ s ^ (2 : ℝ) ≤ delta δ₁ s ^ (3 / 2 : ℝ) :=
    NNReal.rpow_le_rpow_of_exponent_ge hd hd1 (by norm_num)
  rw [NNReal.rpow_two] at hh
  have hnext : delta δ₁ s ^ 2 ≤ delta δ₁ (s + 1) := by
    simpa only [delta, decay_succ] using hh
  have hp := pow_le_pow_left₀ (zero_le : (0 : ℝ≥0) ≤ delta δ₁ s ^ 2) hnext 3
  have hh' : delta δ₁ s ^ 6 ≤ beta δ₁ (s + 1) := by
    simpa only [← pow_mul, beta] using hp
  exact_mod_cast hh'

theorem first_derivative_budget (s : ℕ) :
    perturbation n δ₁ (s + 1) / (beta δ₁ s : ℝ) <
      (delta δ₁ s : ℝ) * beta δ₁ (s + 1) := by
  have hd : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hd1 : (delta δ₁ s : ℝ) < 1 := (b.delta_step_le s).trans_lt b.delta_one
  apply (div_lt_iff₀ (show (0 : ℝ) < beta δ₁ s by
    change 0 < (delta δ₁ s : ℝ) ^ 3; positivity)).mpr
  rw [b.next_perturbation_power]
  calc
    (delta δ₁ s : ℝ) ^ (12 * n + 36) < (delta δ₁ s : ℝ) ^ 10 :=
      pow_lt_pow_right_of_lt_one₀ hd hd1 (by omega)
    _ = (delta δ₁ s : ℝ) * (delta δ₁ s : ℝ) ^ 6 * (delta δ₁ s : ℝ) ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (b.beta_next_lower s) hd.le) (by positivity)

theorem second_derivative_budget (s : ℕ) :
    2 * perturbation n δ₁ (s + 1) / (beta δ₁ s : ℝ) ^ 2 < (delta δ₁ s : ℝ) := by
  have hd : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hd4 : (delta δ₁ s : ℝ) < 1 / 4 := (b.delta_step_le s).trans_lt b.delta_quarter
  have hd1 : (delta δ₁ s : ℝ) ≤ 1 := by linarith
  apply (div_lt_iff₀ (show (0 : ℝ) < (beta δ₁ s : ℝ) ^ 2 by
    change 0 < ((delta δ₁ s : ℝ) ^ 3) ^ 2; positivity)).mpr
  rw [b.next_perturbation_power]
  have hp := pow_le_pow_of_le_one hd.le hd1 (show 8 ≤ 12 * n + 36 by omega)
  have hh := mul_lt_mul_of_pos_right (show 2 * (delta δ₁ s : ℝ) < 1 by linarith)
    (pow_pos hd 7)
  change 2 * (delta δ₁ s : ℝ) ^ (12 * n + 36) < (delta δ₁ s : ℝ) *
    ((delta δ₁ s : ℝ) ^ 3) ^ 2
  nlinarith only [hp, hh]

end KamProject.Arnold1963.Iteration.InitialParameters
