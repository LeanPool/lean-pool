/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Cutoff

/-!
Derive every single-step numerical condition from the initial threshold.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963.Iteration.InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem angle_loss (s : ℕ) : 10 * (delta δ₁ s : ℝ) < 2 * gamma n δ₁ s := by
  have hg0 : (0 : ℝ) < gamma n δ₁ s := b.gamma_step_pos s
  have hg := b.gamma_step_quarter s
  have he : (gamma n δ₁ s : ℝ) ^ (4 * n) = delta δ₁ s := by
    exact_mod_cast gamma_pow b.dimension_pos δ₁ s
  have hn := b.dimension_pos
  have hp : (delta δ₁ s : ℝ) ≤ (gamma n δ₁ s : ℝ) ^ 3 := by
    rw [← he]
    exact pow_le_pow_of_le_one hg0.le (by linarith) (by omega)
  have hs := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hg0.le hg.le (n := 2)) hg0.le
  nlinarith

theorem action_loss (s : ℕ) : 3 * (beta δ₁ s : ℝ) < 2 * delta δ₁ s := by
  have hd0 : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hd : (delta δ₁ s : ℝ) < 1 / 4 := (b.delta_step_le s).trans_lt b.delta_quarter
  have hs := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hd0.le hd.le (n := 2)) hd0.le
  change 3 * (delta δ₁ s : ℝ) ^ 3 < 2 * delta δ₁ s
  nlinarith

theorem delta_lt_fraction : (δ₁ : ℝ) < κ := by
  have h := (threshold5_bounds b.small).2.1
  exact (lt_min_iff.mp (lt_min_iff.mp h).2).2

theorem divisor_pos : 0 < κ * (δ₁ : ℝ) := mul_pos b.fraction_pos b.delta_pos

theorem divisor_le_one : κ * (δ₁ : ℝ) ≤ 1 := by
  have hκ := b.fraction_lt_one
  have hd : (δ₁ : ℝ) < 1 := b.delta_one
  nlinarith [b.fraction_pos, δ₁.coe_nonneg]

theorem delta_sq_lt_divisor (s : ℕ) : (delta δ₁ s : ℝ) ^ 2 < κ * (δ₁ : ℝ) := by
  have hh := mul_lt_mul_of_pos_right b.delta_lt_fraction
    (show (0 : ℝ) < δ₁ from b.delta_pos)
  calc
    (delta δ₁ s : ℝ) ^ 2 ≤ (δ₁ : ℝ) ^ 2 :=
      pow_le_pow_left₀ (delta δ₁ s).coe_nonneg (show (delta δ₁ s : ℝ) ≤ δ₁ from
        b.delta_step_le s) 2
    _ < κ * (δ₁ : ℝ) := by nlinarith only [hh]

theorem divisor_margin (s : ℕ) : 2 * (beta δ₁ s : ℝ) < κ * (δ₁ : ℝ) := by
  have hd0 : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hd : (delta δ₁ s : ℝ) < 1 / 4 := (b.delta_step_le s).trans_lt b.delta_quarter
  have hh := mul_lt_mul_of_pos_right (show 2 * (delta δ₁ s : ℝ) < 1 by linarith)
    (sq_pos_of_pos hd0)
  change 2 * (delta δ₁ s : ℝ) ^ 3 < κ * (δ₁ : ℝ)
  exact (show 2 * (delta δ₁ s : ℝ) ^ 3 < (delta δ₁ s : ℝ) ^ 2 by nlinarith).trans
    (b.delta_sq_lt_divisor s)

theorem perturbation_small (s : ℕ) : perturbation n δ₁ s <
    (delta δ₁ s : ℝ) ^ stepExponent n * (κ * (δ₁ : ℝ)) * (beta δ₁ s : ℝ) ^ 2 := by
  have hd0 : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hd1 : (delta δ₁ s : ℝ) < 1 := (b.delta_step_le s).trans_lt b.delta_one
  have hp : perturbation n δ₁ s < (delta δ₁ s : ℝ) ^ (stepExponent n + 8) :=
    pow_lt_pow_right_of_lt_one₀ hd0 hd1 (by unfold iterationExponent stepExponent; omega)
  apply hp.trans
  have hh := mul_lt_mul_of_pos_left (b.delta_sq_lt_divisor s)
    (show 0 < (delta δ₁ s : ℝ) ^ stepExponent n * (delta δ₁ s : ℝ) ^ 6 by positivity)
  convert hh using 1 <;> simp only [beta, NNReal.coe_pow, pow_add] <;> ring

theorem parameters (s : ℕ) :
    IterationParameters n (width n ρ₀ δ₁ s) (beta δ₁ s) (delta δ₁ s) (gamma n δ₁ s)
      (lower θ₀ δ₁ s) (upper Θ₀ δ₁ s) (κ * (δ₁ : ℝ)) (perturbation n δ₁ s) where
  dimension_pos := b.dimension_pos
  beta_pos := pow_pos (b.delta_step_pos s) 3
  delta_pos := b.delta_step_pos s
  lower_pos := by
    have hh := lower_gt_half b.lower_pos b.delta_quarter s
    have hθ : (0 : ℝ) < θ₀ := b.lower_pos
    exact_mod_cast (show (0 : ℝ) < lower θ₀ δ₁ s by linarith)
  lower_lt_one := (lower_step_le θ₀ δ₁ s).trans_lt b.lower_lt_one
  upper_gt_one := b.upper_gt_one.trans_le (upper_step_ge Θ₀ δ₁ s)
  delta_small := b.delta_threshold s
  angle_loss := b.angle_loss s
  angle_width := (uniform_bounds_of_threshold b.dimension_pos b.lower_pos
    (zero_lt_one.trans b.upper_gt_one) b.small s).2.2.2
  width_le_one := (tsub_le_self : width n ρ₀ δ₁ s ≤ ρ₀).trans b.width_le_one
  action_loss := b.action_loss s
  divisor_margin := b.divisor_margin s
  divisor_le_one := b.divisor_le_one
  perturbation_pos := b.perturbation_step_pos s
  perturbation_small := b.perturbation_small s
  cutoff_gt_one := b.cutoff_gt_one s

end KamProject.Arnold1963.Iteration.InitialParameters
