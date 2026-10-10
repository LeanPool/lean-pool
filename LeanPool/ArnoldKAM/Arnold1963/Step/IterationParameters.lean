/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.NumericalBudget

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963

/-- The positive parameters and smallness inequalities required for an inductive KAM step. -/
structure IterationParameters (n : ℕ) (ρ β δ γ θ Θ : ℝ≥0) (K M : ℝ) : Prop where
  dimension_pos : 0 < n
  beta_pos : 0 < β
  delta_pos : 0 < δ
  lower_pos : 0 < θ
  lower_lt_one : θ < 1
  upper_gt_one : 1 < Θ
  delta_small : (δ : ℝ) < threshold1 n θ Θ
  angle_loss : 10 * (δ : ℝ) < 2 * γ
  angle_width : 3 * (γ : ℝ) < ρ
  width_le_one : ρ ≤ 1
  action_loss : 3 * (β : ℝ) < 2 * δ
  divisor_margin : 2 * (β : ℝ) < K
  divisor_le_one : K ≤ 1
  perturbation_pos : 0 < M
  perturbation_small : M < (δ : ℝ) ^ stepExponent n * K * (β : ℝ) ^ 2
  cutoff_gt_one : 1 < fundamentalCutoff γ (2 * M)

namespace IterationParameters
variable {n : ℕ} {ρ β δ γ θ Θ : ℝ≥0} {K M : ℝ}
  (b : IterationParameters n ρ β δ γ θ Θ K M)
include b

theorem fundamental : FundamentalParameters n ρ β δ γ K (2 * M) (2 * Θ) where
  dimension_pos := b.dimension_pos
  beta_pos := b.beta_pos
  delta_pos := b.delta_pos
  theta_pos := by have : (0 : ℝ) < Θ := lt_trans zero_lt_one b.upper_gt_one; positivity
  delta_small := lt_of_lt_of_le b.delta_small (min_le_left _ _)
  angle_loss := b.angle_loss
  angle_width := by linarith [b.angle_width, γ.coe_nonneg]
  width_le_one := b.width_le_one
  action_loss := b.action_loss
  divisor_margin := b.divisor_margin
  perturbation_pos := by linarith [b.perturbation_pos]
  perturbation_small := by linarith [b.perturbation_small]
  cutoff_gt_one := b.cutoff_gt_one

theorem delta_lt_one : δ < 1 := by
  exact_mod_cast (show (δ : ℝ) < 1 by linarith [b.fundamental.delta_lt])

theorem beta_lt_gamma : β < γ := by
  exact_mod_cast (show (β : ℝ) < γ by linarith [b.action_loss, b.angle_loss, δ.coe_nonneg])

theorem lower_le_upper : θ ≤ Θ := b.lower_lt_one.le.trans b.upper_gt_one.le

theorem mean_gradient_small : M / (β : ℝ) < (β : ℝ) * δ := by
  have hβ : (0 : ℝ) < β := b.beta_pos
  have hd : (δ : ℝ) ≤ 1 := b.delta_lt_one.le
  have hp : (δ : ℝ) ^ stepExponent n ≤ δ := by
    simpa using pow_le_pow_of_le_one δ.coe_nonneg hd (show 1 ≤ stepExponent n by
      unfold stepExponent; omega)
  have hpk : (δ : ℝ) ^ stepExponent n * K ≤ δ :=
    (mul_le_mul_of_nonneg_left b.divisor_le_one (by positivity)).trans (by simpa using hp)
  apply (div_lt_iff₀ hβ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hpk (sq_nonneg (β : ℝ)), b.perturbation_small]

theorem mean_hessian_small : 2 * n * M / (β : ℝ) ^ 2 < (δ : ℝ) * θ := by
  have hβ : (0 : ℝ) < β := b.beta_pos
  have hδ : (0 : ℝ) < δ := b.delta_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast b.dimension_pos
  have hsmall : (δ : ℝ) < (θ : ℝ) / (2 * n) :=
    lt_of_lt_of_le b.delta_small (min_le_right _ _)
  have hdθ : 2 * n * (δ : ℝ) < θ := by
    have hh := (lt_div_iff₀ (show (0 : ℝ) < 2 * n by positivity)).mp hsmall
    nlinarith
  have hp : (δ : ℝ) ^ stepExponent n ≤ (δ : ℝ) ^ 2 :=
    pow_le_pow_of_le_one δ.coe_nonneg b.delta_lt_one.le (by unfold stepExponent; omega)
  have hpk : (δ : ℝ) ^ stepExponent n * K ≤ (δ : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left b.divisor_le_one (by positivity)).trans (by simpa using hp)
  have hM : M / (β : ℝ) ^ 2 < (δ : ℝ) ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hβ)).mpr
      (b.perturbation_small.trans_le (mul_le_mul_of_nonneg_right hpk (sq_nonneg _)))
  calc
    _ = (2 * n : ℝ) * (M / (β : ℝ) ^ 2) := by ring
    _ < (2 * n : ℝ) * (δ : ℝ) ^ 2 := mul_lt_mul_of_pos_left hM (by positivity)
    _ < (δ : ℝ) * θ := by nlinarith [mul_lt_mul_of_pos_right hdθ hδ]

end IterationParameters
end KamProject.Arnold1963
