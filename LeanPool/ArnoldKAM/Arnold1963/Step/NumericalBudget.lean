/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.HomologicalBound

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963

/-- The logarithmic Fourier cutoff balancing strip loss and perturbation size. -/
def fundamentalCutoff (γ M : ℝ) : ℝ := Real.log (1 / M) / γ

/-- The strict quadratic remainder target used in the fundamental step. -/
def fundamentalRemainderBound (n : ℕ) (M δ β : ℝ) : ℝ :=
  (1 / 4 : ℝ) * M ^ 2 / (δ ^ (2 * stepExponent n) * β ^ 2)

theorem fundamentalRemainderBound_twice (n : ℕ) (M δ β : ℝ) :
    fundamentalRemainderBound n (2 * M) δ β =
      M ^ 2 / (δ ^ (2 * stepExponent n) * β ^ 2) :=
  strengthened_budget_two_mul M δ β n

/-- The positive parameters and numerical constraints required by the fundamental step. -/
structure FundamentalParameters (n : ℕ) (ρ β δ γ : ℝ≥0) (K M Θ : ℝ) : Prop where
  dimension_pos : 0 < n
  beta_pos : 0 < β
  delta_pos : 0 < δ
  theta_pos : 0 < Θ
  delta_small : (δ : ℝ) < threshold0 n Θ
  angle_loss : 10 * (δ : ℝ) < 2 * γ
  angle_width : 2 * (γ : ℝ) < ρ
  width_le_one : ρ ≤ 1
  action_loss : 3 * (β : ℝ) < 2 * δ
  divisor_margin : 2 * (β : ℝ) < K
  perturbation_pos : 0 < M
  perturbation_small : M < 2 * (δ : ℝ) ^ stepExponent n * K * (β : ℝ) ^ 2
  cutoff_gt_one : 1 < fundamentalCutoff γ M

namespace FundamentalParameters
variable {n : ℕ} {ρ β δ γ : ℝ≥0} {K M Θ : ℝ}
  (b : FundamentalParameters n ρ β δ γ K M Θ)
include b

theorem gamma_pos : 0 < γ := by
  have hd : (0 : ℝ) < δ := b.delta_pos
  exact_mod_cast (show (0 : ℝ) < γ by linarith [b.angle_loss])

theorem K_pos : 0 < K := by
  have hb : (0 : ℝ) < β := b.beta_pos
  linarith [b.divisor_margin]

theorem delta_lt : (δ : ℝ) < 1 / 12 := (threshold0_bounds b.delta_small).1

theorem double_delta_le : δ + δ ≤ ρ := by
  have hd := δ.coe_nonneg
  have h1 := b.angle_loss
  have h2 := b.angle_width
  exact_mod_cast (show (δ : ℝ) + δ ≤ ρ by linarith)

theorem exp_cutoff : Real.exp (-(fundamentalCutoff γ M) * γ) = M := by
  have hγ : (γ : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < γ from b.gamma_pos)
  rw [fundamentalCutoff, neg_mul, div_mul_cancel₀ _ hγ,
    Real.exp_neg, Real.exp_log (div_pos zero_lt_one b.perturbation_pos)]
  simp

theorem generating_bound_lt : homologicalBound n M K δ <
    2 * constantL5 n * (δ : ℝ) ^ 2 * (β : ℝ) ^ 2 := by
  have hL := constantL5_pos n
  apply (div_lt_iff₀ (mul_pos b.K_pos (pow_pos (show (0 : ℝ) < δ from b.delta_pos) _))).2
  have hh := mul_lt_mul_of_pos_right b.perturbation_small hL
  convert hh using 1
  dsimp [stepExponent, homologicalExponent]
  simp only [pow_add, pow_mul]
  ring

theorem generating_small : homologicalBound n M K δ < (β : ℝ) ^ 2 / (16 * n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast b.dimension_pos
  have hδ : (0 : ℝ) < δ := b.delta_pos
  have hβ : (0 : ℝ) < β := b.beta_pos
  have hb := (threshold0_budget_conditions b.dimension_pos b.theta_pos b.delta_small).2.1
  apply (lt_div_iff₀ (show (0 : ℝ) < 16 * n by positivity)).2
  calc
    _ < (2 * constantL5 n * (δ : ℝ) ^ 2 * (β : ℝ) ^ 2) * (16 * n) :=
      mul_lt_mul_of_pos_right b.generating_bound_lt (by positivity)
    _ = ((δ : ℝ) * constantL2 n) * (2 * δ * (β : ℝ) ^ 2) := by unfold constantL2; ring
    _ < 2 * δ * (β : ℝ) ^ 2 := by
      simpa using mul_lt_mul_of_pos_right hb (show 0 < 2 * (δ : ℝ) * (β : ℝ) ^ 2 by positivity)
    _ < (β : ℝ) ^ 2 := by nlinarith [b.delta_lt, sq_pos_of_pos hβ]

theorem generating_lt_beta_sq : homologicalBound n M K δ < (β : ℝ) ^ 2 := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast b.dimension_pos
  exact b.generating_small.trans_le (div_le_self (sq_nonneg _) (by nlinarith))

theorem displacement_lt_beta : homologicalBound n M K δ / β < β := by
  apply (div_lt_iff₀ (show (0 : ℝ) < β from b.beta_pos)).2
  simpa only [pow_two] using b.generating_lt_beta_sq

theorem remainder_budget :
    (1 / 2 : ℝ) * n ^ 2 * Θ * (homologicalBound n M K δ / δ) ^ 2 +
      (((2 * n : ℝ) / Real.exp 1) ^ n * M ^ 2 / (δ : ℝ) ^ (n + 1)) +
      (n * M / β) * (homologicalBound n M K δ / δ) <
        fundamentalRemainderBound n M δ β := by
  have hδ : (0 : ℝ) < δ := b.delta_pos
  have hβ : (0 : ℝ) < β := b.beta_pos
  have hK := b.K_pos
  have hM := b.perturbation_pos
  have hΘ := b.theta_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast b.dimension_pos
  have hδ1 : (δ : ℝ) ≤ 1 := by linarith [b.delta_lt]
  have hβ1 : (β : ℝ) ≤ 1 := by linarith [b.action_loss, b.delta_lt]
  have hr : (β : ℝ) / K ≤ 1 / 2 := (div_le_iff₀ hK).2 (by linarith [b.divisor_margin])
  have hr0 : 0 ≤ (β : ℝ) / K := by positivity
  have hr2 : ((β : ℝ) / K) ^ 2 ≤ 1 / 4 := by nlinarith
  obtain ⟨_, hL2, hL3, hL4⟩ :=
    threshold0_budget_conditions b.dimension_pos b.theta_pos b.delta_small
  have hL5 : (δ : ℝ) * n * constantL5 n ≤ 1 := by
    dsimp [constantL2] at hL2
    linarith only [hL2]
  have htail : (δ : ℝ) * (((2 * n : ℝ) / Real.exp 1) ^ n) ≤ 1 := by
    dsimp [constantL4] at hL4
    linarith only [hL4]
  have hp3 : (δ : ℝ) ^ (3 * n + 4) ≤ (δ : ℝ) ^ 2 :=
    pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have hp4 : (δ : ℝ) ^ (2 * n + 3) ≤ (δ : ℝ) ^ 2 :=
    pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  let R := M ^ 2 / ((δ : ℝ) ^ (2 * stepExponent n) * (β : ℝ) ^ 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have h2 : (1 / 2 : ℝ) * n ^ 2 * Θ * (homologicalBound n M K δ / δ) ^ 2 =
      R * (((δ : ℝ) * (constantL3 n * Θ)) * ((β : ℝ) / K) ^ 2 * δ) := by
    dsimp [R, homologicalBound, homologicalExponent, stepExponent, constantL3]
    simp only [pow_add, pow_mul']
    field_simp
  have h3 : (((2 * n : ℝ) / Real.exp 1) ^ n * M ^ 2 / (δ : ℝ) ^ (n + 1)) =
      R * (((δ : ℝ) * (((2 * n : ℝ) / Real.exp 1) ^ n)) *
        (β : ℝ) ^ 2 * (δ : ℝ) ^ (3 * n + 4)) := by
    dsimp [R, stepExponent]
    simp only [pow_add, pow_mul']
    field_simp
  have h4 : (n * M / β) * (homologicalBound n M K δ / δ) =
      R * (((δ : ℝ) * n * constantL5 n) * ((β : ℝ) / K) * (δ : ℝ) ^ (2 * n + 3)) := by
    dsimp [R, homologicalBound, homologicalExponent, stepExponent]
    simp only [pow_add, pow_mul']
    field_simp
  have hb2 : ((δ : ℝ) * (constantL3 n * Θ)) * ((β : ℝ) / K) ^ 2 * δ ≤ (δ : ℝ) / 4 := by
    have hh := mul_le_mul hL3.le hr2 (sq_nonneg _) zero_le_one
    have := mul_le_mul_of_nonneg_right hh hδ.le
    linarith only [this]
  have hb3 : ((δ : ℝ) * (((2 * n : ℝ) / Real.exp 1) ^ n)) *
      (β : ℝ) ^ 2 * (δ : ℝ) ^ (3 * n + 4) ≤ (δ : ℝ) ^ 2 := by
    have hβ2 : (β : ℝ) ^ 2 ≤ 1 := by nlinarith only [hβ, hβ1]
    have hprod := mul_le_mul htail hβ2 (sq_nonneg _) zero_le_one
    have hh := mul_le_mul hprod hp3 (by positivity) (by norm_num : (0 : ℝ) ≤ 1 * 1)
    simpa using hh
  have hb4 : ((δ : ℝ) * n * constantL5 n) * ((β : ℝ) / K) *
      (δ : ℝ) ^ (2 * n + 3) ≤ (1 / 2 : ℝ) * (δ : ℝ) ^ 2 := by
    have hprod := mul_le_mul hL5 hr hr0 zero_le_one
    have hh := mul_le_mul hprod hp4 (by positivity) (by norm_num : (0 : ℝ) ≤ 1 * (1 / 2))
    simpa using hh
  rw [h2, h3, h4]
  calc
    _ ≤ R * ((δ : ℝ) / 4 + (δ : ℝ) ^ 2 + 1 / 2 * (δ : ℝ) ^ 2) := by
      have hA := mul_le_mul_of_nonneg_left hb2 hR.le
      have hB := mul_le_mul_of_nonneg_left hb3 hR.le
      have hC := mul_le_mul_of_nonneg_left hb4 hR.le
      linarith only [hA, hB, hC]
    _ < R * (1 / 4) := by
      apply mul_lt_mul_of_pos_left _ hR
      nlinarith only [b.delta_lt, hδ]
    _ = fundamentalRemainderBound n M δ β := by dsimp [R, fundamentalRemainderBound]; ring

end FundamentalParameters
end KamProject.Arnold1963
