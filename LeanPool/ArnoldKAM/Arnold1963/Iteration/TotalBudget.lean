/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.CutoffBudget
public import LeanPool.ArnoldKAM.Arnold1963.Iteration.NumericalConditions
public import LeanPool.ArnoldKAM.Arnold1963.Iteration.ShellSum

/-!
Summable total action-domain loss, including resonance shells and boundary layers.
-/

@[expose] public section
noncomputable section
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration

/-- The frequency-space loss budget combining new resonance shells and geometric erosion. -/
def rawLoss (n : ℕ) (δ₁ Θ₀ : ℝ≥0) (κ : ℝ) (s : ℕ) : ℝ :=
  (κ * (δ₁ : ℝ)) * newShellBudget (previousCutoff n δ₁ s) (cutoff n δ₁ s) +
    (((6 + 7 * upper Θ₀ δ₁ s) * beta δ₁ s : ℝ≥0) : ℝ) * cutoff n δ₁ s ^ n

/-- The coefficient transporting the frequency-space loss budget to real action volume. -/
def actionLossFactor (n : ℕ) (θ₀ Θ₀ : ℝ≥0) (D : ℝ) : ℝ :=
  (2 * (Θ₀ : ℝ) / θ₀) ^ n * resonanceLossConstant n * D

/-- The extended nonnegative action-volume loss budget for one iteration stage. -/
def lossBudget (n : ℕ) (δ₁ θ₀ Θ₀ : ℝ≥0) (κ D : ℝ) (s : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (actionLossFactor n θ₀ Θ₀ D * rawLoss n δ₁ Θ₀ κ s)

namespace InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem tube_budget (s : ℕ) :
    (((6 + 7 * upper Θ₀ δ₁ s) * beta δ₁ s : ℝ≥0) : ℝ) * cutoff n δ₁ s ^ n <
      (delta δ₁ s : ℝ) := by
  have hd : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hD := (threshold5_bounds b.small).2.2.1
  have hh : (δ₁ : ℝ) < 1 / (6 + 14 * (Θ₀ : ℝ)) := (lt_min_iff.mp (lt_min_iff.mp hD).2).1
  have hbase := (lt_div_iff₀ (by positivity : (0 : ℝ) < 6 + 14 * (Θ₀ : ℝ))).mp hh
  have hu := upper_lt_twice (zero_lt_one.trans b.upper_gt_one) b.delta_quarter s
  have hA : (6 + 7 * (upper Θ₀ δ₁ s : ℝ)) * (delta δ₁ s : ℝ) < 1 := by
    have hh' := mul_le_mul_of_nonneg_left
      (show (delta δ₁ s : ℝ) ≤ δ₁ from b.delta_step_le s)
      (show (0 : ℝ) ≤ 6 + 14 * (Θ₀ : ℝ) by positivity)
    have hu' := mul_lt_mul_of_pos_right (show
      6 + 7 * (upper Θ₀ δ₁ s : ℝ) < 6 + 14 * (Θ₀ : ℝ) by linarith) hd
    nlinarith
  have hN := mul_lt_mul_of_pos_left (b.cutoff_budget s) (sq_pos_of_pos hd)
  have hNA := mul_lt_mul_of_pos_left hN
    (show (0 : ℝ) < 6 + 7 * (upper Θ₀ δ₁ s : ℝ) by positivity)
  have hAd := mul_lt_mul_of_pos_right hA hd
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, beta, NNReal.coe_pow]
  nlinarith only [hNA, hAd]

theorem rawLoss_nonneg (s : ℕ) : 0 ≤ rawLoss n δ₁ Θ₀ κ s := by
  unfold rawLoss
  exact add_nonneg (mul_nonneg b.divisor_pos.le (newShellBudget_nonneg _ _))
    (mul_nonneg (NNReal.coe_nonneg _) (pow_nonneg (zero_le_one.trans (b.cutoff_gt_one s).le) n))

theorem rawLoss_le (s : ℕ) : rawLoss n δ₁ Θ₀ κ s ≤
    (κ * (δ₁ : ℝ)) * newShellBudget (previousCutoff n δ₁ s) (cutoff n δ₁ s) +
      (delta δ₁ s : ℝ) := add_le_add le_rfl (b.tube_budget s).le

theorem rawLoss_summable : Summable (rawLoss n δ₁ Θ₀ κ) := by
  apply Summable.of_nonneg_of_le b.rawLoss_nonneg b.rawLoss_le
  exact ((shell_summable (previousCutoff n δ₁) b.previousCutoff_strictMono.monotone rfl).mul_left
    (κ * (δ₁ : ℝ))).add (decay_summable b.delta_quarter.le)

theorem rawLoss_tsum_lt : (∑' s, rawLoss n δ₁ Θ₀ κ s) < 4 * (δ₁ : ℝ) := by
  have hs : Summable (fun s => newShellBudget (previousCutoff n δ₁ s) (cutoff n δ₁ s)) :=
    shell_summable (previousCutoff n δ₁) b.previousCutoff_strictMono.monotone rfl
  have hd : Summable (fun s => (delta δ₁ s : ℝ)) := decay_summable b.delta_quarter.le
  have hle := b.rawLoss_summable.tsum_le_tsum b.rawLoss_le
    ((hs.mul_left (κ * (δ₁ : ℝ))).add hd)
  rw [Summable.tsum_add (hs.mul_left _) hd, tsum_mul_left] at hle
  have hshell := mul_le_mul_of_nonneg_left
    (shell_tsum_le_two (previousCutoff n δ₁) b.previousCutoff_strictMono.monotone rfl)
    b.divisor_pos.le
  have hdelta := decay_tsum_le b.delta_quarter.le
  have hstrict := mul_lt_mul_of_pos_right b.fraction_lt_one
    (show (0 : ℝ) < δ₁ from b.delta_pos)
  change (∑' s, (delta δ₁ s : ℝ)) ≤ 2 * (δ₁ : ℝ) at hdelta
  change (κ * (δ₁ : ℝ)) *
    (∑' s, newShellBudget (previousCutoff n δ₁ s) (cutoff n δ₁ s)) ≤ _ at hshell
  nlinarith only [hle, hshell, hdelta, hstrict]

theorem actionLossFactor_pos : 0 < actionLossFactor n θ₀ Θ₀ D := by
  have hn : (0 : ℝ) < n := by exact_mod_cast b.dimension_pos
  have hθ : (0 : ℝ) < θ₀ := b.lower_pos
  have hΘ : (0 : ℝ) < Θ₀ := zero_lt_one.trans b.upper_gt_one
  unfold actionLossFactor resonanceLossConstant
  positivity [b.type_constant_pos]

theorem initial_measure_budget : 4 * (δ₁ : ℝ) * actionLossFactor n θ₀ Θ₀ D < κ := by
  have hθ : (θ₀ : ℝ) ≠ 0 := ne_of_gt b.lower_pos
  have hΘ : (Θ₀ : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans b.upper_gt_one)
  have hD : D ≠ 0 := b.type_constant_pos.ne'
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast b.dimension_pos.ne'
  have hpow : (4 : ℝ) ^ (n + 2) = 4 * 2 ^ n * 2 ^ (n + 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    simp only [← pow_mul, ← pow_add]
    congr 1
    omega
  have he : ((4 : ℝ) ^ (n + 2))⁻¹ * κ * (θ₀ : ℝ) ^ n /
      ((Θ₀ : ℝ) ^ n * D * n) = κ / (4 * actionLossFactor n θ₀ Θ₀ D) := by
    unfold actionLossFactor resonanceLossConstant
    rw [div_pow, mul_pow, hpow]
    field_simp
  have hs := (lt_min_iff.mp (lt_min_iff.mp (threshold5_bounds b.small).2.2.1).2).2
  rw [he] at hs
  have hh := (lt_div_iff₀ (mul_pos (by norm_num) b.actionLossFactor_pos)).mp hs
  nlinarith only [hh]

theorem total_budget : actionLossFactor n θ₀ Θ₀ D * (∑' s, rawLoss n δ₁ Θ₀ κ s) < κ := by
  have hh := mul_lt_mul_of_pos_left b.rawLoss_tsum_lt b.actionLossFactor_pos
  nlinarith only [hh, b.initial_measure_budget]

theorem lossBudget_tsum_lt : (∑' s, lossBudget n δ₁ θ₀ Θ₀ κ D s) < ENNReal.ofReal κ := by
  unfold lossBudget
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun s => mul_nonneg b.actionLossFactor_pos.le (b.rawLoss_nonneg s))
    (b.rawLoss_summable.mul_left _), tsum_mul_left]
  exact (ENNReal.ofReal_lt_ofReal_iff b.fraction_pos).mpr b.total_budget

end InitialParameters
end KamProject.Arnold1963.Iteration
