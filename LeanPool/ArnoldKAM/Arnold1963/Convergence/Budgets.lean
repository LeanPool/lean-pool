/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.InitialParameters

/-!
Summable weighted transformation increments and separate unweighted frequency tails.
-/

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem beta_eighth (s : ℕ) : (beta δ₁ (s + 1) : ℝ) ≤ (beta δ₁ s : ℝ) / 8 := by
  have hh := pow_le_pow_left₀ (delta δ₁ (s + 1)).coe_nonneg (decay_half b.delta_quarter.le s) 3
  change (delta δ₁ (s + 1) : ℝ) ^ 3 ≤ (delta δ₁ s : ℝ) ^ 3 / 8
  change (delta δ₁ (s + 1) : ℝ) ^ 3 ≤ ((delta δ₁ s : ℝ) / 2) ^ 3 at hh
  nlinarith

theorem beta_geometric (s j : ℕ) :
    (beta δ₁ (j + s) : ℝ) ≤ (beta δ₁ s : ℝ) * (1 / 8 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hh := b.beta_eighth (j + s)
    rw [show j + 1 + s = (j + s) + 1 by omega, pow_succ]
    nlinarith

theorem beta_summable : Summable (fun s => (beta δ₁ s : ℝ)) :=
  Summable.of_nonneg_of_le (fun s => (beta δ₁ s).coe_nonneg)
    (by simpa using b.beta_geometric 0)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num)).mul_left (beta δ₁ 0 : ℝ))

theorem beta_tail_le (s : ℕ) : (∑' j, (beta δ₁ (j + s) : ℝ)) ≤ 8 / 7 * (beta δ₁ s : ℝ) := by
  calc
    _ ≤ ∑' j, (beta δ₁ s : ℝ) * (1 / 8 : ℝ) ^ j :=
      ((summable_nat_add_iff s).mpr b.beta_summable).tsum_le_tsum (b.beta_geometric s)
        ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
          (by norm_num)).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

theorem weighted_beta_bound (s : ℕ) :
    (2 : ℝ) ^ s * beta δ₁ s ≤ (beta δ₁ 0 : ℝ) * (1 / 4 : ℝ) ^ s := by
  have hh := mul_le_mul_of_nonneg_left (b.beta_geometric 0 s) (by positivity : (0 : ℝ) ≤ 2 ^ s)
  simpa only [Nat.add_zero, ← mul_assoc, mul_comm ((2 : ℝ) ^ s), mul_assoc, ← mul_pow,
    show (1 / 8 : ℝ) * 2 = 1 / 4 by norm_num] using hh

theorem weighted_beta_summable : Summable (fun s => (2 : ℝ) ^ s * beta δ₁ s) :=
  Summable.of_nonneg_of_le (fun s => by positivity) b.weighted_beta_bound
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).mul_left (beta δ₁ 0 : ℝ))

theorem weighted_beta_tsum_lt : (∑' s, (2 : ℝ) ^ s * beta δ₁ s) < 2 * (beta δ₁ 0 : ℝ) := by
  have hh := b.weighted_beta_summable.tsum_le_tsum b.weighted_beta_bound
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).mul_left (beta δ₁ 0 : ℝ))
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hh
  have hp : (0 : ℝ) < beta δ₁ 0 := pow_pos (b.delta_step_pos 0) 3
  norm_num at hh
  nlinarith

theorem weighted_beta_tendsto_zero :
    Tendsto (fun s => (2 : ℝ) ^ s * beta δ₁ s) atTop (𝓝 0) :=
  b.weighted_beta_summable.tendsto_atTop_zero

theorem frequency_budget_summable :
    Summable (fun s => (beta δ₁ s : ℝ) * delta δ₁ s) := by
  apply Summable.of_nonneg_of_le (fun s => by positivity) _ b.beta_summable
  intro s
  exact mul_le_of_le_one_right (beta δ₁ s).coe_nonneg ((b.delta_step_le s).trans b.delta_one.le)

theorem frequency_tail_lt (s : ℕ) :
    (∑' j, (beta δ₁ (j + s) : ℝ) * delta δ₁ (j + s)) < (beta δ₁ s : ℝ) / 2 := by
  have hh := ((summable_nat_add_iff s).mpr b.frequency_budget_summable).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left
      (show (delta δ₁ (j + s) : ℝ) ≤ 1 / 4 from
        ((b.delta_step_le _).trans b.delta_quarter.le)) (beta δ₁ _).coe_nonneg)
    (((summable_nat_add_iff s).mpr b.beta_summable).mul_right (1 / 4 : ℝ))
  rw [tsum_mul_right] at hh
  have ht := b.beta_tail_le s
  have hp : (0 : ℝ) < beta δ₁ s := pow_pos (b.delta_step_pos s) 3
  nlinarith

end KamProject.Arnold1963.Iteration.InitialParameters
