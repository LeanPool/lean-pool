/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.UniformBounds
public import LeanPool.ArnoldKAM.Arnold1963.Step.IterationParameters

/-!
Initial numerical hypotheses and their consequences at every iteration stage.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963.Iteration

/-- Positive initial parameters satisfying every smallness and measure-budget constraint. -/
structure InitialParameters (n : ℕ) (δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0) (κ D : ℝ) : Prop where
  dimension_pos : 0 < n
  delta_pos : 0 < δ₁
  lower_pos : 0 < θ₀
  lower_lt_one : θ₀ < 1
  upper_gt_one : 1 < Θ₀
  width_pos : 0 < ρ₀
  width_le_one : ρ₀ ≤ 1
  fraction_pos : 0 < κ
  fraction_lt_one : κ < 1
  type_constant_pos : 0 < D
  small : (δ₁ : ℝ) < threshold5 n θ₀ Θ₀ ρ₀ κ D

theorem threshold1_mono {n : ℕ} {θ θ' Θ Θ' : ℝ}
    (hθ : θ ≤ θ') (hΘ : 0 < Θ') (hΘΘ : Θ' ≤ Θ) :
    threshold1 n θ Θ ≤ threshold1 n θ' Θ' := by
  have hi : (2 * Θ)⁻¹ ≤ (2 * Θ')⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have hL : 0 ≤ (constantL3 n)⁻¹ := by unfold constantL3 constantL5 constantL0; positivity
  apply min_le_min _ (div_le_div_of_nonneg_right hθ (by positivity))
  unfold threshold0
  exact min_le_min le_rfl (min_le_min le_rfl
    (min_le_min (mul_le_mul_of_nonneg_left hi hL) le_rfl))

namespace InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem delta_quarter : δ₁ < 1 / 4 := delta_initial_lt_quarter b.small

theorem delta_one : δ₁ < 1 := by
  have h : (δ₁ : ℝ) < 1 / 4 := b.delta_quarter
  exact_mod_cast (show (δ₁ : ℝ) < 1 by linarith)

theorem delta_step_pos (s : ℕ) : 0 < delta δ₁ s := decay_pos b.delta_pos s

theorem delta_step_le (s : ℕ) : delta δ₁ s ≤ δ₁ := decay_le b.delta_one.le s

theorem gamma_step_pos (s : ℕ) : 0 < gamma n δ₁ s := by
  rw [gamma_eq]
  exact NNReal.rpow_pos (b.delta_step_pos s)

theorem gamma_step_le (s : ℕ) : gamma n δ₁ s ≤ gamma n δ₁ 0 := by
  obtain ⟨_, hγ⟩ := gamma_initial_bounds b.dimension_pos (threshold5_bounds b.small).2.1
  have h1 : δ₁ ^ (1 / (4 * (n : ℝ))) ≤ 1 := by
    have : (gamma n δ₁ 0 : ℝ) ≤ 1 := by linarith
    simp only [gamma, decay_zero] at this
    exact_mod_cast this
  simpa only [gamma, decay_zero] using decay_le h1 s

theorem gamma_step_quarter (s : ℕ) : (gamma n δ₁ s : ℝ) < 1 / 4 :=
  (show (gamma n δ₁ s : ℝ) ≤ gamma n δ₁ 0 from b.gamma_step_le s).trans_lt
    (gamma_initial_bounds b.dimension_pos (threshold5_bounds b.small).2.1).2

omit b in
theorem lower_step_le (θ₀ δ₁ : ℝ≥0) (s : ℕ) : lower θ₀ δ₁ s ≤ θ₀ := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [lower_succ]
    exact (mul_le_mul_of_nonneg_left (tsub_le_self : 1 - delta δ₁ s ≤ 1)
      (zero_le : 0 ≤ lower θ₀ δ₁ s)).trans (by simpa using ih)

omit b in
theorem upper_step_ge (Θ₀ δ₁ : ℝ≥0) (s : ℕ) : Θ₀ ≤ upper Θ₀ δ₁ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [upper_succ]
    apply ih.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (zero_le : 0 ≤ delta δ₁ s) : 1 ≤ 1 + delta δ₁ s)
      (zero_le : 0 ≤ upper Θ₀ δ₁ s)

theorem delta_threshold (s : ℕ) :
    (delta δ₁ s : ℝ) < threshold1 n (lower θ₀ δ₁ s) (upper Θ₀ δ₁ s) := by
  obtain ⟨hl, hu, _, _⟩ := uniform_bounds_of_threshold b.dimension_pos b.lower_pos
    (zero_lt_one.trans b.upper_gt_one) b.small s
  exact ((show (delta δ₁ s : ℝ) ≤ δ₁ from b.delta_step_le s).trans_lt
    (threshold5_bounds b.small).1).trans_le
    (threshold1_mono hl.le (by
      have hh := b.upper_gt_one.trans_le (upper_step_ge Θ₀ δ₁ s)
      exact_mod_cast (zero_lt_one.trans hh)) hu.le)

theorem delta_strictAnti : StrictAnti (delta δ₁) := by
  apply strictAnti_nat_of_succ_lt
  intro s
  have hh := decay_half b.delta_quarter.le s
  have hp : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  exact_mod_cast (show (delta δ₁ (s + 1) : ℝ) < delta δ₁ s by
    change (delta δ₁ (s + 1) : ℝ) ≤ (delta δ₁ s : ℝ) / 2 at hh
    linarith)

end InitialParameters
end KamProject.Arnold1963.Iteration
