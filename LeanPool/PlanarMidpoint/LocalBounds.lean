/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! Local coefficient bounds with an explicit smallness margin for the BVP estimate. -/

@[expose] public section

open Set Metric
open scoped ContDiff

namespace PlanarMidpoint

theorem local_coefficient_bounds {Ω : Set E} {C : E → Coeff} {p : E}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hC : ContDiffOn ℝ 2 C Ω) :
    ∃ r > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∃ L ≥ (0 : ℝ),
      ball p r ⊆ Ω ∧
      (∀ x ∈ ball p r, ‖C x‖ ≤ M) ∧
      (∀ x ∈ ball p r, ∀ y ∈ ball p r, ‖C x - C y‖ ≤ L * ‖x - y‖) ∧
      8 * L * r ^ 2 + 16 * M * r < 1 / 2 := by
  have hc : ContDiffAt ℝ 1 C p :=
    ((hC p hp).contDiffAt (hΩ.mem_nhds hp)).of_le (by norm_num)
  obtain ⟨L, U, hU, hLip⟩ := hc.exists_lipschitzOnWith
  obtain ⟨e, he, heU⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU (hΩ.mem_nhds hp))
  let M : ℝ := ‖C p‖ + L
  have hM : 0 ≤ M := add_nonneg (norm_nonneg _) L.coe_nonneg
  have hs : 0 < (L : ℝ) + M + 1 := by positivity
  let r := min e (min 1 ((64 * ((L : ℝ) + M + 1))⁻¹))
  have hr : 0 < r := lt_min he (lt_min (by norm_num) (inv_pos.mpr (by positivity)))
  have hre : r ≤ e := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hri : r ≤ (64 * ((L : ℝ) + M + 1))⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ball p r ⊆ U ∩ Ω := fun x hx => heU (ball_subset_ball hre hx)
  refine ⟨r, hr, M, hM, L, L.coe_nonneg, fun x hx => (hsub hx).2, ?_, ?_, ?_⟩
  · intro x hx
    have hpU : p ∈ U := (heU (mem_ball_self he)).1
    have hb := hLip.norm_sub_le (hsub hx).1 hpU
    have hd : ‖x - p‖ ≤ 1 := (mem_ball.mp hx).le.trans hr1
    calc
      ‖C x‖ ≤ ‖C x - C p‖ + ‖C p‖ := norm_le_norm_sub_add _ _
      _ ≤ (L : ℝ) * ‖x - p‖ + ‖C p‖ := add_le_add hb le_rfl
      _ ≤ M := by dsimp [M]; nlinarith [mul_le_mul_of_nonneg_left hd L.coe_nonneg]
  · intro x hx y hy
    exact hLip.norm_sub_le (hsub hx).1 (hsub hy).1
  · have hi : r * (64 * ((L : ℝ) + M + 1)) ≤ 1 := by
      rw [inv_eq_one_div] at hri
      exact (le_div_iff₀ (by positivity)).mp hri
    have hrs : r ^ 2 ≤ r := by nlinarith
    have hLr := mul_le_mul_of_nonneg_left hrs L.coe_nonneg
    have hL0 := mul_nonneg L.coe_nonneg hr.le
    nlinarith

end PlanarMidpoint
