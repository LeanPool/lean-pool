/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.TotientLogLogBound
public import LeanPool.NairTenenbaum.Hooley.HooleyWeightedMean

/-! # Absorbing reciprocal totients into the Hooley exponential factor -/

@[expose] public section

namespace NairTenenbaum

open Real Filter
open scoped Topology

theorem tendsto_sqrt_mul_log_atTop :
    Tendsto (fun u : ℝ => Real.sqrt (u * Real.log u)) atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with
      u hu hl
  change u ≤ u * Real.log u
  nlinarith

theorem tendsto_log_div_sqrt_mul_log :
    Tendsto (fun u : ℝ => Real.log u / Real.sqrt (u * Real.log u)) atTop (𝓝 0) := by
  have H : Tendsto (fun u : ℝ => 1 / momentOrderScale 1 u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_momentOrderScale (by norm_num))
  apply H.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hs := momentOrderScale_pos (by norm_num : (0 : ℝ) < 1) hu
  have hr := Real.sqrt_pos.mpr (mul_pos (by linarith : 0 < u) (Real.log_pos hu))
  have HE := momentOrderScale_log_identity (a := 1) hu
  simp only [one_mul] at HE
  apply (div_eq_div_iff hs.ne' hr.ne').mpr
  simpa only [one_mul, mul_comm] using HE.symm

theorem eventually_affine_log_le_sqrt_mul_log (A B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop, A + B * Real.log u ≤ ε * Real.sqrt (u * Real.log u) := by
  have HA : Tendsto (fun u : ℝ => A / Real.sqrt (u * Real.log u)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_sqrt_mul_log_atTop
  have HB := tendsto_log_div_sqrt_mul_log.const_mul B
  have H : Tendsto (fun u : ℝ => (A + B * Real.log u) / Real.sqrt (u * Real.log u))
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using HA.add HB
  filter_upwards [H.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)] with u hu hu₁
  have hs := Real.sqrt_pos.mpr (mul_pos (by linarith : 0 < u) (Real.log_pos hu₁))
  exact (div_lt_iff₀ hs).mp hu |>.le

theorem exists_reciprocalTotient_subexponential_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ < x → ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ x →
      (n : ℝ) / n.totient ≤ hooleySubexponential ε x := by
  obtain ⟨A, B, x₁, _, _, hx₁, H⟩ := exists_reciprocalTotient_logLog_bound
  have HE := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_affine_log_le_sqrt_mul_log A B hε)
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp HE
  refine ⟨max x₁ x₂, hx₁.trans_le (le_max_left _ _), fun x hx n hn hnx => ?_⟩
  apply (H x ((le_max_left _ _).trans_lt hx) n hn hnx).trans
  exact Real.exp_le_exp.mpr (hx₂ x ((le_max_right _ _).trans hx.le))

theorem hooleySubexponential_mul (η ε x : ℝ) :
    hooleySubexponential η x * hooleySubexponential ε x = hooleySubexponential (η + ε) x := by
  unfold hooleySubexponential
  rw [← Real.exp_add, ← add_mul]

end NairTenenbaum
