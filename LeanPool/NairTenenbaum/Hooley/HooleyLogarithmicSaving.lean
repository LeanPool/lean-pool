/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.DivisorSums.DivisorWindowMoments
public import LeanPool.NairTenenbaum.Results.CorollaryFour

/-! # Choosing a Hooley moment that gives logarithmic tail saving -/

@[expose] public section

namespace NairTenenbaum

open Real Filter Polynomial
open scoped Topology

theorem exists_hooley_tail_exponent {η : ℝ} (hη : Real.log 4 - 1 < η) :
    ∃ ε : ℝ, 0 < ε ∧ (2 : ℝ) ^ (1 + ε) - (1 + ε) - 1 - ε * η < 0 := by
  let f (u : ℝ) := (2 : ℝ) ^ u - u - 1 - (u - 1) * η
  have HD : HasDerivAt f (2 * Real.log 2 - 1 - η) 1 := by
    have H := (((HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) (hasDerivAt_id (1 : ℝ))).sub
      (hasDerivAt_id 1)).sub_const 1).sub (((hasDerivAt_id (1 : ℝ)).sub_const 1).mul_const η)
    convert H using 1 <;> simp [f, id_eq, mul_comm]
    rfl
  have hd : 2 * Real.log 2 - 1 - η < 0 := by
    have HE : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [HE] at hη
    linarith
  have H := HD.tendsto_slope_zero_right.eventually (gt_mem_nhds hd)
  obtain ⟨δ, hδ, HH⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp H
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have HR := HH (show δ / 2 ∈ Set.Ioo 0 δ from ⟨half_pos hδ, half_lt_self hδ⟩)
  simp only [Set.mem_ofPred_eq, smul_eq_mul] at HR
  have HF : f 1 = 0 := by norm_num [f]
  rw [HF, sub_zero] at HR
  have HN : f (1 + δ / 2) < 0 := by
    have Hpos := inv_pos.mpr (half_pos hδ)
    nlinarith
  simpa only [f, add_sub_cancel_left] using HN

theorem tendsto_sqrt_mul_log_div_self :
    Tendsto (fun u : ℝ => Real.sqrt (u * Real.log u) / u) atTop (𝓝 0) := by
  have H : Tendsto (fun u : ℝ => 1 / momentOrderScale 1 u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_momentOrderScale (by norm_num))
  apply H.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hs := momentOrderScale_pos (by norm_num : (0 : ℝ) < 1) hu
  have HE := momentOrderScale_sqrt_identity (a := 1) hu
  simp only [one_mul] at HE
  apply (div_eq_div_iff hs.ne' (by linarith : u ≠ 0)).mpr
  simpa only [one_mul, mul_one, mul_comm] using HE.symm

theorem eventually_hooleySubexponential_le_log_rpow (η : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, hooleySubexponential η x ≤ (Real.log x) ^ δ := by
  have H : Tendsto (fun u : ℝ => η * Real.sqrt (u * Real.log u) / u) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using tendsto_sqrt_mul_log_div_self.const_mul η
  have HE : ∀ᶠ u : ℝ in atTop, η * Real.sqrt (u * Real.log u) ≤ δ * u := by
    filter_upwards [H.eventually (gt_mem_nhds hδ), eventually_gt_atTop (0 : ℝ)] with u hu hu₀
    exact ((div_lt_iff₀ hu₀).mp hu).le
  have HL := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually HE
  filter_upwards [HL, eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  rw [hooleySubexponential, Real.rpow_def_of_pos (Real.log_pos hx₁)]
  apply Real.exp_le_exp.mpr
  simpa only [Function.comp_apply, mul_comm] using hx

end NairTenenbaum
