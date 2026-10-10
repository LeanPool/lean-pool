/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Cutoff

/-!
Uniform estimates for cutoff growth relative to decay of the small parameter.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963.Iteration

/-- The dimension-dependent coefficient used to bound the iteration's Fourier cutoffs. -/
def cutoffConstant (n : ℕ) : ℝ := 4 * n * (iterationExponent n + 1) / Real.exp 1

namespace InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem cutoff_bound (s : ℕ) :
    cutoff n δ₁ s < cutoffConstant n / (gamma n δ₁ s : ℝ) ^ 2 := by
  have hd : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hd1 : (delta δ₁ s : ℝ) < 1 := (b.delta_step_le s).trans_lt b.delta_one
  have hg : (0 : ℝ) < gamma n δ₁ s := b.gamma_step_pos s
  have hn : (0 : ℝ) < n := by exact_mod_cast b.dimension_pos
  have hL : 0 < Real.log (1 / (delta δ₁ s : ℝ)) :=
    Real.log_pos ((one_lt_div hd).mpr hd1)
  rw [one_div, Real.log_inv] at hL
  have hnum : Real.log (1 / (2 * perturbation n δ₁ s)) <
      (iterationExponent n + 1 : ℝ) * Real.log (1 / (delta δ₁ s : ℝ)) := by
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    simp only [perturbation, one_div, Real.log_inv,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hd.ne'), Real.log_pow]
    nlinarith
  have hlog : Real.log (1 / (delta δ₁ s : ℝ)) ≤ (4 * n / Real.exp 1) /
      (gamma n δ₁ s : ℝ) := by
    have hh := log_inv_le_rpow hd (show (0 : ℝ) < 4 * n by positivity)
    simpa only [gamma_eq, NNReal.coe_rpow, Real.rpow_neg hd.le, div_eq_mul_inv] using hh
  calc
    cutoff n δ₁ s <
        ((iterationExponent n + 1 : ℝ) * Real.log (1 / (delta δ₁ s : ℝ))) /
          (gamma n δ₁ s : ℝ) := div_lt_div_of_pos_right hnum hg
    _ ≤ ((iterationExponent n + 1 : ℝ) * ((4 * n / Real.exp 1) /
          (gamma n δ₁ s : ℝ))) / (gamma n δ₁ s : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hg.le
    _ = _ := by unfold cutoffConstant; ring

theorem delta_cutoffConstant_small (s : ℕ) :
    (delta δ₁ s : ℝ) * cutoffConstant n ^ (2 * n) < 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast b.dimension_pos
  have hden : 0 < (32 * (n : ℝ) ^ 2 + 100 * n) ^ (2 * n) := by positivity
  have hd := ((show (delta δ₁ s : ℝ) ≤ δ₁ from b.delta_step_le s).trans_lt
    (threshold5_bounds b.small).2.2.1).trans_le (min_le_left _ _)
  change (delta δ₁ s : ℝ) < Real.exp (2 * n) /
    (32 * (n : ℝ) ^ 2 + 100 * n) ^ (2 * n) at hd
  have he : Real.exp (2 * (n : ℝ)) = Real.exp 1 ^ (2 * n) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 (2 * n)
  rw [he] at hd
  have hh := (lt_div_iff₀ hden).mp hd
  have hc : cutoffConstant n = (32 * (n : ℝ) ^ 2 + 100 * n) / Real.exp 1 := by
    unfold cutoffConstant iterationExponent
    push_cast
    ring
  rw [hc, div_pow, ← mul_div_assoc]
  exact (div_lt_one (by positivity)).mpr hh

theorem cutoff_budget (s : ℕ) : (delta δ₁ s : ℝ) * cutoff n δ₁ s ^ n < 1 := by
  have hg : (0 : ℝ) < gamma n δ₁ s := b.gamma_step_pos s
  have hd : (0 : ℝ) < delta δ₁ s := b.delta_step_pos s
  have hn := b.dimension_pos
  have hN : 0 < cutoff n δ₁ s := zero_lt_one.trans (b.cutoff_gt_one s)
  have hc : 0 < cutoffConstant n := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    unfold cutoffConstant
    positivity
  have hp : (gamma n δ₁ s : ℝ) ^ (4 * n) = delta δ₁ s := by
    exact_mod_cast gamma_pow hn δ₁ s
  have hbound := mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ (b.cutoff_bound s) hN.le hn.ne') hd
  have he : (delta δ₁ s : ℝ) *
      (cutoffConstant n / (gamma n δ₁ s : ℝ) ^ 2) ^ n =
        (gamma n δ₁ s : ℝ) ^ (2 * n) * cutoffConstant n ^ n := by
    rw [← hp, div_pow, ← pow_mul, show 4 * n = 2 * n + 2 * n by omega, pow_add]
    field_simp
  rw [he] at hbound
  have hsq : ((gamma n δ₁ s : ℝ) ^ (2 * n) * cutoffConstant n ^ n) ^ 2 < 1 := by
    have heq : ((gamma n δ₁ s : ℝ) ^ (2 * n) * cutoffConstant n ^ n) ^ 2 =
        (delta δ₁ s : ℝ) * cutoffConstant n ^ (2 * n) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      rw [show 2 * n * 2 = 4 * n by omega, show n * 2 = 2 * n by omega, hp]
    rw [heq]
    exact b.delta_cutoffConstant_small s
  have hh : (gamma n δ₁ s : ℝ) ^ (2 * n) * cutoffConstant n ^ n < 1 := by nlinarith
  exact hbound.trans hh

end InitialParameters
end KamProject.Arnold1963.Iteration
