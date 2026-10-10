/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.InitialParameters

/-!
Strictly increasing Fourier cutoffs from the actual perturbation and angle-loss sequences.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963.Iteration

/-- The Fourier cutoff selected from the stage's strip loss and perturbation bound. -/
def cutoff (n : ℕ) (δ₁ : ℝ≥0) (s : ℕ) : ℝ :=
  fundamentalCutoff (gamma n δ₁ s) (2 * perturbation n δ₁ s)

/-- The preceding Fourier cutoff, initialized to one before the first step. -/
def previousCutoff (n : ℕ) (δ₁ : ℝ≥0) : ℕ → ℝ
  | 0 => 1
  | s + 1 => cutoff n δ₁ s

namespace InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b

theorem perturbation_step_pos (s : ℕ) : 0 < perturbation n δ₁ s :=
  pow_pos (b.delta_step_pos s) _

theorem perturbation_le_delta (s : ℕ) : perturbation n δ₁ s ≤ delta δ₁ s := by
  have hd : (delta δ₁ s : ℝ) ≤ 1 := (b.delta_step_le s).trans b.delta_one.le
  simpa only [perturbation, pow_one] using pow_le_pow_of_le_one
    (delta δ₁ s).coe_nonneg hd (show 1 ≤ iterationExponent n by unfold iterationExponent; omega)

theorem cutoff_numerator_gt_half (s : ℕ) :
    1 / 2 < Real.log (1 / (2 * perturbation n δ₁ s)) := by
  have hM := b.perturbation_step_pos s
  have hM4 : perturbation n δ₁ s < 1 / 4 :=
    (b.perturbation_le_delta s).trans_lt ((b.delta_step_le s).trans_lt b.delta_quarter)
  have hi : (2 : ℝ) < 1 / (2 * perturbation n δ₁ s) :=
    (lt_div_iff₀ (by positivity)).mpr (by linarith)
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  exact hl.trans_lt (Real.log_lt_log (by norm_num) hi)

theorem cutoff_gt_one (s : ℕ) : 1 < cutoff n δ₁ s := by
  apply (lt_div_iff₀ (show (0 : ℝ) < gamma n δ₁ s from b.gamma_step_pos s)).mpr
  have hg := b.gamma_step_quarter s
  have hl := b.cutoff_numerator_gt_half s
  linarith

theorem cutoff_strictMono : StrictMono (cutoff n δ₁) := by
  intro s t hst
  have hd := b.delta_strictAnti hst
  have hm : perturbation n δ₁ t < perturbation n δ₁ s :=
    pow_lt_pow_left₀ (show (delta δ₁ t : ℝ) < delta δ₁ s from hd)
      (delta δ₁ t).coe_nonneg (by unfold iterationExponent; omega)
  have hMs := b.perturbation_step_pos s
  have hMt := b.perturbation_step_pos t
  have hl : Real.log (1 / (2 * perturbation n δ₁ s)) <
      Real.log (1 / (2 * perturbation n δ₁ t)) := by
    apply Real.log_lt_log (by positivity)
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hg : (gamma n δ₁ t : ℝ) ≤ gamma n δ₁ s := by
    simp only [gamma_eq, NNReal.coe_rpow]
    exact Real.rpow_le_rpow (delta δ₁ t).coe_nonneg hd.le (by positivity)
  have hgp : (0 : ℝ) < gamma n δ₁ t := b.gamma_step_pos t
  exact (div_lt_div_of_pos_right hl (b.gamma_step_pos s)).trans_le
    (div_le_div_of_nonneg_left (by linarith [b.cutoff_numerator_gt_half t]) hgp hg)

theorem previousCutoff_strictMono : StrictMono (previousCutoff n δ₁) := by
  apply strictMono_nat_of_lt_succ
  intro s
  cases s with
  | zero => exact b.cutoff_gt_one 0
  | succ s => exact b.cutoff_strictMono (Nat.lt_succ_self s)

theorem previousCutoff_ge_one (s : ℕ) : 1 ≤ previousCutoff n δ₁ s :=
  b.previousCutoff_strictMono.monotone (Nat.zero_le s)

theorem cutoff_step_le (s : ℕ) : previousCutoff n δ₁ s ≤ cutoff n δ₁ s :=
  (b.previousCutoff_strictMono (Nat.lt_succ_self s)).le

end InitialParameters
end KamProject.Arnold1963.Iteration
