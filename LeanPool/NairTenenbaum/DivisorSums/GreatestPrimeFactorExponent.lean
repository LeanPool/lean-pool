/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.DivisorSums.PrimeFactorLogGain
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The exponent margin in Theorem 2 -/

@[expose] public section

namespace NairTenenbaum

open Filter Real
open scoped Topology

theorem eventually_log_rpow_lt_gain {α η c : ℝ} (hα : α < 1 - η) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ α < c * (Real.log x) ^ (1 - η) := by
  have H : Tendsto (fun x : ℝ => (Real.log x) ^ (α - (1 - η))) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (show 0 < (1 - η) - α by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [H.eventually (gt_mem_nhds hc), eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  have hl := Real.log_pos hx₁
  rw [Real.rpow_sub hl] at hx
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos hl _)).mp hx

/-- The final strict inequality follows from any fixed positive coefficient
in the stronger logarithmic exponent. -/
theorem eventually_greatestPrimeFactor_gain {α η c : ℝ} (hα : α < 1 - η) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ y P : ℝ, 0 < y →
      y * Real.exp (c * (Real.log x) ^ (1 - η)) ≤ P →
        y * Real.exp ((Real.log x) ^ α) < P := by
  filter_upwards [eventually_log_rpow_lt_gain hα hc] with x hx
  intro y P hy hP
  exact (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hx) hy).trans_le hP

end NairTenenbaum
