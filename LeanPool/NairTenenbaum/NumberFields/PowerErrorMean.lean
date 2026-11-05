/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Identifying the leading coefficient of a power-saving count -/

@[expose] public section

namespace NairTenenbaum

open Filter
open scoped Topology

theorem tendsto_div_of_power_error {A : ℝ → ℝ} {V C θ : ℝ} (hθ : θ < 1)
    (hA : ∀ x : ℝ, 1 ≤ x → |A x - V * x| ≤ C * x ^ θ) :
    Tendsto (fun x : ℝ => A x / x) atTop (𝓝 V) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have Hlim : Tendsto (fun x : ℝ => C * x ^ (θ - 1)) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (show 0 < 1 - θ by linarith)).const_mul C
    simpa only [neg_sub, mul_zero] using H
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ Hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.norm_eq_abs, show A x / x - V = (A x - V * x) / x by field_simp,
    abs_div, abs_of_pos hx0, Real.rpow_sub_one hx0.ne']
  convert div_le_div_of_nonneg_right (hA x hx) hx0.le using 1; ring

theorem leading_coefficient_eq_of_power_error {A : ℝ → ℝ} {V C θ L : ℝ} (hθ : θ < 1)
    (hA : ∀ x : ℝ, 1 ≤ x → |A x - V * x| ≤ C * x ^ θ)
    (hmean : Tendsto (fun x : ℝ => A x / x) atTop (𝓝 L)) : V = L :=
  tendsto_nhds_unique (tendsto_div_of_power_error hθ hA) hmean

end NairTenenbaum
