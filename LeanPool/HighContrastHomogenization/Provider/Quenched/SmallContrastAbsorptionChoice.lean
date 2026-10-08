/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAbsorptionChoice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The absorption lag and gain choice

For every response constant `Cpre ≥ 1` there are a lag `H ≥ 4` and a Young
gain `eta > 0` with `Cpre·eta + (3/2)·Cpre·3^{-H} ≤ 1/2`.  This is the scalar
choice that the compact pre-Young reabsorption requires; the lag is
dimension-dependent through `Cpre` and is selected before the law.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The absorption choice: `eta := (4·Cpre)⁻¹` and
`H := max 4 ⌈log₃(6·Cpre)⌉`. -/
theorem exists_absorption_lag_choice {Cpre : ℝ} (hCpre : 1 ≤ Cpre) :
    ∃ (H : ℕ) (eta : ℝ), 4 ≤ H ∧ 0 < eta ∧
      Cpre * eta + (3 / 2 : ℝ) * Cpre * (3 : ℝ) ^ (-(H : ℝ)) ≤ 1 / 2 := by
  have hCpre0 : 0 < Cpre := lt_of_lt_of_le zero_lt_one hCpre
  refine ⟨max 4 ⌈Real.logb 3 (6 * Cpre)⌉₊, (4 * Cpre)⁻¹,
    le_max_left _ _, by positivity, ?_⟩
  set H : ℕ := max 4 ⌈Real.logb 3 (6 * Cpre)⌉₊
  have hfirst : Cpre * (4 * Cpre)⁻¹ = 1 / 4 := by
    field_simp
  have hlogH : Real.logb 3 (6 * Cpre) ≤ (H : ℝ) := by
    calc
      Real.logb 3 (6 * Cpre) ≤ (⌈Real.logb 3 (6 * Cpre)⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ ≤ (H : ℝ) := by
        exact_mod_cast Nat.le_max_right 4 ⌈Real.logb 3 (6 * Cpre)⌉₊
  have hsix : 6 * Cpre ≤ (3 : ℝ) ^ (H : ℝ) := by
    have hle : (3 : ℝ) ^ Real.logb 3 (6 * Cpre) ≤ (3 : ℝ) ^ (H : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlogH
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at hle
  have hinv : (3 : ℝ) ^ (-(H : ℝ)) ≤ (6 * Cpre)⁻¹ := by
    rw [Real.rpow_neg (by norm_num)]
    exact inv_anti₀ (by positivity) hsix
  have hsecond : (3 / 2 : ℝ) * Cpre * (3 : ℝ) ^ (-(H : ℝ)) ≤ 1 / 4 := by
    calc
      (3 / 2 : ℝ) * Cpre * (3 : ℝ) ^ (-(H : ℝ)) ≤
          (3 / 2 : ℝ) * Cpre * (6 * Cpre)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 1 / 4 := by
        field_simp
        ring
  calc
    Cpre * (4 * Cpre)⁻¹ + (3 / 2 : ℝ) * Cpre * (3 : ℝ) ^ (-(H : ℝ)) ≤
        1 / 4 + 1 / 4 := by
      rw [hfirst]
      exact add_le_add le_rfl hsecond
    _ = 1 / 2 := by norm_num

end

end HCPolySupport.HighContrast.Quenched
