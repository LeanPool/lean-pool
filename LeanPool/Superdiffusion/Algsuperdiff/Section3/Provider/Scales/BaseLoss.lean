/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Scales

/-!
# BaseLoss

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Basic A for the Section 3.2 Option-A base loss

`Algsuperdiff.Section3.baseLoss d s = 1 + 6 d (log 3) / s` is the adopted
all-scale loss of the Section 3.2 base case, defined on the literal source
range `0 < s < 1`.

This file records the small facts that downstream base-case estimates need:
the loss is at least one, hence positive, and it is antitone in the multiscale
regularity parameter `s`.

## References

* ABK26, Section 3.2.
-/

namespace Algsuperdiff.Section3.Provider.Scales

/-- The defining formula of the Option-A base loss. -/
theorem baseLoss_eq (d : ℕ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    baseLoss d s = 1 + 6 * (d : ℝ) * Real.log 3 / (s : ℝ) :=
  rfl

/-- The numerator of the loss term is nonnegative. -/
private theorem baseLoss_numerator_nonneg (d : ℕ) :
    (0 : ℝ) ≤ 6 * (d : ℝ) * Real.log 3 :=
  mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    (Real.log_nonneg (by norm_num))

/-- The multiscale parameter of the base loss is strictly positive. -/
private theorem coe_param_pos (s : {s : ℝ // s ∈ Set.Ioo 0 1}) : (0 : ℝ) < (s : ℝ) :=
  (Set.mem_Ioo.mp s.2).1

/-- The Option-A base loss is a genuine loss: it is at least one. -/
theorem one_le_baseLoss (d : ℕ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    1 ≤ baseLoss d s := by
  rw [baseLoss_eq]
  have hdiv : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.log 3 / (s : ℝ) :=
    div_nonneg (baseLoss_numerator_nonneg d) (coe_param_pos s).le
  linarith

/-- The Option-A base loss is strictly positive. -/
theorem baseLoss_pos (d : ℕ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    0 < baseLoss d s :=
  lt_of_lt_of_le zero_lt_one (one_le_baseLoss d s)

/-- The Option-A base loss has a square root of size `K / s` with a
dimension-only `K`: on `0 < s < 1` one has
`baseLoss d s <= (1 + 6 d log 3) s^{-2}`. -/
theorem sqrt_baseLoss_le (d : ℕ) (u : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    Real.sqrt (baseLoss d u) ≤
      Real.sqrt (1 + 6 * (d : ℝ) * Real.log 3) * (u : ℝ)⁻¹ := by
  obtain ⟨hu0, hu1⟩ := u.property
  have hK : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.log 3 :=
    mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  have hKnn : (0 : ℝ) ≤ 1 + 6 * (d : ℝ) * Real.log 3 := by linarith
  have hiu : (0 : ℝ) ≤ (u : ℝ)⁻¹ := inv_nonneg.mpr hu0.le
  have hinv1 : (1 : ℝ) ≤ (u : ℝ)⁻¹ := by
    have hcancel : (u : ℝ) * (u : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hu0.ne'
    have hprod : 0 ≤ (1 - (u : ℝ)) * (u : ℝ)⁻¹ := mul_nonneg (by linarith) hiu
    nlinarith [hcancel, hprod]
  have hsq : (u : ℝ)⁻¹ ≤ ((u : ℝ)⁻¹) ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_left hiu hinv1
  have hone : (1 : ℝ) ≤ ((u : ℝ)⁻¹) ^ 2 := le_trans hinv1 hsq
  have hstep : baseLoss d u ≤ (1 + 6 * (d : ℝ) * Real.log 3) * ((u : ℝ)⁻¹) ^ 2 := by
    rw [Provider.Scales.baseLoss_eq, div_eq_mul_inv]
    have h1 : 6 * (d : ℝ) * Real.log 3 * (u : ℝ)⁻¹ ≤
        6 * (d : ℝ) * Real.log 3 * ((u : ℝ)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hK
    linarith
  calc Real.sqrt (baseLoss d u)
      ≤ Real.sqrt ((1 + 6 * (d : ℝ) * Real.log 3) * ((u : ℝ)⁻¹) ^ 2) :=
        Real.sqrt_le_sqrt hstep
    _ = Real.sqrt (1 + 6 * (d : ℝ) * Real.log 3) * (u : ℝ)⁻¹ := by
        rw [Real.sqrt_mul hKnn, Real.sqrt_sq hiu]

end Algsuperdiff.Section3.Provider.Scales
