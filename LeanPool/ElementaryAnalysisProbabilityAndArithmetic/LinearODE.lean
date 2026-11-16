/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Linear ODEs with a constant coefficient

The variation of constants formula (Duhamel's formula) for the linear ODE `y' = A * y + F t`,
where `A` lies in a complete normed real algebra and `F` is continuous: the solution with
`y t₀ = y₀` is `t ↦ exp ((t - t₀) • A) * (y₀ + ∫ s in t₀..t, exp ((t₀ - s) • A) * F s)`, and it
is the only one.

## Main statements

* `hasDerivAt_exp_smul_mul_integral`: the formula solves `y' = A * y + F t`.
* `eq_exp_smul_mul_integral_of_hasDerivAt`: every solution with `y t₀ = y₀` is given by the
  formula.
-/

public section

open NormedSpace Set

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Duhamel's formula** (variation of constants): for `A : 𝔸` and a continuous `F`, the function
`t ↦ exp ((t - t₀) • A) * (y₀ + ∫ s in t₀..t, exp ((t₀ - s) • A) * F s)` solves
`y' = A * y + F t`. -/
theorem hasDerivAt_exp_smul_mul_integral (A y₀ : 𝔸) {F : ℝ → 𝔸} (hF : Continuous F)
    (t₀ t : ℝ) :
    HasDerivAt (fun t ↦ exp ((t - t₀) • A) * (y₀ + ∫ s in t₀..t, exp ((t₀ - s) • A) * F s))
      (A * (exp ((t - t₀) • A) * (y₀ + ∫ s in t₀..t, exp ((t₀ - s) • A) * F s)) + F t) t := by
  have hc : Continuous fun s ↦ exp ((t₀ - s) • A) * F s :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp (by fun_prop)).mul hF
  have h1 := (hasDerivAt_exp_smul_const' A (t - t₀)).comp_sub_const t t₀
  convert h1.mul ((hc.integral_hasStrictDerivAt t₀ t).hasDerivAt.const_add y₀) using 1
  rw [mul_assoc, ← mul_assoc (exp _), ← exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl A).smul_left _).smul_right _) (by simp [expSeries_radius_eq_top])
    (by simp [expSeries_radius_eq_top]), ← add_smul, sub_add_sub_cancel', sub_self, zero_smul,
    exp_zero, one_mul, mul_add]

/-- Uniqueness in **Duhamel's formula**: a solution of `y' = A * y + F t` with `y t₀ = y₀` is
`t ↦ exp ((t - t₀) • A) * (y₀ + ∫ s in t₀..t, exp ((t₀ - s) • A) * F s)`. -/
theorem eq_exp_smul_mul_integral_of_hasDerivAt {A y₀ : 𝔸} {F y : ℝ → 𝔸} {t₀ : ℝ}
    (hF : Continuous F) (hy : ∀ t, HasDerivAt y (A * y t + F t) t) (hy₀ : y t₀ = y₀) :
    y = fun t ↦ exp ((t - t₀) • A) * (y₀ + ∫ s in t₀..t, exp ((t₀ - s) • A) * F s) := by
  refine ODE_solution_unique_univ (v := fun t x ↦ A * x + F t) (s := fun _ ↦ univ) (t₀ := t₀)
    (K := ‖A‖₊) (fun t ↦ (LipschitzWith.of_dist_le_mul fun x z ↦ ?_).lipschitzOnWith)
    (fun t ↦ ⟨hy t, trivial⟩)
    (fun t ↦ ⟨hasDerivAt_exp_smul_mul_integral A y₀ hF t₀ t, trivial⟩) (by simp [hy₀])
  simpa [dist_eq_norm, ← mul_sub] using norm_mul_le A (x - z)
