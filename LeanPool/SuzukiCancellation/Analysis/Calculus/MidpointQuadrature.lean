/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Midpoint quadrature in real normed spaces

The midpoint rule cancels the linear Taylor term exactly. Integrating a
quadratic remainder bound gives the sharp constant `1 / 24`, independently
of the dimension of the target space.

## Main results

* `norm_midpoint_smul_sub_integral_le`: the single-interval estimate.
* `norm_midpoint_sum_sub_integral_le`: the composite midpoint estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Finset

namespace TrotterError

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Midpoint quadrature bound.** A quadratic Taylor remainder with coefficient
`J / 2` gives an interval error bounded by `h ^ 3 * J / 24`. -/
theorem norm_midpoint_smul_sub_integral_le (f : ℝ → E) (hf : Continuous f)
    (a h J : ℝ) (hh : 0 ≤ h) (d : E)
    (hrem : ∀ x ∈ Set.Icc a (a + h),
      ‖f x - f (a + h / 2) - (x - (a + h / 2)) • d‖ ≤
        J / 2 * (x - (a + h / 2)) ^ 2) :
    ‖h • f (a + h / 2) - ∫ x in a..a + h, f x‖ ≤ h ^ 3 * J / 24 := by
  let c := a + h / 2
  have hi : (∫ x in a..a + h, x - c) = 0 := by
    rw [intervalIntegral.integral_sub (f := fun x : ℝ ↦ x) (g := fun _ ↦ c)
      (continuous_id.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
    simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
    dsimp [c]
    ring
  have hsq : (∫ x in a..a + h, J / 2 * (x - c) ^ 2) = h ^ 3 * J / 24 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ 2)]
    rw [integral_pow]
    dsimp [c]
    norm_num
    ring
  have heq : (∫ x in a..a + h, f x - f c - (x - c) • d) =
      (∫ x in a..a + h, f x) - h • f c := by
    rw [intervalIntegral.integral_sub
      (f := fun x ↦ f x - f c) (g := fun x ↦ (x - c) • d)
      ((hf.sub continuous_const).intervalIntegrable _ _)
      ((continuous_id.sub continuous_const).smul continuous_const |>.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_smul_const, hi]
    simp
  rw [norm_sub_rev, ← heq, ← hsq]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · filter_upwards with x hx
    exact hrem x ⟨hx.1.le, hx.2⟩
  · exact (show Continuous (fun x : ℝ ↦ J / 2 * (x - c) ^ 2) by
      fun_prop).intervalIntegrable _ _

omit [CompleteSpace E] in
/-- **Composite midpoint quadrature bound.** Each of the `r` equal cells
contributes at most `h ^ 3 * J / 24`. -/
theorem norm_midpoint_sum_sub_integral_le (f : ℝ → E) (hf : Continuous f)
    (r : ℕ) (h J : ℝ)
    (hcell : ∀ k < r,
      ‖h • f (((k : ℝ) + 1 / 2) * h) -
        ∫ x in (k : ℝ) * h..((k : ℝ) + 1) * h, f x‖ ≤ h ^ 3 * J / 24) :
    ‖h • ∑ k ∈ range r, f (((k : ℝ) + 1 / 2) * h) -
      ∫ x in 0..(r : ℝ) * h, f x‖ ≤ (r : ℝ) * h ^ 3 * J / 24 := by
  have hint := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ (k : ℝ) * h) (n := r) (μ := volume)
    (fun k _ ↦ hf.intervalIntegrable ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h))
  simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at hint
  rw [← hint, Finset.smul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ range r, ‖h • f (((k : ℝ) + 1 / 2) * h) -
        ∫ x in (k : ℝ) * h..((k : ℝ) + 1) * h, f x‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range r, h ^ 3 * J / 24 := sum_le_sum fun k hk ↦ hcell k (mem_range.mp hk)
    _ = _ := by simp [mul_div_assoc, mul_assoc]

end TrotterError
