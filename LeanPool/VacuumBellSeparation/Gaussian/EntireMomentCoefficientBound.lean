/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCauchyCoefficients
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialPolydiscKernels
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The exact base 5a in the multivariate Cauchy moment bound

The radius (n+1)/(sqrt(3)*a) treats n=0 uniformly and costs only a
single additional exp(1) in the unspecified prefactor. The exponential
base remains exactly 5a. Coefficients are the actual nested integrals.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped BigOperators

theorem exp_one_mul_sqrt_three_lt_five : Real.exp 1 * Real.sqrt 3 < 5 := by
  have he : Real.exp 1 < 11 / 4 := by linarith [Real.exp_one_lt_d9]
  have hs : Real.sqrt 3 ≤ 7 / 4 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  calc
    _ < (11 / 4 : ℝ) * Real.sqrt 3 :=
      mul_lt_mul_of_pos_right he (Real.sqrt_pos.mpr (by norm_num))
    _ ≤ (11 / 4 : ℝ) * (7 / 4) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ < 5 := by norm_num

theorem multiIndex_factorial_le_succ_degree_pow (α : Fin 3 → ℕ) :
    (∏ j, ((α j).factorial : ℝ)) ≤ ((∑ j, α j : ℕ) + 1 : ℝ) ^ (∑ j, α j) := by
  have hf : (∏ j, (α j).factorial) ≤ (∑ j, α j).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ α)
  have hp := (Nat.factorial_le_pow (∑ j, α j)).trans
    (Nat.pow_le_pow_left (Nat.le_succ _) _)
  exact_mod_cast hf.trans hp

/-- Moment Cauchy radius given by `((∑ j, α j : ℕ) + 1 : ℝ) / (Real.sqrt 3 * a)`. -/
noncomputable def momentCauchyRadius (a : ℝ) (α : Fin 3 → ℕ) : ℝ :=
  ((∑ j, α j : ℕ) + 1 : ℝ) / (Real.sqrt 3 * a)

theorem entire_moment_coefficient_bound {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (F : (Fin 3 → ℂ) → ℂ)
    (hF : ∀ z : EuclideanSpace ℂ (Fin 3), ‖F (WithLp.ofLp z)‖ ≤ A * Real.exp (a * ‖z‖))
    (α : Fin 3 → ℕ) :
    (∏ j, ((α j).factorial : ℝ)) *
      ‖polydiscCoefficient 3 (momentCauchyRadius a α) F α‖ ≤
        Real.exp 1 * A * (5 * a) ^ (∑ j, α j) := by
  let n : ℕ := ∑ j, α j
  let R : ℝ := momentCauchyRadius a α
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hR : 0 < R := by dsimp [R, momentCauchyRadius]; positivity
  have hcancel : a * (Real.sqrt 3 * R) = n + 1 := by
    dsimp [R, momentCauchyRadius, n]
    field_simp [ha.ne', hs.ne']
  have hbound : ∀ z ∈ coordinateClosedPolydisc 3 R,
      ‖F z‖ ≤ A * Real.exp ((n : ℝ) + 1) := by
    intro z hz
    have hn := spatial_triple_norm_le_of_coordinate_bounds hR.le (WithLp.toLp 2 z) hz
    calc
      _ ≤ A * Real.exp (a * ‖WithLp.toLp 2 z‖) := hF (WithLp.toLp 2 z)
      _ ≤ A * Real.exp (a * (Real.sqrt 3 * R)) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn ha.le)) hA
      _ = _ := by rw [hcancel]
  have hc := polydiscCoefficient_norm_le 3 hR (by positivity) F hbound α
  rw [Finset.prod_pow_eq_pow_sum] at hc
  have hfact := multiIndex_factorial_le_succ_degree_pow α
  have hpow : ((n : ℝ) + 1) ^ n * R⁻¹ ^ n = (Real.sqrt 3 * a) ^ n := by
    rw [← mul_pow]
    congr 1
    dsimp [R, momentCauchyRadius, n]
    field_simp [ha.ne', hs.ne']
  have hexp : Real.exp ((n : ℝ) + 1) = Real.exp 1 * Real.exp 1 ^ n := by
    rw [Real.exp_add, mul_comm]
    congr 1
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) n
  have heq : ((n : ℝ) + 1) ^ n * (A * Real.exp ((n : ℝ) + 1) * R⁻¹ ^ n) =
      Real.exp 1 * A * (Real.exp 1 * Real.sqrt 3 * a) ^ n := by
    rw [hexp]
    calc
      _ = Real.exp 1 * A * (Real.exp 1 ^ n * (((n : ℝ) + 1) ^ n * R⁻¹ ^ n)) := by ring
      _ = _ := by rw [hpow, ← mul_pow]; congr 1; ring
  calc
    _ ≤ ((n : ℝ) + 1) ^ n * (A * Real.exp ((n : ℝ) + 1) * R⁻¹ ^ n) :=
      mul_le_mul hfact hc (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * A * (Real.exp 1 * Real.sqrt 3 * a) ^ n := heq
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right exp_one_mul_sqrt_three_lt_five.le ha.le) n) (by positivity)

end VacuumBellSeparation.Gaussian
