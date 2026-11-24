/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.NumberTheory.Bernoulli

/-!
# Scalar series for the symmetric logarithmic derivative

The inverse of `(exp z - 1) / z` is the Bernoulli series. Multiplying this
inverse by `(1 + exp z) / 2` cancels the linear coefficient and leaves only
even Bernoulli coefficients. All series in this file have scalar coefficients;
no commutativity assumption is imposed on a later Lie algebra application.
-/

@[expose] public noncomputable section

namespace FQFP

open PowerSeries

/-- The scalar series `(exp z - 1) / z`, including its constant coefficient one. -/
def exponentialDivX : PowerSeries ℚ :=
  mk fun n ↦ (Nat.factorial (n + 1) : ℚ)⁻¹

theorem exponentialDivX_mul_X : exponentialDivX * X = exp ℚ - 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [exponentialDivX, coeff_exp]

/-- The Bernoulli series inverts the divided exponential, without dividing by `z`. -/
theorem bernoulliPowerSeries_mul_exponentialDivX :
    bernoulliPowerSeries ℚ * exponentialDivX = 1 := by
  apply mul_X_injective
  change (bernoulliPowerSeries ℚ * exponentialDivX) * X = 1 * X
  rw [mul_assoc, exponentialDivX_mul_X, bernoulliPowerSeries_mul_exp_sub_one, one_mul]

/-- The symmetrized logarithmic derivative has no linear Bernoulli contribution. -/
theorem bernoulliPowerSeries_mul_half_exp_add_one :
    bernoulliPowerSeries ℚ * ((2 : ℚ)⁻¹ • (1 + exp ℚ)) =
      bernoulliPowerSeries ℚ + (2 : ℚ)⁻¹ • X := by
  have h := bernoulliPowerSeries_mul_exp_sub_one ℚ
  rw [mul_sub, mul_one] at h
  rw [mul_smul_comm, mul_add, mul_one, sub_eq_iff_eq_add.mp h]
  module

/-- The coefficient formula that selects only even adjoint powers in symmetric BCH. -/
theorem coeff_bernoulliPowerSeries_mul_half_exp_add_one (n : ℕ) :
    coeff n (bernoulliPowerSeries ℚ * ((2 : ℚ)⁻¹ • (1 + exp ℚ))) =
      if n = 0 then 1 else if n % 2 = 0 then bernoulli n / (n.factorial : ℚ) else 0 := by
  rw [bernoulliPowerSeries_mul_half_exp_add_one]
  by_cases hn0 : n = 0
  · subst n
    simp [bernoulliPowerSeries]
  by_cases hn1 : n = 1
  · subst n
    norm_num [bernoulliPowerSeries, bernoulli_one]
  by_cases he : n % 2 = 0
  · simp [bernoulliPowerSeries, coeff_X, hn0, hn1, he]
  · have ho : Odd n := Nat.odd_iff.mpr (by lia)
    simp [bernoulliPowerSeries, coeff_X, hn0, hn1, he,
      bernoulli_eq_zero_of_odd ho (by lia)]

end FQFP
