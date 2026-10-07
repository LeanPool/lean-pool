/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCSlabEstimate

/-!
# Polynomial control of Gaussian decay

An exponential with negative reciprocal time is bounded by any fixed
positive integer power of time.
-/

public section


noncomputable section

namespace ESS

/-- A reciprocal-time Gaussian is bounded by an explicit polynomial. -/
theorem uc_exp_neg_div_le_pow
    (b t : ℝ) (n : ℕ) (hb : 0 < b) (ht : 0 < t) (hn : 0 < n) :
    Real.exp (-(b / t)) ≤ ((n : ℝ) * t / b) ^ n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  let x : ℝ := b / ((n : ℝ) * t)
  have hx : 0 < x := by dsimp [x]; positivity
  have hbase : x ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith only [h]
  have hpow : x ^ n ≤ Real.exp (b / t) := by
    calc
      x ^ n ≤ (Real.exp x) ^ n :=
        pow_le_pow_left₀ hx.le hbase _
      _ = Real.exp (b / t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [x]
        field_simp
  calc
    Real.exp (-(b / t)) = (Real.exp (b / t))⁻¹ := Real.exp_neg _
    _ ≤ (x ^ n)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (pow_pos hx _)).mpr hpow
    _ = ((n : ℝ) * t / b) ^ n := by
      rw [← inv_pow]
      dsimp [x]
      rw [inv_div]

end ESS
