/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.StoppingGeneration

/-!
# High-contrast homogenization: Provider.Quenched.SuperGeometricTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Summation of a super-geometric family of exponentials

A stretched-exponential tail whose argument grows by a fixed triadic factor at
each step is summable, and its sum is dominated by twice its first term as soon
as the one-step gain exceeds the logarithm of two.  This is the elementary
mechanism that converts the per-generation Gaussian gauge of the endgame into a
single stretched-exponential bound after the union bound over generations.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

noncomputable section

/-- The triadic Bernoulli bound at a natural exponent. -/
private theorem one_add_mul_le_rpow_nat {nu : ℝ} (hnu : 0 ≤ nu) (j : ℕ) :
    1 + (j : ℝ) * ((3 : ℝ) ^ nu - 1) ≤ (3 : ℝ) ^ (nu * (j : ℝ)) := by
  have hpow : (3 : ℝ) ^ (nu * (j : ℝ)) = ((3 : ℝ) ^ nu) ^ j := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
  have hone : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ nu :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hnu
  rw [Real.rpow_zero] at hone
  have hbern := one_add_mul_le_pow (a := (3 : ℝ) ^ nu - 1)
    (by linarith only [hone]) j
  have hbase : (1 : ℝ) + ((3 : ℝ) ^ nu - 1) = (3 : ℝ) ^ nu := by ring
  rw [hpow]
  calc
    1 + (j : ℝ) * ((3 : ℝ) ^ nu - 1) ≤ (1 + ((3 : ℝ) ^ nu - 1)) ^ j := hbern
    _ = ((3 : ℝ) ^ nu) ^ j := by rw [hbase]

/-- A family whose exponent grows at least linearly with a positive slope has a
summable exponential tail. -/
private theorem summable_exp_neg_of_linear_growth {A c : ℝ} {T : ℕ → ℝ}
    (hc : 0 < c) (hcA : ∀ j : ℕ, A + (j : ℝ) * c ≤ A * T j) :
    Summable fun j : ℕ => Real.exp (-(A * T j)) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith only [hc])
  have hterm : ∀ j : ℕ,
      Real.exp (-(A * T j)) ≤ Real.exp (-A) * Real.exp (-c) ^ j := by
    intro j
    have hmono : Real.exp (-(A * T j)) ≤ Real.exp (-(A + (j : ℝ) * c)) :=
      Real.exp_le_exp.mpr (neg_le_neg (hcA j))
    have heq : Real.exp (-(A + (j : ℝ) * c)) =
        Real.exp (-A) * Real.exp (-c) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    exact hmono.trans heq.le
  exact Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) hterm
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _)

/-- Once the one-step gain exceeds the logarithm of two, the whole exponential
family sums to at most twice its first term. -/
private theorem tsum_exp_neg_le_two_mul {A c : ℝ} {T : ℕ → ℝ}
    (hc : Real.log 2 ≤ c) (hcA : ∀ j : ℕ, A + (j : ℝ) * c ≤ A * T j) :
    ∑' j : ℕ, Real.exp (-(A * T j)) ≤ 2 * Real.exp (-A) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcpos : 0 < c := lt_of_lt_of_le hlog2 hc
  have hr0 : (0 : ℝ) ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hhalf : Real.exp (-c) ≤ 1 / 2 := by
    have hstep : Real.exp (-c) ≤ Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr (neg_le_neg hc)
    have hval : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    exact hval ▸ hstep
  have hr1 : Real.exp (-c) < 1 := lt_of_le_of_lt hhalf (by norm_num)
  have hterm : ∀ j : ℕ,
      Real.exp (-(A * T j)) ≤ Real.exp (-A) * Real.exp (-c) ^ j := by
    intro j
    have hmono : Real.exp (-(A * T j)) ≤ Real.exp (-(A + (j : ℝ) * c)) :=
      Real.exp_le_exp.mpr (neg_le_neg (hcA j))
    have heq : Real.exp (-(A + (j : ℝ) * c)) =
        Real.exp (-A) * Real.exp (-c) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    exact hmono.trans heq.le
  have hsummable_r : Summable fun j : ℕ => Real.exp (-A) * Real.exp (-c) ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsummable : Summable fun j : ℕ => Real.exp (-(A * T j)) :=
    summable_exp_neg_of_linear_growth hcpos hcA
  have hgeom : ∑' j : ℕ, Real.exp (-A) * Real.exp (-c) ^ j =
      Real.exp (-A) * (1 - Real.exp (-c))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hinvpos : (0 : ℝ) < 1 - Real.exp (-c) := by
    have := hhalf
    linarith only [this]
  have hinv : (1 - Real.exp (-c))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hinvpos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hhalf]
  calc
    ∑' j : ℕ, Real.exp (-(A * T j))
        ≤ ∑' j : ℕ, Real.exp (-A) * Real.exp (-c) ^ j :=
      hsummable.tsum_le_tsum hterm hsummable_r
    _ = Real.exp (-A) * (1 - Real.exp (-c))⁻¹ := hgeom
    _ ≤ Real.exp (-A) * 2 := by
      exact mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
    _ = 2 * Real.exp (-A) := by ring

/-- The triadic linear-growth datum of the super-geometric family. -/
private theorem triadic_linear_growth {A nu : ℝ} (hA : 0 ≤ A) (hnu : 0 ≤ nu)
    (j : ℕ) :
    A + (j : ℝ) * (A * ((3 : ℝ) ^ nu - 1)) ≤ A * (3 : ℝ) ^ (nu * (j : ℝ)) := by
  have hbern := one_add_mul_le_rpow_nat hnu j
  have hmul := mul_le_mul_of_nonneg_left hbern hA
  calc
    A + (j : ℝ) * (A * ((3 : ℝ) ^ nu - 1))
        = A * (1 + (j : ℝ) * ((3 : ℝ) ^ nu - 1)) := by ring
    _ ≤ A * (3 : ℝ) ^ (nu * (j : ℝ)) := hmul

/-- The triadic super-geometric exponential family is summable. -/
theorem summable_exp_neg_triadic {A nu : ℝ} (hA : 0 < A) (hnu : 0 < nu) :
    Summable fun j : ℕ => Real.exp (-(A * (3 : ℝ) ^ (nu * (j : ℝ)))) := by
  have hgain : 0 < A * ((3 : ℝ) ^ nu - 1) := by
    have hone : (3 : ℝ) ^ (0 : ℝ) < (3 : ℝ) ^ nu :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hnu
    rw [Real.rpow_zero] at hone
    have hpos : (0 : ℝ) < (3 : ℝ) ^ nu - 1 := by linarith only [hone]
    exact mul_pos hA hpos
  exact summable_exp_neg_of_linear_growth hgain
    (triadic_linear_growth hA.le hnu.le)

/-- The triadic super-geometric exponential family sums to at most twice its
first term once its one-step gain exceeds the logarithm of two. -/
theorem tsum_exp_neg_triadic_le_two_mul {A nu : ℝ} (hA : 0 ≤ A) (hnu : 0 ≤ nu)
    (hthr : Real.log 2 ≤ A * ((3 : ℝ) ^ nu - 1)) :
    ∑' j : ℕ, Real.exp (-(A * (3 : ℝ) ^ (nu * (j : ℝ)))) ≤ 2 * Real.exp (-A) :=
  tsum_exp_neg_le_two_mul hthr (triadic_linear_growth hA hnu)

/-- A positive multiple of an exponential is absorbed by halving its exponent
once the exponent dominates twice the logarithm of the multiple. -/
theorem mul_exp_neg_le_exp_neg_half {A c : ℝ} (hc : 0 < c)
    (hA : 2 * Real.log c ≤ A) :
    c * Real.exp (-A) ≤ Real.exp (-(A / 2)) := by
  have hceq : c = Real.exp (Real.log c) := (Real.exp_log hc).symm
  calc
    c * Real.exp (-A) = Real.exp (Real.log c) * Real.exp (-A) := by rw [← hceq]
    _ = Real.exp (Real.log c + -A) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(A / 2)) := Real.exp_le_exp.mpr (by linarith only [hA])

end

end Quenched
end HighContrast
end HCPolySupport
