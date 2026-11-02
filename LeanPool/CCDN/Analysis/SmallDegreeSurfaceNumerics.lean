/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Explicit exponent margins for the small-degree surface argument.
The estimates hold uniformly for every degree at least five and absorb any
fixed power of the logarithm; geometric covering hypotheses are separate. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- For every natural number `d ≥ 5`, `1 / √d ≤ 9 / 20`. -/
theorem surface_inverse_sqrt_le_nine_twentieths {d : ℕ} (hd : 5 ≤ d) :
    1 / Real.sqrt (d : ℝ) ≤ (9 / 20 : ℝ) := by
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : (20 / 9 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20 / 9) hs
  norm_num at hh
  simpa only [one_div] using hh

/-- A fixed logarithmic power costs at most any prescribed positive power,
with an explicit constant independent of the box radius. -/
theorem logarithm_add_one_pow_le_rpow (k : ℕ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 1 ≤ B) :
    (Real.log B + 1) ^ k ≤
      ((k.factorial : ℝ) / ε ^ k * Real.exp ε) * B ^ ε := by
  have hB0 : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hh := Real.pow_div_factorial_le_exp (ε * (Real.log B + 1))
    (show 0 ≤ ε * (Real.log B + 1) by positivity) k
  have he : Real.exp (ε * (Real.log B + 1)) = Real.exp ε * B ^ ε := by
    rw [Real.rpow_def_of_pos hB0, ← Real.exp_add]
    congr 1
    ring
  rw [he, mul_pow] at hh
  have hm := (div_le_iff₀ hfac).mp hh
  calc
    _ ≤ (Real.exp ε * B ^ ε * (k.factorial : ℝ)) / ε ^ k := by
      apply (le_div_iff₀ (pow_pos hε k)).mpr
      simpa only [mul_comm] using hm
    _ = _ := by ring

/-- Retained nonlinear curves with square-root box count and any fixed
polylogarithmic loss contribute O(B) once their number has the
B^(1/sqrt(d)) scale, for every d>=5. -/
theorem surface_nonlinear_polylog_weight {d : ℕ} (hd : 5 ≤ d) (k : ℕ)
    {B : ℝ} (hB : 1 ≤ B) :
    B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ k ≤
      ((k.factorial : ℝ) / (1 / 20 : ℝ) ^ k * Real.exp (1 / 20)) * B := by
  have hB0 : 0 < B := by linarith
  have hlog := logarithm_add_one_pow_le_rpow k (by norm_num : (0 : ℝ) < 1 / 20) hB
  let C : ℝ := (k.factorial : ℝ) / (1 / 20 : ℝ) ^ k * Real.exp (1 / 20)
  have hC : 0 ≤ C := by positivity
  have he : 1 / Real.sqrt (d : ℝ) + 1 / 2 + 1 / 20 ≤ (1 : ℝ) := by
    have := surface_inverse_sqrt_le_nine_twentieths hd
    linarith
  calc
    _ ≤ B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (C * B ^ (1 / 20 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C * B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2 + 1 / 20) := by
      rw [Real.rpow_add hB0 (1 / Real.sqrt (d : ℝ) + 1 / 2) (1 / 20)]
      ring
    _ ≤ C * B := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB he) hC

end
end CCDN
