/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.SimplexEigenvalue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The exact threshold revealed by the counterexample eigenvalue -/

@[expose] public section

namespace NoncommutativeAMGM

/-- The simplex eigenvalue has modulus at most one exactly at the stated threshold. -/
theorem simplex_eigenvalue_abs_le_iff {n m ℓ : ℕ} (hn : 1 < n) (hm : 1 < m)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    |(-1 : ℝ) ^ ℓ * ((n : ℝ) / ((n : ℝ) - 1) * c) ^ (m - 1)| ≤ 1 ↔
      1 / (1 - c) ≤ (n : ℝ) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 1 := by linarith
  have hc : 0 < 1 - c := by linarith
  let q := (n : ℝ) / ((n : ℝ) - 1) * c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpow : q ^ (m - 1) ≤ 1 ↔ q ≤ 1 := by
    constructor
    · intro h
      by_contra hq1
      have hlt := one_lt_pow₀ (lt_of_not_ge hq1) (show m - 1 ≠ 0 by omega)
      linarith
    · exact pow_le_one₀ hq
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hc0, abs_of_nonneg (show 0 ≤ (n : ℝ) / ((n : ℝ) - 1) by positivity)]
  rw [hpow]
  have he : q = ((n : ℝ) * c) / ((n : ℝ) - 1) := by dsimp [q]; ring
  rw [he, div_le_iff₀ hd, div_le_iff₀ hc]
  constructor <;> intro h <;> nlinarith

/-- The exact threshold implies the quadratic necessary scale via the cosine Taylor bound. -/
theorem simplex_threshold_quadratic {n : ℕ} {θ : ℝ} (hn : 0 < n) (hθ : θ ≠ 0)
    (hc : Real.cos θ < 1) (hthreshold : 1 / (1 - Real.cos θ) ≤ (n : ℝ)) :
    2 / θ ^ 2 ≤ (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (div_le_iff₀ (show 0 < 1 - Real.cos θ by linarith)).mp hthreshold
  have hcos : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hmul := mul_le_mul_of_nonneg_left hcos hn'.le
  apply (div_le_iff₀ (sq_pos_of_ne_zero hθ)).mpr
  nlinarith

end NoncommutativeAMGM
