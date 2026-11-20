/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.QuadraticBound

/-! # The cubic-threshold corollary -/

@[expose] public section
namespace NoncommutativeAMGM

/-- The cubic sample-size condition implies the quadratic threshold for `m≥2`. -/
theorem cubic_implies_quadratic {m n : ℕ} (hm : 2 ≤ m) (hcube : m ^ 3 ≤ 2 * n) :
    2 * ((m + 1) / 2) ^ 2 ≤ n := by
  by_cases hm2 : m = 2
  · subst m
    norm_num at hcube ⊢
    omega
  have hm3 : 3 ≤ m := by omega
  have hδ : 2 * ((m + 1) / 2) ≤ m + 1 := by omega
  have hsq := Nat.mul_self_le_mul_self hδ
  have hc : 3 * (m * m) ≤ m ^ 3 := by
    simpa [pow_succ, pow_two, Nat.mul_assoc] using Nat.mul_le_mul_right (m * m) hm3
  have hc2 : 3 * m ≤ m * m := Nat.mul_le_mul_right m hm3
  nlinarith

/-- Corollary 3.6: the original cubic threshold gives both Loewner bounds. -/
theorem withoutReplacementMean_cubic_bounds {n m dim : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hcube : m ^ 3 ≤ 2 * n)
    (A : Fin n → Matrix (Fin dim) (Fin dim) ℝ) (hA : Admissible A) :
    LoewnerLE (-(1 : Matrix (Fin dim) (Fin dim) ℝ)) (withoutReplacementMean n m A) ∧
      LoewnerLE (withoutReplacementMean n m A) 1 := by
  by_cases hm1 : m = 1
  · subst m
    exact mean_one_bounds (by omega) A hA
  · exact withoutReplacementMean_quadratic_bounds hm hmn
      (cubic_implies_quadratic (by omega) hcube) A hA

end NoncommutativeAMGM
