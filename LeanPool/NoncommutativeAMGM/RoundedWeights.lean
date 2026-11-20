/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.NodePerturbation
public import LeanPool.NoncommutativeAMGM.InverseSquareGaps

/-! # Product estimates for rounded interpolation weights -/

@[expose] public section

namespace NoncommutativeAMGM
open scoped BigOperators

/-- The actual normalized interpolation weights on the rounded cosine nodes. -/
noncomputable def roundedWeight (n m j : ℕ) : ℝ :=
  interpolationWeight m (roundedCosineNode n m) j

/-- A rounded interpolation weight is the ideal weight divided by the product of relative gaps. -/
theorem roundedWeight_eq_chebyshevWeight_mul_inv_prod {n m j : ℕ} (hm : 0 < m)
    (hj : j ≤ m) :
    roundedWeight n m j = chebyshevWeight m j *
      (∏ l ∈ (Finset.range (m + 1)).erase j,
        (roundedCosineNode n m j - roundedCosineNode n m l) /
          (chebyshevNode m j - chebyshevNode m l))⁻¹ := by
  let s := (Finset.range (m + 1)).erase j
  have hc (l : ℕ) (hl : l ∈ s) : chebyshevNode m j - chebyshevNode m l ≠ 0 := by
    have hl' := Finset.mem_erase.mp hl
    exact sub_ne_zero.mpr (chebyshevNode_ne hm hj
      (by have := Finset.mem_range.mp hl'.2; omega) hl'.1.symm)
  rw [roundedWeight, interpolationWeight_perturbation _ (chebyshevNode m) hc,
    interpolationWeight_chebyshev hm hj]

/-- The finite product of gap estimates gives the exact finite-sum exponential bound. -/
theorem roundedWeight_abs_le_exp_sum {n m j : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hj : j ≤ m) :
    |roundedWeight n m j| ≤ |chebyshevWeight m j| *
      Real.exp (∑ l ∈ (Finset.range (m + 1)).erase j,
        2 * (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2)) := by
  classical
  let s := (Finset.range (m + 1)).erase j
  let cost := fun l : ℕ ↦ 2 * (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2)
  let ratio := fun l : ℕ ↦ (roundedCosineNode n m j - roundedCosineNode n m l) /
    (chebyshevNode m j - chebyshevNode m l)
  have hp : Real.exp (-(∑ l ∈ s, cost l)) ≤ ∏ l ∈ s, |ratio l| := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro l _
      positivity
    · intro l hl
      have hl' := Finset.mem_erase.mp hl
      exact roundedCosineNode_gap_ratio_exp hm hn hj
        (by have := Finset.mem_range.mp hl'.2; omega) hl'.1.symm
  have hi : (∏ l ∈ s, |ratio l|)⁻¹ ≤ Real.exp (∑ l ∈ s, cost l) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hp
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  rw [roundedWeight_eq_chebyshevWeight_mul_inv_prod hm hj, abs_mul, abs_inv, Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)

/-- Equation (21): the uniform exponential upper bound for every rounded weight. -/
theorem roundedWeight_abs_le {n m j : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hj : j ≤ m) :
    |roundedWeight n m j| ≤ |chebyshevWeight m j| *
      Real.exp (2 * (m : ℝ) ^ 2 / (n : ℝ) * (Real.pi ^ 2 / 3)) := by
  have he : (∑ l ∈ (Finset.range (m + 1)).erase j,
      2 * (m : ℝ) ^ 2 / ((n : ℝ) * ((j : ℝ) - l) ^ 2)) =
      (2 * (m : ℝ) ^ 2 / (n : ℝ)) *
        ∑ l ∈ (Finset.range (m + 1)).erase j, 1 / ((j : ℝ) - l) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hc := mul_le_mul_of_nonneg_left (inverseSquare_gap_sum hj)
    (show 0 ≤ 2 * (m : ℝ) ^ 2 / (n : ℝ) by positivity)
  rw [← he] at hc
  exact (roundedWeight_abs_le_exp_sum hm hn hj).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hc) (abs_nonneg _))

end NoncommutativeAMGM
