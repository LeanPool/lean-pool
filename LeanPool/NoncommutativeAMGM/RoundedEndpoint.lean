/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RoundedWeights
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The retained endpoint weight for rounded interpolation -/

@[expose] public section

namespace NoncommutativeAMGM
open scoped BigOperators

/-- The endpoint needs only the one-sided rounding error in the relative gap estimate. -/
theorem roundedCosineNode_endpoint_ratio {n m l : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hl0 : 0 < l) (hlm : l ≤ m) :
    let r := (1 - roundedCosineNode n m l) / (1 - chebyshevNode m l)
    0 < r ∧ r ≤ Real.exp ((m : ℝ) ^ 2 / (2 * (n : ℝ) * (l : ℝ) ^ 2)) := by
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl0
  have hgap := chebyshevNode_gap hm (Nat.zero_le l) hlm
  simp only [chebyshevNode, Nat.cast_zero, zero_mul, zero_div, Real.cos_zero,
    sub_zero] at hgap
  change 2 / (m : ℝ) ^ 2 * (l : ℝ) ^ 2 ≤ 1 - chebyshevNode m l at hgap
  have hd : 0 < 1 - chebyshevNode m l :=
    (by positivity : 0 < 2 / (m : ℝ) ^ 2 * (l : ℝ) ^ 2).trans_le hgap
  have hr0 : 0 ≤ (1 - roundedCosineNode n m l) / (1 - chebyshevNode m l) :=
    div_nonneg (by have := (roundedCosineNode_mem hn0 m l).2; linarith) hd.le
  constructor
  · have h := roundedCosineNode_gap_ratio_exp hm hn (Nat.zero_le m) hlm
      (by omega : 0 ≠ l)
    simp only [roundedCosineNode_zero, chebyshevNode, Nat.cast_zero, zero_mul,
      zero_div, Real.cos_zero] at h
    change Real.exp _ ≤ |(1 - roundedCosineNode n m l) / (1 - chebyshevNode m l)| at h
    rw [abs_of_nonneg hr0] at h
    exact (Real.exp_pos _).trans_le h
  · have he := (abs_le.mp (roundedCosineNode_error hn0 m l)).1
    have hb : (1 / (n : ℝ)) / (1 - chebyshevNode m l) ≤
        (m : ℝ) ^ 2 / (2 * (n : ℝ) * (l : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ hd (by positivity : 0 < 2 * (n : ℝ) * (l : ℝ) ^ 2)).mpr
      have h := mul_le_mul_of_nonneg_left hgap (sq_nonneg (m : ℝ))
      have hc : (m : ℝ) ^ 2 * (2 / (m : ℝ) ^ 2 * (l : ℝ) ^ 2) =
          2 * (l : ℝ) ^ 2 := by field_simp
      rw [hc] at h
      have hc' : (1 / (n : ℝ)) * (2 * (n : ℝ) * (l : ℝ) ^ 2) =
          2 * (l : ℝ) ^ 2 := by field_simp
      rwa [hc']
    have hr : (1 - roundedCosineNode n m l) / (1 - chebyshevNode m l) ≤
        1 + (1 / (n : ℝ)) / (1 - chebyshevNode m l) := by
      apply (div_le_iff₀ hd).mpr
      have hc : (1 + (1 / (n : ℝ)) / (1 - chebyshevNode m l)) *
          (1 - chebyshevNode m l) = 1 - chebyshevNode m l + 1 / (n : ℝ) := by
        field_simp
      rw [hc]
      linarith
    calc
      _ ≤ 1 + (m : ℝ) ^ 2 / (2 * (n : ℝ) * (l : ℝ) ^ 2) := by linarith
      _ ≤ _ := by
        simpa only [add_comm] using
          Real.add_one_le_exp ((m : ℝ) ^ 2 / (2 * (n : ℝ) * (l : ℝ) ^ 2))

/-- The first rounded interpolation weight retains the paper's quantitative endpoint mass. -/
theorem roundedWeight_zero_lower {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    (1 / (2 * (m : ℝ))) * Real.exp (-(Real.pi ^ 2 * (m : ℝ) ^ 2 / (12 * (n : ℝ)))) ≤
      roundedWeight n m 0 := by
  classical
  let s := (Finset.range (m + 1)).erase 0
  let cost := fun l : ℕ ↦ (m : ℝ) ^ 2 / (2 * (n : ℝ) * (l : ℝ) ^ 2)
  let ratio := fun l : ℕ ↦ (1 - roundedCosineNode n m l) / (1 - chebyshevNode m l)
  have hratio (l : ℕ) (hl : l ∈ s) : 0 < ratio l ∧ ratio l ≤ Real.exp (cost l) := by
    have hl' := Finset.mem_erase.mp hl
    exact roundedCosineNode_endpoint_ratio hm hn (by omega)
      (by have := Finset.mem_range.mp hl'.2; omega)
  have hp : 0 < ∏ l ∈ s, ratio l := Finset.prod_pos (fun l hl ↦ (hratio l hl).1)
  have hprod : (∏ l ∈ s, ratio l) ≤ Real.exp (∑ l ∈ s, cost l) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun l hl ↦ (hratio l hl).1.le)
      (fun l hl ↦ (hratio l hl).2)
  have hi : Real.exp (-(∑ l ∈ s, cost l)) ≤ (∏ l ∈ s, ratio l)⁻¹ := by
    have h := one_div_le_one_div_of_le hp hprod
    simpa only [one_div, Real.exp_neg] using h
  have hc (l : ℕ) (hl : l ∈ s) : chebyshevNode m 0 - chebyshevNode m l ≠ 0 := by
    have hl' := Finset.mem_erase.mp hl
    exact sub_ne_zero.mpr (chebyshevNode_ne hm (Nat.zero_le m)
      (by have := Finset.mem_range.mp hl'.2; omega) hl'.1.symm)
  have he : roundedWeight n m 0 = chebyshevWeight m 0 * (∏ l ∈ s, ratio l)⁻¹ := by
    rw [roundedWeight, interpolationWeight_perturbation _ (chebyshevNode m) hc,
      interpolationWeight_chebyshev hm (Nat.zero_le m)]
    simp only [roundedCosineNode_zero, chebyshevNode, Nat.cast_zero, zero_mul,
      zero_div, Real.cos_zero]
    rfl
  have hsum : (∑ l ∈ s, cost l) ≤ Real.pi ^ 2 * (m : ℝ) ^ 2 / (12 * (n : ℝ)) := by
    have hz : (∑ l ∈ s, 1 / (l : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 :=
      sum_le_hasSum _ (fun _ _ ↦ by positivity) hasSum_zeta_two
    have hf : (∑ l ∈ s, cost l) =
        ((m : ℝ) ^ 2 / (2 * (n : ℝ))) * ∑ l ∈ s, 1 / (l : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      dsimp [cost]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hf]
    have h := mul_le_mul_of_nonneg_left hz
      (show 0 ≤ (m : ℝ) ^ 2 / (2 * (n : ℝ)) by positivity)
    convert h using 1
    ring
  rw [he, ← chebyshevWeight_zero]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hsum))
    (chebyshevWeight_zero_pos hm).le).trans
      (mul_le_mul_of_nonneg_left hi (chebyshevWeight_zero_pos hm).le)

/-- In particular the actual endpoint weight is strictly positive. -/
theorem roundedWeight_zero_pos {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    0 < roundedWeight n m 0 :=
  (by positivity : 0 < (1 / (2 * (m : ℝ))) *
    Real.exp (-(Real.pi ^ 2 * (m : ℝ) ^ 2 / (12 * (n : ℝ))))).trans_le
      (roundedWeight_zero_lower hm hn)

/-- A rational certificate for the numerical exponential constant in Section 2.3. -/
theorem exp_neg_pi_sq_div_48_gt : (4 / 5 : ℝ) < Real.exp (-(Real.pi ^ 2 / 48)) := by
  have hπ : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have ht := Real.one_sub_le_exp_neg (Real.pi ^ 2 / 96)
  have hlin : (43 / 48 : ℝ) < Real.exp (-(Real.pi ^ 2 / 96)) := by linarith
  have hsq : (4 / 5 : ℝ) < Real.exp (-(Real.pi ^ 2 / 96)) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp (-(Real.pi ^ 2 / 96)) - 43 / 48)]
  have he : Real.exp (-(Real.pi ^ 2 / 96)) ^ 2 = Real.exp (-(Real.pi ^ 2 / 48)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rwa [he] at hsq

/-- The strict `2/(5m)` endpoint bound, with the paper's original constants. -/
theorem roundedWeight_zero_gt {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    2 / (5 * (m : ℝ)) < roundedWeight n m 0 := by
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : 4 * (m : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hr : (m : ℝ) ^ 2 / (n : ℝ) ≤ 1 / 4 :=
    (div_le_iff₀ hn').mpr (by linarith)
  have hc : Real.pi ^ 2 * (m : ℝ) ^ 2 / (12 * (n : ℝ)) ≤ Real.pi ^ 2 / 48 := by
    have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ Real.pi ^ 2 / 12 by positivity)
    convert h using 1 <;> ring
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    _ = (1 / (2 * (m : ℝ))) * (4 / 5) := by ring
    _ < (1 / (2 * (m : ℝ))) * Real.exp (-(Real.pi ^ 2 / 48)) :=
      mul_lt_mul_of_pos_left exp_neg_pi_sq_div_48_gt (by positivity)
    _ ≤ (1 / (2 * (m : ℝ))) *
        Real.exp (-(Real.pi ^ 2 * (m : ℝ) ^ 2 / (12 * (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hc)) (by positivity)
    _ ≤ _ := roundedWeight_zero_lower hm hn

end NoncommutativeAMGM
