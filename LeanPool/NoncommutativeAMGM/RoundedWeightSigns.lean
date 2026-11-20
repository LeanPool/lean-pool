/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RoundedWeights

/-! # Alternating signs and exact variation identities for the rounded weights -/

@[expose] public section

namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

/-- Every relative gap is positive because both node lists have the same strict order. -/
theorem roundedCosineNode_gap_ratio_pos {n m j l : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hj : j ≤ m) (hl : l ≤ m) (hjl : j ≠ l) :
    0 < (roundedCosineNode n m j - roundedCosineNode n m l) /
      (chebyshevNode m j - chebyshevNode m l) := by
  have hn' : m ^ 2 < n := by nlinarith [sq_pos_of_pos hm]
  have hord {j l : ℕ} (hjl : j < l) (hl : l ≤ m) :
      0 < roundedCosineNode n m j - roundedCosineNode n m l ∧
        0 < chebyshevNode m j - chebyshevNode m l := by
    have ht := roundedCosineNode_strictAnti hm hn'
      (a := ⟨j, by omega⟩) (b := ⟨l, by omega⟩) hjl
    have hc := chebyshevNode_gap hm hjl.le hl
    have hdiff : 0 < (l : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjl)
    have hpos : 0 < 2 / (m : ℝ) ^ 2 * ((l : ℝ) - j) ^ 2 := by positivity
    exact ⟨sub_pos.mpr ht, hpos.trans_le hc⟩
  rcases lt_or_gt_of_ne hjl with h | h
  · obtain ⟨ht, hc⟩ := hord h hl
    exact div_pos ht hc
  · obtain ⟨ht, hc⟩ := hord h hj
    apply div_pos_of_neg_of_neg <;> linarith

/-- The perturbed weight has exactly the same alternating sign as the ideal one. -/
theorem roundedWeight_sign {n m j : ℕ} (hm : 0 < m)
    (hn : 4 * m ^ 2 ≤ n) (hj : j ≤ m) :
    roundedWeight n m j * (-1 : ℝ) ^ j = |roundedWeight n m j| := by
  classical
  let s := (Finset.range (m + 1)).erase j
  let ratio := fun l : ℕ ↦ (roundedCosineNode n m j - roundedCosineNode n m l) /
    (chebyshevNode m j - chebyshevNode m l)
  have hp : 0 < ∏ l ∈ s, ratio l := by
    apply Finset.prod_pos
    intro l hl
    have hl' := Finset.mem_erase.mp hl
    exact roundedCosineNode_gap_ratio_pos hm hn hj
      (by have := Finset.mem_range.mp hl'.2; omega) hl'.1.symm
  have hc (l : ℕ) (hl : l ∈ s) : chebyshevNode m j - chebyshevNode m l ≠ 0 := by
    have hl' := Finset.mem_erase.mp hl
    exact sub_ne_zero.mpr (chebyshevNode_ne hm hj
      (by have := Finset.mem_range.mp hl'.2; omega) hl'.1.symm)
  have he : roundedWeight n m j = chebyshevWeight m j * (∏ l ∈ s, ratio l)⁻¹ := by
    rw [roundedWeight, interpolationWeight_perturbation _ (chebyshevNode m) hc,
      interpolationWeight_chebyshev hm hj]
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hp)]
  calc
    _ = (chebyshevWeight m j * (-1 : ℝ) ^ j) * (∏ l ∈ s, ratio l)⁻¹ := by ring
    _ = _ := by rw [chebyshevWeight_sign]

/-- The variation excess is exactly the signed Chebyshev rounding error. -/
theorem roundedWeight_variation_identity {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    (∑ j ∈ Finset.range (m + 1), |roundedWeight n m j|) - 1 =
      -∑ j ∈ Finset.range (m + 1), roundedWeight n m j *
        ((Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j) -
          (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j)) := by
  have hn' : m ^ 2 < n := by nlinarith [sq_pos_of_pos hm]
  have hmoment := interpolationWeight_chebyshev_moment (m := m) (roundedCosineNode n m)
    (roundedCosineNode_injOn hm hn')
  have heval (j : ℕ) : (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j) = (-1 : ℝ) ^ j := by
    simpa only [chebyshevNode, Int.cast_negOnePow_natCast] using
      Chebyshev.eval_T_real_cos_int_mul_pi_div (k := j) hm.ne'
  simp_rw [heval, mul_sub, Finset.sum_sub_distrib]
  have hs : (∑ j ∈ Finset.range (m + 1), roundedWeight n m j * (-1 : ℝ) ^ j) =
      ∑ j ∈ Finset.range (m + 1), |roundedWeight n m j| := by
    apply Finset.sum_congr rfl
    intro j hj
    exact roundedWeight_sign hm hn (by have := Finset.mem_range.mp hj; omega)
  change (∑ j ∈ Finset.range (m + 1), |roundedWeight n m j|) - 1 =
    -((∑ j ∈ Finset.range (m + 1), interpolationWeight m (roundedCosineNode n m) j *
      (Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j)) - _)
  rw [hmoment, hs]
  ring

/-- Reduction of the total-variation excess to absolute Chebyshev rounding errors. -/
theorem roundedWeight_variation_le {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    (∑ j ∈ Finset.range (m + 1), |roundedWeight n m j|) - 1 ≤
      ∑ j ∈ Finset.range (m + 1), |roundedWeight n m j| *
        |(Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j) -
          (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j)| := by
  rw [roundedWeight_variation_identity hm hn]
  exact (neg_le_abs _).trans (by
    simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
      (s := Finset.range (m + 1))
      (f := fun j ↦ roundedWeight n m j *
        ((Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j) -
          (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j))))

end NoncommutativeAMGM
