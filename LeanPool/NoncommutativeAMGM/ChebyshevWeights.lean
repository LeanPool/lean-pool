/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.CosineQuadrature
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! # Appendix B: the exact normalized Chebyshev interpolation weights -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

/-- The monic nodal polynomial with the `j`th node omitted. -/
noncomputable def chebyshevNodalComplement (m j : ℕ) : Polynomial ℝ :=
  ∏ l ∈ (Finset.range (m + 1)).erase j, (Polynomial.X - C (chebyshevNode m l))

theorem chebyshevNodalComplement_natDegree {m j : ℕ} (hj : j ≤ m) :
    (chebyshevNodalComplement m j).natDegree = m := by
  rw [chebyshevNodalComplement, natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_erase_of_mem (by simp; omega), Finset.card_range]
  omega

theorem chebyshevNodalComplement_coeff {m j : ℕ} (hj : j ≤ m) :
    (chebyshevNodalComplement m j).coeff m = 1 := by
  have hdeg := chebyshevNodalComplement_natDegree hj
  calc
    _ = (chebyshevNodalComplement m j).coeff (chebyshevNodalComplement m j).natDegree := by
      rw [hdeg]
    _ = _ := by rw [coeff_natDegree]; exact (monic_prod_X_sub_C _ _).leadingCoeff

theorem chebyshevNodalComplement_eval_other {m j l : ℕ} (hl : l ≤ m) (hlj : l ≠ j) :
    (chebyshevNodalComplement m j).eval (chebyshevNode m l) = 0 := by
  classical
  rw [chebyshevNodalComplement, eval_prod]
  apply Finset.prod_eq_zero (i := l)
  · simp [hlj, Finset.mem_range, show l < m + 1 by omega]
  · simp

theorem chebyshevNodalComplement_eval_self (m j : ℕ) :
    (chebyshevNodalComplement m j).eval (chebyshevNode m j) =
      ∏ l ∈ (Finset.range (m + 1)).erase j, (chebyshevNode m j - chebyshevNode m l) := by
  simp [chebyshevNodalComplement, eval_prod]

/-- Applying the normalized quadrature to a Lagrange complement gives its nodal denominator. -/
theorem chebyshevWeight_mul_product {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    chebyshevWeight m j *
      (∏ l ∈ (Finset.range (m + 1)).erase j, (chebyshevNode m j - chebyshevNode m l)) =
        1 / (2 : ℝ) ^ (m - 1) := by
  have he := chebyshevWeight_extracts hm (chebyshevNodalComplement m j)
    (chebyshevNodalComplement_natDegree hj).le
  rw [chebyshevNodalComplement_coeff hj, Finset.sum_eq_single j] at he
  · simpa only [chebyshevNodalComplement_eval_self] using he
  · intro l hl hlj
    rw [chebyshevNodalComplement_eval_other (by have := Finset.mem_range.mp hl; omega) hlj,
      mul_zero]
  · simp [show j < m + 1 by omega]

/-- Appendix B's barycentric product formula, including the normalization `2^(1-m)`. -/
theorem chebyshevWeight_eq_product {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    chebyshevWeight m j = ((2 : ℝ) ^ (m - 1))⁻¹ /
      (∏ l ∈ (Finset.range (m + 1)).erase j, (chebyshevNode m j - chebyshevNode m l)) := by
  classical
  let D := ∏ l ∈ (Finset.range (m + 1)).erase j, (chebyshevNode m j - chebyshevNode m l)
  have he : chebyshevWeight m j * D = 1 / (2 : ℝ) ^ (m - 1) :=
    chebyshevWeight_mul_product hm hj
  have hD : D ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact one_div_ne_zero (pow_ne_zero _ (by norm_num)) he.symm
  calc
    chebyshevWeight m j = chebyshevWeight m j * D / D := by rw [mul_div_cancel_right₀ _ hD]
    _ = _ := by rw [he, one_div]

/-- The nodal-product weights are exactly the endpoint/interior closed forms in equation (22). -/
theorem chebyshev_interpolation_weights {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    ((2 : ℝ) ^ (m - 1))⁻¹ /
      (∏ l ∈ (Finset.range (m + 1)).erase j, (chebyshevNode m j - chebyshevNode m l)) =
      if j = 0 ∨ j = m then (-1 : ℝ) ^ j / (2 * (m : ℝ)) else (-1 : ℝ) ^ j / m := by
  rw [← chebyshevWeight_eq_product hm hj]
  by_cases h0 : j = 0
  · subst j
    simp [chebyshevWeight_zero]
  · by_cases he : j = m
    · subst j
      simp [chebyshevWeight_last]
    · rw [chebyshevWeight_interior (by omega) (by omega), ite_eq_right (by tauto)]

theorem cosineEndpointFactor_nonneg (m j : ℕ) : 0 ≤ cosineEndpointFactor m j := by
  unfold cosineEndpointFactor
  split_ifs <;> norm_num

theorem chebyshevWeight_abs (m j : ℕ) :
    |chebyshevWeight m j| = (1 / (m : ℝ)) * cosineEndpointFactor m j := by
  simp only [chebyshevWeight, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    Nat.abs_cast, abs_of_nonneg (cosineEndpointFactor_nonneg m j)]

theorem chebyshevWeight_sign (m j : ℕ) :
    chebyshevWeight m j * (-1 : ℝ) ^ j = |chebyshevWeight m j| := by
  rw [chebyshevWeight_abs]
  have hp : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul]; norm_num
  calc
    _ = ((-1 : ℝ) ^ j) ^ 2 / m * cosineEndpointFactor m j := by unfold chebyshevWeight; ring
    _ = _ := by rw [hp]

theorem chebyshevWeight_totalVariation {m : ℕ} (hm : 0 < m) :
    (∑ j ∈ Finset.range (m + 1), |chebyshevWeight m j|) = 1 := by
  have hdegree : (Chebyshev.T ℝ (m : ℤ)).natDegree = m := by simp [Chebyshev.natDegree_T]
  have hcoeff : (Chebyshev.T ℝ (m : ℤ)).coeff m = (2 : ℝ) ^ (m - 1) := by
    have he := coeff_natDegree (p := Chebyshev.T ℝ (m : ℤ))
    simpa only [hdegree, Chebyshev.leadingCoeff_T, Int.natAbs_natCast] using he
  have he := chebyshevWeight_extracts hm (Chebyshev.T ℝ (m : ℤ)) hdegree.le
  have heval (j : ℕ) : (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j) = (-1 : ℝ) ^ j := by
    simpa only [chebyshevNode, Int.cast_negOnePow_natCast] using
      Chebyshev.eval_T_real_cos_int_mul_pi_div (k := j) hm.ne'
  simp_rw [heval, chebyshevWeight_sign] at he
  simpa only [hcoeff, div_self (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))] using he

theorem chebyshevWeight_zero_pos {m : ℕ} (hm : 0 < m) : 0 < chebyshevWeight m 0 := by
  rw [chebyshevWeight_zero]
  positivity

/-- Exact endpoint saving of the ideal interpolation weights. -/
theorem chebyshevWeight_totalVariation_sub_endpoint {m : ℕ} (hm : 0 < m) :
    (∑ j ∈ Finset.range (m + 1), |chebyshevWeight m j|) - 2 * chebyshevWeight m 0 =
      1 - 1 / (m : ℝ) := by
  rw [chebyshevWeight_totalVariation hm, chebyshevWeight_zero]
  ring

end NoncommutativeAMGM
