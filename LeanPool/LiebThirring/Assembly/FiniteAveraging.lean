/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.ENNReal.Inv

/-!
# Finite product averaging

Product-of-sums identities and their first and second moments hold for extended nonnegative
coefficients.
-/

public section

open scoped ENNReal

namespace LiebThirring.Assembly

theorem sum_product_weights {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι]
    (w : ι → β → ℝ≥0∞) (hw : ∀ i, ∑ b, w i b = 1) :
    (∑ v : ι → β, ∏ i, w i (v i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [hw, Finset.prod_const_one]

theorem sum_product_weights_mul_product {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι]
    (w c : ι → β → ℝ≥0∞) :
    (∑ v : ι → β, (∏ i, w i (v i)) * (∏ i, c i (v i))) =
      ∏ i, ∑ b, w i b * c i b := by
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => w i b * c i b)).symm

theorem sum_product_weights_first {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι]
    (w c : ι → β → ℝ≥0∞) (hw : ∀ i, ∑ b, w i b = 1) (k : ι) :
    (∑ v : ι → β, (∏ i, w i (v i)) * c k (v k)) = ∑ b, w k b * c k b := by
  have hc (v : ι → β) : c k (v k) =
      ∏ i, if i = k then c i (v i) else 1 :=
    (Fintype.prod_ite_eq' k (fun i => c i (v i))).symm
  simp_rw [hc]
  rw [sum_product_weights_mul_product w (fun i b => if i = k then c i b else 1)]
  have hf (i : ι) : (∑ b, w i b * (if i = k then c i b else 1)) =
      if i = k then ∑ b, w i b * c i b else 1 := by
    split_ifs
    · rfl
    · simp only [mul_one, hw]
  simp_rw [hf]
  exact Fintype.prod_ite_eq' k _

theorem sum_product_weights_second {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι]
    (w c : ι → β → ℝ≥0∞) (hw : ∀ i, ∑ b, w i b = 1) (k l : ι) (hkl : k ≠ l) :
    (∑ v : ι → β, (∏ i, w i (v i)) * (c k (v k) * c l (v l))) =
      (∑ b, w k b * c k b) * (∑ b, w l b * c l b) := by
  have hc (v : ι → β) : c k (v k) * c l (v l) =
      ∏ i, (if i = k then c i (v i) else 1) *
        (if i = l then c i (v i) else 1) := by
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  simp_rw [hc]
  rw [sum_product_weights_mul_product w (fun i b =>
    (if i = k then c i b else 1) * (if i = l then c i b else 1))]
  have hf (i : ι) :
      (∑ b, w i b * ((if i = k then c i b else 1) *
        (if i = l then c i b else 1))) =
      (if i = k then ∑ b, w i b * c i b else 1) *
        (if i = l then ∑ b, w i b * c i b else 1) := by
    by_cases hik : i = k
    · subst i
      simp only [ite_true, hkl, ite_false, mul_one]
    · by_cases hil : i = l
      · subst i
        simp only [hik, ite_false, ite_true, one_mul]
      · simp only [hik, hil, ite_false, mul_one, hw]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']

end LiebThirring.Assembly

end
