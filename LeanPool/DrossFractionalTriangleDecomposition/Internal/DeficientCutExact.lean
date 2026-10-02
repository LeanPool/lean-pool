/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.ExactScalar
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact deficient-cut averaging

Jensen's inequality turns the two per-edge cut inequalities into a scalar
contradiction at the exact 9/10 threshold.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

public theorem deficient_finish_exact {α : Type*} (A B : Finset α)
    (hA : A.Nonempty) (hB : B.Nonempty) (T : α → ℝ) (n m cc wΔ δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) (hn : 20 ≤ n) (hcc : 0 < cc)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - δ) - 3))
    (hcard : (A.card : ℝ) + (B.card : ℝ) = m)
    (hTA : ∀ e ∈ A, (1 - 2 * δ) * n ≤ T e ∧ T e ≤ n)
    (hTB : ∀ e ∈ B, (1 - 2 * δ) * n ≤ T e ∧ T e ≤ n)
    (mbound : 2 * m ≤ (1 - δ + 2 * δ ^ 2) * n ^ 2 + 4 + n - 6 * δ * n)
    (ineq1 : cc * (∑ e ∈ A, (T e * (T e - δ * n) / 2 - A.card)) < ∑ e ∈ A, (T e * wΔ - 1))
    (ineq2 : cc * (∑ e ∈ B, (T e * (T e - δ * n) / 2 - B.card)) < ∑ e ∈ B, (1 - T e * wΔ)) :
    False := by
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBcard : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  set T_A := (∑ e ∈ A, T e) / A.card with hT_A_def
  set T_B := (∑ e ∈ B, T e) / B.card with hT_B_def
  have hTA_lower : (1 - 2 * δ : ℝ) * n ≤ T_A := by
    have h : A.card • ((1 - 2 * δ : ℝ) * n) ≤ ∑ e ∈ A, T e :=
      Finset.card_nsmul_le_sum A T ((1 - 2 * δ : ℝ) * n) (fun e he => by linarith [(hTA e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (le_div_iff₀ hAcard).mpr h
  have hTA_upper : T_A ≤ n := by
    have h : ∑ e ∈ A, T e ≤ A.card • n :=
      Finset.sum_le_card_nsmul A T n (fun e he => (hTA e he).2)
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (div_le_iff₀ hAcard).mpr h
  have hTB_lower : (1 - 2 * δ : ℝ) * n ≤ T_B := by
    have h : B.card • ((1 - 2 * δ : ℝ) * n) ≤ ∑ e ∈ B, T e :=
      Finset.card_nsmul_le_sum B T ((1 - 2 * δ : ℝ) * n) (fun e he => by linarith [(hTB e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_B_def]
    exact (le_div_iff₀ hBcard).mpr h
  have hunivA := convex_avg hA (fun e => T e) (δ * n)
  have hunivB := convex_avg hB (fun e => T e) (δ * n)
  rw [← Finset.sum_div] at hunivA hunivB
  have ineq1' : cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) -
      (A.card : ℝ) * A.card) < (∑ e ∈ A, T e * wΔ) - A.card := by
    have lhs_eq : ∑ e ∈ A, (T e * (T e - δ * n) / 2 - (A.card : ℝ)) =
        (∑ e ∈ A, T e * (T e - δ * n) / 2) - A.card * A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ A, (T e * wΔ - 1) = (∑ e ∈ A, T e * wΔ) - A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [lhs_eq, rhs_eq] at ineq1
    exact ineq1
  have ineq2' : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) -
      (B.card : ℝ) * B.card) < (∑ e ∈ B, (1 : ℝ)) -
        (∑ e ∈ B, T e * wΔ) := by
    have lhs_eq : ∑ e ∈ B, (T e * (T e - δ * n) / 2 - (B.card : ℝ)) =
        (∑ e ∈ B, T e * (T e - δ * n) / 2) - B.card * B.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ B, (1 - T e * wΔ) = (∑ e ∈ B, (1 : ℝ)) - (∑ e ∈ B, T e * wΔ) := by
      rw [Finset.sum_sub_distrib]
    rw [lhs_eq, rhs_eq] at ineq2
    exact ineq2
  have ineq3 : cc * (T_A * (T_A - δ * n) / 2 - (A.card : ℝ)) < T_A * wΔ - 1 := by
    have hunivA_simp : T_A * (T_A - δ * n) ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card := by
      have h := hunivA
      simp only [hT_A_def] at h ⊢
      rw [le_div_iff₀ hAcard]
      linarith
    have h_quad_bound : T_A * (T_A - δ * n) / 2 ≤ (∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card := by
      have h1 : (∑ e ∈ A, T e * (T e - δ * n) / 2) = (∑ e ∈ A, T e * (T e - δ * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_A * (T_A - δ * n) ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card := hunivA_simp
      have h3 : T_A * (T_A - δ * n) / 2 ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have ineq1_div : cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) <
        T_A * wΔ - 1 := by
      have key : (cc * (∑ e ∈ A, T e * (T e - δ * n) / 2 - A.card * A.card)) / A.card <
          ((∑ e ∈ A, T e * wΔ) - A.card) / A.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ A, T e * (T e - δ * n) / 2 - A.card * A.card)) / A.card =
          cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hAcard)]
      have rhs_eq : ((∑ e ∈ A, T e * wΔ) - A.card) / A.card = T_A * wΔ - 1 := by
        rw [sub_div, div_self (ne_of_gt hAcard)]
        congr 1
        rw [← Finset.sum_mul]
        rw [hT_A_def, mul_div_assoc]
        ring
      linarith
    have h_le : cc * (T_A * (T_A - δ * n) / 2 - A.card) ≤
        cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq1_div]
  have ineq4 : cc * (T_B * (T_B - δ * n) / 2 - (B.card : ℝ)) < 1 - T_B * wΔ := by
    have hunivB_simp : T_B * (T_B - δ * n) ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card := by
      have h := hunivB
      simp only [hT_B_def] at h ⊢
      rw [le_div_iff₀ hBcard]
      linarith
    have h_quad_bound : T_B * (T_B - δ * n) / 2 ≤ (∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card := by
      have h1 : (∑ e ∈ B, T e * (T e - δ * n) / 2) = (∑ e ∈ B, T e * (T e - δ * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_B * (T_B - δ * n) ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card := hunivB_simp
      have h3 : T_B * (T_B - δ * n) / 2 ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have sumB_one : (∑ e ∈ B, (1 : ℝ)) = 1 * B.card := by simp
    have TBwΔ_eq : T_B * wΔ = (∑ e ∈ B, T e * wΔ) / B.card := by
      rw [hT_B_def]
      rw [← Finset.sum_mul]
      ring
    have ineq2_div : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) <
        (∑ e ∈ B, (1 : ℝ)) / B.card - T_B * wΔ := by
      have key : (cc * (∑ e ∈ B, T e * (T e - δ * n) / 2 - B.card * B.card)) / B.card <
          ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ B, T e * (T e - δ * n) / 2 - B.card * B.card)) / B.card =
          cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hBcard)]
      have rhs_eq : ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card =
          1 - T_B * wΔ := by
        rw [sub_div, sumB_one, one_mul, div_self (ne_of_gt hBcard), TBwΔ_eq]
      rw [lhs_eq, rhs_eq] at key
      convert key using 1
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have sumB_one' : (∑ e ∈ B, (1 : ℝ)) / B.card = 1 := by
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have ineq2_div' : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) /
        B.card - B.card) < 1 - T_B * wΔ := by
      simpa only [sumB_one'] using ineq2_div
    have h_le : cc * (T_B * (T_B - δ * n) / 2 - B.card) ≤
        cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq2_div']
  have hBcard_eq : (B.card : ℝ) = m - (A.card : ℝ) := by linarith
  have ineq4' : cc * (T_B * (T_B - δ * n) / 2 - (m - (A.card : ℝ))) < 1 - T_B * wΔ := by
    rw [hBcard_eq] at ineq4
    exact ineq4
  exact dross_3_4_to_false_exact n m (A.card : ℝ) cc wΔ T_A T_B δ
    hδ0 hδ1 hcc hccrel hn hTA_lower hTA_upper hTB_lower mbound ineq3 ineq4'

end LeanPool.DrossFractionalTriangleDecomposition
