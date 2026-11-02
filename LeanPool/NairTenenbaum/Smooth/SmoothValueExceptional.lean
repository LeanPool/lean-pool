/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.FixedSmoothCounting
public import LeanPool.NairTenenbaum.Contributions.ValueBoundContributions
public import LeanPool.NairTenenbaum.Smooth.SmoothValueRankin

/-! # Exceptional weighted contributions for the smoothness restriction -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem polynomial_small_values_nat_card_le {Q : ℤ[X]} (hQ : 0 < Q.natDegree)
    (S : Finset ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ((S.filter (fun n : ℕ => ((Q.eval (n : ℤ)).natAbs : ℝ) ≤ T)).card : ℝ) ≤
      2 * Q.natDegree * (T + 1) := by
  have H := polynomial_small_values_card_le hQ (S.image (fun n : ℕ => (n : ℤ))) hT
  rw [filter_image, card_image_of_injective _ (fun _ _ h => Int.natCast_inj.mp h)] at H
  exact H

theorem polynomial_fixed_smooth_nat_card_le {Q : ℤ[X]} (hQ : 0 < Q.natDegree)
    (S : Finset ℕ) (s : Finset ℕ) {η X : ℝ} (hη : 0 < η) (hX : 0 ≤ X) :
    ((S.filter (fun n : ℕ => (Q.eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers s ∧
      ((Q.eval (n : ℤ)).natAbs : ℝ) ≤ X)).card : ℝ) ≤
      (2 * Q.natDegree * fixedSmoothCountBound s η) * X ^ η := by
  have H := polynomial_fixed_smooth_card_le hQ (S.image (fun n : ℕ => (n : ℤ))) s hη hX
  rw [filter_image, card_image_of_injective _ (fun _ _ h => Int.natCast_inj.mp h)] at H
  exact H

theorem PolynomialSystem.original_dvd_total {k r : ℕ} (P : PolynomialSystem k r) (j : Fin k) :
    P.Q j ∣ P.total := Finset.dvd_prod_of_mem P.Q (mem_univ j)

theorem PolynomialSystem.original_degree_le_total {k r : ℕ} (P : PolynomialSystem k r) (j : Fin k) :
    (P.Q j).natDegree ≤ P.total.natDegree :=
  Polynomial.natDegree_le_of_dvd (P.original_dvd_total j) P.total_ne_zero

theorem PolynomialSystem.original_value_le_total {k r : ℕ} (P : PolynomialSystem k r)
    (j : Fin k) {t : ℤ} (ht : P.total.eval t ≠ 0) :
    ((P.Q j).eval t).natAbs ≤ (P.total.eval t).natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr ht)
    (Int.natAbs_dvd_natAbs.mpr (Polynomial.eval_dvd (P.original_dvd_total j)))

theorem PolynomialSystem.smallValues_sum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    (j : Fin k) (hj : 0 < (P.Q j).natDegree) (S : Finset ℕ) {x c T : ℝ}
    (hx : 0 ≤ x) (hT : 0 ≤ T)
    (hvalue : ∀ n ∈ S, ((P.total.eval (n : ℤ)).natAbs : ℝ) ≤ x ^ c) :
    (∑ n ∈ S.filter (fun n : ℕ => (((P.Q j).eval (n : ℤ)).natAbs : ℝ) ≤ T),
      extendArithmeticMap F (fun i => ((P.Q i).eval (n : ℤ)).natAbs)) ≤
      (2 * P.total.natDegree * (T + 1)) * (B * x ^ (c * σ) * F 1) := by
  have hW : 0 ≤ B * x ^ (c * σ) * F 1 := by positivity [hF.nonneg 1]
  have Hcard : ((S.filter (fun n : ℕ => (((P.Q j).eval (n : ℤ)).natAbs : ℝ) ≤ T)).card : ℝ) ≤
      2 * P.total.natDegree * (T + 1) := (polynomial_small_values_nat_card_le hj S hT).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast P.original_degree_le_total j) (by norm_num : (0 : ℝ) ≤ 2)) (by linarith))
  calc
    _ ≤ ∑ _n ∈ S.filter (fun n : ℕ => (((P.Q j).eval (n : ℤ)).natAbs : ℝ) ≤ T),
        B * x ^ (c * σ) * F 1 := Finset.sum_le_sum (fun n hn =>
      P.value_weight_le_of_value_bound hF hB hσ hx (hvalue n (mem_filter.mp hn).1))
    _ = _ := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right Hcard hW

theorem PolynomialSystem.fixedSmooth_sum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    (j : Fin k) (hj : 0 < (P.Q j).natDegree) (S s : Finset ℕ) {x c η : ℝ}
    (hx : 0 ≤ x) (hη : 0 < η)
    (hvalue : ∀ n ∈ S, ((P.total.eval (n : ℤ)).natAbs : ℝ) ≤ x ^ c) :
    (∑ n ∈ S.filter (fun n : ℕ => ((P.Q j).eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers s),
      extendArithmeticMap F (fun i => ((P.Q i).eval (n : ℤ)).natAbs)) ≤
      (2 * P.total.natDegree * fixedSmoothCountBound s η) *
        x ^ (c * η) * (B * x ^ (c * σ) * F 1) := by
  classical
  let V := S.filter (fun n : ℕ => ((P.Q j).eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers s)
  let U := V.filter (fun n : ℕ => P.total.eval (n : ℤ) ≠ 0)
  let W := B * x ^ (c * σ) * F 1
  have hW : 0 ≤ W := by dsimp [W]; positivity [hF.nonneg 1]
  have Hsum : (∑ n ∈ U, extendArithmeticMap F (fun i => ((P.Q i).eval (n : ℤ)).natAbs)) =
      ∑ n ∈ V, extendArithmeticMap F (fun i => ((P.Q i).eval (n : ℤ)).natAbs) := by
    apply Finset.sum_subset (filter_subset _ _)
    intro n hn hnU
    apply P.value_weight_eq_zero F
    by_contra h
    exact hnU (mem_filter.mpr ⟨hn, h⟩)
  have Hsubset : U ⊆ S.filter (fun n : ℕ => ((P.Q j).eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers s ∧
      (((P.Q j).eval (n : ℤ)).natAbs : ℝ) ≤ x ^ c) := by
    intro n hn
    obtain ⟨hnV, hnzero⟩ := mem_filter.mp hn
    obtain ⟨hnS, hns⟩ := mem_filter.mp hnV
    refine mem_filter.mpr ⟨hnS, hns, ?_⟩
    exact (show (((P.Q j).eval (n : ℤ)).natAbs : ℝ) ≤ (P.total.eval (n : ℤ)).natAbs by
      exact_mod_cast P.original_value_le_total j hnzero).trans (hvalue n hnS)
  have Hcard : (U.card : ℝ) ≤ (2 * P.total.natDegree * fixedSmoothCountBound s η) * x ^ (c * η) :=
      by
    have H := (show (U.card : ℝ) ≤ _ from Nat.cast_le.mpr (card_le_card Hsubset)).trans
      (polynomial_fixed_smooth_nat_card_le hj S s hη (Real.rpow_nonneg hx c))
    rw [← Real.rpow_mul hx] at H
    apply H.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx _)
    apply mul_le_mul_of_nonneg_right _ (fixedSmoothCountBound_pos s hη).le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast P.original_degree_le_total j) (by norm_num)
  change (∑ n ∈ V, _) ≤ _
  rw [← Hsum]
  calc
    _ ≤ ∑ _n ∈ U, W := Finset.sum_le_sum (fun n hn =>
      P.value_weight_le_of_value_bound hF hB hσ hx (hvalue n (mem_filter.mp (mem_filter.mp
          hn).1).1))
    _ = (U.card : ℝ) * W := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right Hcard hW

end NairTenenbaum
