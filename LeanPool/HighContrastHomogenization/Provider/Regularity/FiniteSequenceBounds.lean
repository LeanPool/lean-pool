/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.Euclidean
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# High-contrast homogenization: Provider.Regularity.FiniteSequenceBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite sequence bounds

This module records elementary finite-interval estimates used in multiscale
arguments.  The statements are independent of coefficient fields and PDEs.
-/

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators

/-- A contractive fixed-step recurrence bounds the full error sum by its
terminal block and the accumulated forcing. -/
theorem finiteStepErrorSum_le
    (N : ℕ) (hN : 0 < N) (E F : ℤ → ℝ) (C B : ℝ)
    {r m : ℤ} (_hrm : r ≤ m) (hE : ∀ j, 0 ≤ E j)
    (hF : ∀ j, 0 ≤ F j) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hstep : ∀ k ∈ Finset.Icc (r + (N : ℤ)) m,
      E (k - (N : ℤ)) ≤ (1 / 8 : ℝ) * E k + C * F k)
    (htop : ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j ≤ B) :
    ∑ j ∈ Finset.Icc r m, E j ≤
      2 * (B + C * ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k) := by
  classical
  by_cases hlong : r + (N : ℤ) ≤ m
  · have hsplit : Finset.Icc r (m - (N : ℤ)) ∪
        Finset.Ioc (m - (N : ℤ)) m = Finset.Icc r m := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc r (m - (N : ℤ)))
        (Finset.Ioc (m - (N : ℤ)) m) := by
      exact Finset.disjoint_left.2 fun j hj hj' ↦ by
        simp only [Finset.mem_Icc] at hj
        simp only [Finset.mem_Ioc] at hj'
        omega
    have hshift : (∑ k ∈ Finset.Icc (r + (N : ℤ)) m,
          E (k - (N : ℤ))) =
        ∑ j ∈ Finset.Icc r (m - (N : ℤ)), E j := by
      refine Finset.sum_bij (fun k _ ↦ k - (N : ℤ)) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_Icc] at hk ⊢
        omega
      · intro k₁ _ k₂ _ hk
        exact sub_left_injective hk
      · intro j hj
        refine ⟨j + (N : ℤ), ?_, by ring⟩
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro k _
        rfl
    have hsubset : Finset.Icc (r + (N : ℤ)) m ⊆ Finset.Icc r m :=
      Finset.Icc_subset_Icc (by omega) le_rfl
    have hsumE : (∑ k ∈ Finset.Icc (r + (N : ℤ)) m, E k) ≤
        ∑ j ∈ Finset.Icc r m, E j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j _ _ ↦ hE j)
    have hlower : (∑ j ∈ Finset.Icc r (m - (N : ℤ)), E j) ≤
        (1 / 8 : ℝ) * (∑ j ∈ Finset.Icc r m, E j) +
          C * ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k := by
      rw [← hshift]
      calc
        (∑ k ∈ Finset.Icc (r + (N : ℤ)) m, E (k - (N : ℤ))) ≤
            ∑ k ∈ Finset.Icc (r + (N : ℤ)) m,
              ((1 / 8 : ℝ) * E k + C * F k) :=
          Finset.sum_le_sum fun k hk ↦ hstep k hk
        _ = (1 / 8 : ℝ) * (∑ k ∈ Finset.Icc (r + (N : ℤ)) m, E k) +
              C * ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ (1 / 8 : ℝ) * (∑ j ∈ Finset.Icc r m, E j) +
              C * ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left hsumE (by norm_num : (0 : ℝ) ≤ 1 / 8)) _
    have htotal : (∑ j ∈ Finset.Icc r m, E j) ≤
        (1 / 8 : ℝ) * (∑ j ∈ Finset.Icc r m, E j) +
          C * ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k + B := by
      calc
        (∑ j ∈ Finset.Icc r m, E j) =
            (∑ j ∈ Finset.Icc r (m - (N : ℤ)), E j) +
              ∑ j ∈ Finset.Ioc (m - (N : ℤ)) m, E j := by
          rw [← hsplit, Finset.sum_union hdisj]
        _ ≤ (1 / 8 : ℝ) * (∑ j ∈ Finset.Icc r m, E j) +
              C * ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k + B :=
          add_le_add hlower htop
    have hsumF : 0 ≤ ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k :=
      Finset.sum_nonneg fun k _ ↦ hF k
    nlinarith only [htotal, hB, hC, hsumF]
  · have hsubset : Finset.Icc r m ⊆ Finset.Ioc (m - (N : ℤ)) m := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [Finset.mem_Ioc]
      omega
    have hshort : (∑ j ∈ Finset.Icc r m, E j) ≤ B :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j _ _ ↦ hE j)).trans htop
    have hsumF : 0 ≤ ∑ k ∈ Finset.Icc (r + (N : ℤ)) m, F k :=
      Finset.sum_nonneg fun k _ ↦ hF k
    nlinarith only [hshort, hB, hC, hsumF]

/-- The Euclidean norm of the first term of a finite sequence is bounded by
the terminal norm plus its successive differences. -/
theorem euclideanNorm_le_terminal_add_sum_adjacent
    {d : ℕ} (p : ℤ → Vec d) {r m : ℤ} (hrm : r ≤ m) :
    euclideanNorm (p r) ≤ euclideanNorm (p m) +
      ∑ j ∈ Finset.Ico r m, euclideanNorm (p j - p (j + 1)) := by
  have hadd {x y : Vec d} :
      euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
    rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
      euclideanNorm_eq_norm_ofVec]
    change ‖WithLp.toLp 2 (x + y)‖ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖
    rw [WithLp.toLp_add]
    exact norm_add_le _ _
  have hsum (S : Finset ℤ) (f : ℤ → Vec d) :
      euclideanNorm (∑ j ∈ S, f j) ≤ ∑ j ∈ S, euclideanNorm (f j) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        exact (hadd.trans (add_le_add_right ih _))
  have htel : (∑ j ∈ Finset.Ico r m, (p j - p (j + 1))) = p r - p m := by
    induction m, hrm using Int.leInduction with
    | base => simp
    | succ w hw ih =>
        rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hw
          (fun j ↦ p j - p (j + 1))]
        rw [ih]
        ring
  calc
    euclideanNorm (p r) = euclideanNorm ((p r - p m) + p m) := by
      congr 1
      abel
    _ ≤ euclideanNorm (p r - p m) + euclideanNorm (p m) := hadd
    _ = euclideanNorm (p m) + euclideanNorm
          (∑ j ∈ Finset.Ico r m, (p j - p (j + 1))) := by rw [htel]; ring
    _ ≤ euclideanNorm (p m) +
          ∑ j ∈ Finset.Ico r m, euclideanNorm (p j - p (j + 1)) :=
      add_le_add_right (hsum (Finset.Ico r m) (fun j ↦ p j - p (j + 1))) _

/-- The two adjacent copies of a nonnegative row over a half-open interval
are bounded by twice its sum over the closed interval. -/
theorem sum_adjacent_le_two_sum_Icc
    (E : ℤ → ℝ) {r m : ℤ} (_hrm : r ≤ m) (hE : ∀ j, 0 ≤ E j) :
    ∑ j ∈ Finset.Ico r m, (E j + E (j + 1)) ≤
      2 * ∑ j ∈ Finset.Icc r m, E j := by
  classical
  have hleft : ∑ j ∈ Finset.Ico r m, E j ≤ ∑ j ∈ Finset.Icc r m, E j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Icc_self)
      (fun j _ _ ↦ hE j)
  have hshift : (∑ j ∈ Finset.Ico r m, E (j + 1)) =
      ∑ k ∈ Finset.Ioc r m, E k := by
    refine Finset.sum_bij (fun j _ ↦ j + 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_Ioc]
      omega
    · intro j₁ _ j₂ _ hj
      exact add_left_injective (1 : ℤ) hj
    · intro k hk
      refine ⟨k - 1, ?_, by ring⟩
      simp only [Finset.mem_Ioc] at hk
      simp only [Finset.mem_Ico]
      omega
    · intro j _
      rfl
  have hright : ∑ j ∈ Finset.Ico r m, E (j + 1) ≤
      ∑ j ∈ Finset.Icc r m, E j := by
    rw [hshift]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.Ioc_subset_Icc_self
      (fun j _ _ ↦ hE j)
  rw [Finset.sum_add_distrib]
  nlinarith only [hleft, hright]

end HighContrast
end HCPolySupport
