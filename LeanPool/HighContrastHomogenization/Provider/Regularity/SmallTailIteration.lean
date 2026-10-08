/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Int.Interval
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# High-contrast homogenization: Provider.Regularity.SmallTailIteration

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators

/-- A nonnegative recurrence with a sufficiently small accumulated tail is
uniformly controlled by its terminal value. -/
theorem smallTail_interval_bound
    {n m : ℤ} (C : ℝ) (D E : ℤ → ℝ)
    (hnm : n ≤ m) (hC : 1 ≤ C)
    (hD : ∀ j ∈ Finset.Icc n m, 0 ≤ D j)
    (hE : ∀ j ∈ Finset.Icc n m, 0 ≤ E j)
    (hrec : ∀ h ∈ Finset.Icc n m,
      D h ≤ C * D m + C * ∑ j ∈ Finset.Ioc h m, E j * D j)
    (hsmall : ∑ j ∈ Finset.Icc n m, E j ≤ (2 * C)⁻¹) :
    ∀ h ∈ Finset.Icc n m, D h ≤ 2 * C * D m := by
  classical
  let S : Finset ℤ := Finset.Icc n m
  have hS : S.Nonempty := by
    exact ⟨m, by simp [S, hnm]⟩
  let M : ℝ := S.sup' hS D
  have hD_le_M : ∀ j ∈ S, D j ≤ M := by
    intro j hj
    exact Finset.le_sup' (f := D) hj
  have hM_nonneg : 0 ≤ M := by
    exact (hD m (by simp [hnm])).trans (hD_le_M m (by simp [S, hnm]))
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have htail_subset (h : ℤ) (hh : h ∈ S) : Finset.Ioc h m ⊆ S := by
    intro j hj
    have hj' : h < j ∧ j ≤ m := by simpa using hj
    have hh' : n ≤ h ∧ h ≤ m := by simpa [S] using hh
    simp [S, le_trans hh'.1 hj'.1.le, hj'.2]
  have htail_small (h : ℤ) (hh : h ∈ S) :
      ∑ j ∈ Finset.Ioc h m, E j ≤ (2 * C)⁻¹ := by
    calc
      ∑ j ∈ Finset.Ioc h m, E j ≤ ∑ j ∈ S, E j := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (htail_subset h hh)
          (fun j hjS _ => hE j hjS)
      _ ≤ (2 * C)⁻¹ := by simpa [S] using hsmall
  have hsum_mul_le (h : ℤ) (hh : h ∈ S) :
      ∑ j ∈ Finset.Ioc h m, E j * D j ≤
        M * ∑ j ∈ Finset.Ioc h m, E j := by
    calc
      ∑ j ∈ Finset.Ioc h m, E j * D j ≤
          ∑ j ∈ Finset.Ioc h m, E j * M := by
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left
            (hD_le_M j (htail_subset h hh (by simpa using hj)))
            (hE j (htail_subset h hh (by simpa using hj)))
      _ = M * ∑ j ∈ Finset.Ioc h m, E j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hpoint (h : ℤ) (hh : h ∈ S) :
      D h ≤ C * D m + M / 2 := by
    have hrec' := hrec h (by simpa [S] using hh)
    have hsum := hsum_mul_le h hh
    have hsumC :
        C * ∑ j ∈ Finset.Ioc h m, E j * D j ≤
          C * (M * ∑ j ∈ Finset.Ioc h m, E j) :=
      mul_le_mul_of_nonneg_left hsum hC_pos.le
    have htailM :
        M * ∑ j ∈ Finset.Ioc h m, E j ≤ M * (2 * C)⁻¹ :=
      mul_le_mul_of_nonneg_left (htail_small h hh) hM_nonneg
    have hcancel : C * (M * (2 * C)⁻¹) = M / 2 := by
      field_simp [hC_pos.ne']
    calc
      D h ≤ C * D m + C * ∑ j ∈ Finset.Ioc h m, E j * D j := hrec'
      _ ≤ C * D m + C * (M * ∑ j ∈ Finset.Ioc h m, E j) :=
        add_le_add (le_refl _) hsumC
      _ ≤ C * D m + C * (M * (2 * C)⁻¹) := by
        gcongr
      _ = C * D m + M / 2 := by rw [hcancel]
  have hM_bound : M ≤ 2 * C * D m := by
    obtain ⟨h, hh, hMh⟩ := Finset.exists_mem_eq_sup' hS D
    have hp := hpoint h hh
    have hDm_nonneg : 0 ≤ D m := hD m (by simp [hnm])
    have hMh' : M = D h := by simpa [M] using hMh
    rw [hMh'] at hp ⊢
    linarith only [hp, hDm_nonneg]
  intro h hh
  exact (hD_le_M h (by simpa [S] using hh)).trans hM_bound

end HighContrast
end HCPolySupport
