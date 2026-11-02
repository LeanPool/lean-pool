/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Counting

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The minimum inventory size and tight degree bounds
-/

@[expose] public section
namespace MacMahon
open scoped BigOperators

lemma usable_count_identity (a : Inventory) (hz : DiagonalZero a)
    (i j : Label) (hij : i ≠ j) :
    usableCount a (i, j) + row a i + col a j + a (j, i) = total a + 2 * a (i, j) := by
  unfold usableCount
  simp_rw [usable_rule i j hij]
  simp only [DiagonalZero, Fin.forall_fin_succ] at hz
  fin_cases i <;> fin_cases j <;>
    norm_num [row, col, total, Fintype.sum_prod_type, Fin.sum_univ_succ] at * <;> omega

lemma universal_pair_bound (a : Inventory) (hz : DiagonalZero a) (h : Universal a)
    (i j : Label) (hij : i ≠ j) :
    row a i + col a j + a (j, i) + 8 ≤ total a + 2 * a (i, j) := by
  have := builds_usable_bound a i j hij (h i j hij)
  have := usable_count_identity a hz i j hij
  omega

lemma total_rows (a : Inventory) : total a = ∑ i, row a i := by
  simp [total, row, Fintype.sum_prod_type]
lemma total_cols (a : Inventory) : total a = ∑ j, col a j := by
  simp only [total, col, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma universal_row_bound (a : Inventory) (hz : DiagonalZero a) (h : Universal a)
    (i : Label) : 3 * row a i + 40 ≤ 4 * total a := by
  have hp := universal_pair_bound a hz h i
  have ht := total_cols a
  have hr : row a i = ∑ j, a (i, j) := rfl
  have hc : col a i = ∑ j, a (j, i) := rfl
  have hd := hz i
  fin_cases i <;> norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ] at * <;> omega

lemma universal_col_bound (a : Inventory) (hz : DiagonalZero a) (h : Universal a)
    (j : Label) : 3 * col a j + 40 ≤ 4 * total a := by
  have hp : ∀ i : Label, i ≠ j →
      row a i + col a j + a (j, i) + 8 ≤ total a + 2 * a (i, j) :=
    fun i hij => universal_pair_bound a hz h i j hij
  have ht := total_rows a
  have hr : row a j = ∑ i, a (j, i) := rfl
  have hc : col a j = ∑ i, a (i, j) := rfl
  have hd := hz j
  fin_cases j <;> norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ] at * <;> omega

theorem universal_minimum (a : Inventory) (hz : DiagonalZero a) (h : Universal a) :
    12 ≤ total a := by
  have hb := universal_row_bound a hz h
  have ht := total_rows a
  norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ] at hb ht
  omega

/-- If a finite sum attains the sum of pointwise upper bounds, all bounds are tight. -/
lemma eq_two_of_le_of_sum (f : Label → ℕ) (hb : ∀ i, f i ≤ 2)
    (hs : ∑ i, f i = 12) : ∀ i, f i = 2 := by
  have hh : (∑ i, f i) = ∑ _i : Label, 2 := by simpa using hs
  intro i
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hb j)).mp hh i (Finset.mem_univ i)

lemma rows_two (a : Inventory) (hz : DiagonalZero a) (h : Universal a)
    (ht : total a = 12) : ∀ i, row a i = 2 := by
  have hb : ∀ i, row a i ≤ 2 := by
    intro i
    have := universal_row_bound a hz h i
    omega
  exact eq_two_of_le_of_sum (row a) hb ((total_rows a).symm.trans ht)

lemma cols_two (a : Inventory) (hz : DiagonalZero a) (h : Universal a)
    (ht : total a = 12) : ∀ i, col a i = 2 := by
  have hb : ∀ i, col a i ≤ 2 := by
    intro i
    have := universal_col_bound a hz h i
    omega
  exact eq_two_of_le_of_sum (col a) hb ((total_cols a).symm.trans ht)

lemma reverse_bound (a : Inventory) (hz : DiagonalZero a) (h : Universal a)
    (ht : total a = 12) : ∀ i j, a (j, i) ≤ 2 * a (i, j) := by
  intro i j
  by_cases hij : i = j
  · subst j; omega
  have := universal_pair_bound a hz h i j hij
  rw [rows_two a hz h ht i, cols_two a hz h ht j, ht] at this
  omega

end MacMahon
