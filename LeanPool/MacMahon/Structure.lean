/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.MacMahon.Definitions

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Symmetry of degree-two inventories
-/

@[expose] public section
namespace MacMahon
open scoped BigOperators

lemma entry_le_row (a : Inventory) (i j : Label) : a (i, j) ≤ row a i :=
  Finset.single_le_sum (f := fun j => a (i, j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-- Two unit entries exhaust a row of total multiplicity two. -/
lemma row_eq_of_two_unit_entries (a : Inventory) (i j k : Label) (hjk : j ≠ k)
    (hr : row a i = 2) (hj : a (i, j) = 1) (hk : a (i, k) = 1) :
    ∀ l, a (i, l) = if l = j ∨ l = k then 1 else 0 := by
  intro l
  by_cases hlj : l = j
  · subst l
    simp [hj]
  by_cases hlk : l = k
  · subst l
    simp [hk]
  have hsum : a (i, j) + a (i, k) + a (i, l) ≤ row a i := by
    simpa [row, Finset.sum_insert, hjk, Ne.symm hlj, Ne.symm hlk, Nat.add_assoc] using
      (Finset.sum_le_sum_of_subset (f := fun n : Label => a (i, n))
        (Finset.subset_univ ({j, k, l} : Finset Label)))
  simp only [hlj, hlk, or_self, ite_false]
  omega

/-- Degree two and reciprocal support force reciprocal multiplicities. -/
lemma symmetric_of_degree_two (a : Inventory)
    (hr : ∀ i, row a i = 2) (hc : ∀ i, col a i = 2)
    (hb : ∀ i j, a (j, i) ≤ 2 * a (i, j)) : ∀ i j, a (i, j) = a (j, i) := by
  have ht : ∀ i j, a (i, j) = 2 → a (j, i) = 2 := by
    intro i j hij
    have hzero : ∀ k, k ≠ j → a (k, i) = 0 := by
      intro k hkj
      have hsum : a (i, j) + a (i, k) ≤ row a i :=
        Finset.add_le_sum (f := fun j => a (i, j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          (Finset.mem_univ k) hkj.symm
      have := hb i k
      rw [hr i, hij] at hsum
      omega
    have hsum : col a i = a (j, i) :=
      Finset.sum_eq_single j (fun k _ hk => hzero k hk) (by simp)
    have := hc i
    omega
  intro i j
  have hi := entry_le_row a i j
  have hj := entry_le_row a j i
  rw [hr i] at hi
  rw [hr j] at hj
  have hb1 := hb i j
  have hb2 := hb j i
  have ht1 := ht i j
  have ht2 := ht j i
  omega
end MacMahon
