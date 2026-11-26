/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.Fin.Basic

/-!
# Points of a finite parameter subdivision

The trace definition in XII, page 243, lists all vertex parameters
and the intervening open intervals. Every point between the first
and last parameters is either an entry of the list or belongs to
one of those intervals. Remove the first interval and repeat to
prove this coverage. It is used to read the original curve image
as its vertex visits together with its region visits.
-/

public section

namespace GraphMinor.GM12

open Set

/-- A finite real-parameter subdivision covers its closed interval
by its entries and its successive open intervals. The assertion
holds in any linear order. -/
theorem mem_range_or_mem_successive_open_interval
    {α : Type*} [LinearOrder α] {n : ℕ} (t : Fin (n + 1) → α)
    {s : α} (hs : s ∈ Icc (t 0) (t (Fin.last n))) :
    s ∈ range t ∨ ∃ i : Fin n, s ∈ Ioo (t i.castSucc) (t i.succ) := by
  induction n with
  | zero =>
    left
    exact ⟨0, (le_antisymm hs.2 hs.1).symm⟩
  | succ n ih =>
    by_cases hs0 : s = t 0
    · exact Or.inl ⟨0, hs0.symm⟩
    · by_cases hs1 : s = t (0 : Fin (n + 1)).succ
      · exact Or.inl ⟨(0 : Fin (n + 1)).succ, hs1.symm⟩
      · by_cases hst : s ≤ t (0 : Fin (n + 1)).succ
        · exact Or.inr ⟨0, lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hst hs1⟩
        · let t' : Fin (n + 1) → α := fun i => t i.succ
          have hs' : s ∈ Icc (t' 0) (t' (Fin.last n)) :=
            ⟨(lt_of_not_ge hst).le, hs.2⟩
          rcases ih t' hs' with h | ⟨i, hi⟩
          · obtain ⟨i, hi⟩ := h
            exact Or.inl ⟨i.succ, hi⟩
          · exact Or.inr ⟨i.succ, hi⟩

end GraphMinor.GM12
