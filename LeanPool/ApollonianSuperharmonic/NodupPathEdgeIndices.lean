/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Basic
public import Mathlib.Init

/-!
# Indices of an undirected edge in a list without repetitions

Shared list reasoning adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- The endpoints of an edge occurring consecutively in a list have consecutive indices. -/
theorem NodupPathEdgeIndices {α : Type*} [DecidableEq α] (p : List α) (hp : p.Nodup)
    (a b : α)
    (hedge : ∃ c d : α, ∃ l r : List α, p = l ++ c :: d :: r ∧
      ({a, b} : Finset α) = {c, d}) :
    p.idxOf a + 1 = p.idxOf b ∨ p.idxOf b + 1 = p.idxOf a := by
  classical
  rcases hedge with ⟨c, d, l, r, heq, hedge⟩
  have hnd := hp
  rw [heq, List.nodup_append] at hnd
  have hc : c ∉ l := by
    intro hc
    exact hnd.2.2 c hc c (by simp) rfl
  have hd : d ∉ l := by
    intro hd
    exact hnd.2.2 d hd d (by simp) rfl
  have hcd : c ≠ d := by
    have hcnot := (List.nodup_cons.mp hnd.2.1).1
    intro h
    exact hcnot (by simp [h])
  have hic : p.idxOf c = l.length := by
    simp [heq, List.idxOf_append, hc]
  have hid : p.idxOf d = l.length + 1 := by
    simp [heq, List.idxOf_append, hd, hcd, Nat.add_comm]
  have ha : a = c ∨ a = d := by
    have : a ∈ ({c, d} : Finset α) := by rw [← hedge]; simp
    simpa using this
  have hb : b = c ∨ b = d := by
    have : b ∈ ({c, d} : Finset α) := by rw [← hedge]; simp
    simpa using this
  have habne : a ≠ b := by
    intro h
    have hcmem : c ∈ ({a, b} : Finset α) := by rw [hedge]; simp
    have hdmem : d ∈ ({a, b} : Finset α) := by rw [hedge]; simp
    simp [h] at hcmem hdmem
    exact hcd (hcmem.trans hdmem.symm)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (habne rfl)
  · exact Or.inl (by rw [hic, hid])
  · exact Or.inr (by rw [hic, hid])
  · exact False.elim (habne rfl)

end ApollonianSuperharmonic

end
