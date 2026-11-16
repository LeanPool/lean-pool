/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: shared array lemmas are separated from tree preparation. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Monad

/-!
# Total array views

These lemmas sit below tree preparation so RAM encoding can reuse them without importing
its correctness proofs.
-/

@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof

theorem getX_push' {α : Type} [Inhabited α] (a : Array α) (x : α) (i : Nat) :
    (a.push x).getX i = if i = a.size then x else a.getX i := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

theorem size_setX' {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = max a.size (i + 1) := by
  unfold Array.setX
  split
  · simp; omega
  · simp; omega

theorem getX_setX' {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) (j : Nat) :
    (a.setX i v).getX j = if j = i then v else a.getX j := by
  unfold Array.setX
  split
  · next hi =>
    simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
    by_cases hj : i = j
    · subst hj; simp [hi]
    · simp [hj, Ne.symm hj]
  · next hi =>
    rw [getX_push']
    have hs : (a ++ Array.replicate (i - a.size) default).size = i := by simp; omega
    rw [hs]
    by_cases hj : j = i
    · rw [ite_eq_left hj, ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right hj]
      simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_append]
      split
      · rfl
      · rw [Array.getElem?_replicate]
        split
        · simp; rw [Array.getElem?_eq_none (by omega)]; rfl
        · rw [Array.getElem?_eq_none (by omega)]

theorem getX_modify' {α : Type} [Inhabited α] (a : Array α) (f : α → α) (i j : Nat) :
    (a.modify i f).getX j = if j = i ∧ i < a.size then f (a.getX j) else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases e : i = j
  · subst e
    by_cases hi : i < a.size
    · simp [hi]
    · rw [ite_eq_right (show ¬(i = i ∧ i < a.size) from fun h => hi h.2),
      Array.getElem?_eq_none (by omega)]; simp
  · rw [ite_eq_right (show ¬(j = i ∧ i < a.size) from fun h => e h.1.symm)]; simp [e]

end OrderMaintenance.Proof.Top
