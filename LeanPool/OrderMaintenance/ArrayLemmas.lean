/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: shared array lemmas are separated from tree preparation. -/

module

public import LeanPool.OrderMaintenance.Model.State

/-!
# Total array views

Generic total-map facts depend only on the state-level array operations. Both functional
correctness and RAM encoding reuse them without importing one another.
-/

@[expose] public section

namespace OrderMaintenance.Proof

/-! ### Arrays as total maps -/

section arrays
variable {α : Type} [Inhabited α]

theorem Array.getX_def (a : Array α) (i : Nat) : a.getX i = a.getD i default := rfl

@[simp] theorem Array.getX_modify (a : Array α) (i j : Nat) (f : α → α) :
    (a.modify i f).getX j = if i = j ∧ i < a.size then f (a.getX j) else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size <;> simp [hi]
  · simp [hij]

omit [Inhabited α] in
theorem Array.size_modify' (a : Array α) (i : Nat) (f : α → α) :
    (a.modify i f).size = a.size := Array.size_modify

@[simp] theorem Array.getX_push (a : Array α) (v : α) (j : Nat) :
    (a.push v).getX j = if j = a.size then v else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : j = a.size <;> simp [h]

theorem Array.getX_set! (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v).getX j = if i = j ∧ i < a.size then v else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij; by_cases hi : i < a.size <;> simp [hi]
  · simp [hij]

@[simp] theorem Array.getX_setIfInBounds (a : Array α) (i j : Nat) (v : α) :
    (a.setIfInBounds i v).getX j = if i = j ∧ i < a.size then v else a.getX j := by
  rw [← Array.set!_eq_setIfInBounds]; exact Array.getX_set! a i j v

omit [Inhabited α] in
theorem Array.size_set!' (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by simp

@[simp] theorem Array.getX_ite {c : Prop} [Decidable c] (a b : Array α) (i : Nat) :
    (if c then a else b).getX i = if c then a.getX i else b.getX i := by split <;> rfl

omit [Inhabited α] in
@[simp] theorem Array.size_ite {c : Prop} [Decidable c] (a b : Array α) :
    (if c then a else b).size = if c then a.size else b.size := by split <;> rfl

theorem Array.getX_ge (a : Array α) {j : Nat} (h : a.size ≤ j) : a.getX j = default := by
  simp [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

end arrays


theorem Array.getX_setX {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) :
    (a.setX i v).getX j = if j = i then v else a.getX j := by
  unfold Array.setX Array.getX
  split
  · simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
    by_cases h : j = i
    · subst h; simp [*]
    · simp [Ne.symm h, h]
  · rename_i hi
    have hs : (a ++ Array.replicate (i - a.size) (default : α)).size = i := by simp; omega
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
    by_cases h : j = i
    · simp [h]
    · rw [ite_eq_right h, ite_eq_right h, Array.getElem?_append]
      by_cases hj : j < a.size
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj, Array.getElem?_eq_none (by omega : a.size ≤ j),
        Array.getElem?_replicate]
        split <;> rfl


/-- Updating a total array grows it exactly far enough to contain the updated index. -/
theorem Array.size_setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = if i < a.size then a.size else i + 1 := by
  unfold Array.setX
  split
  · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  · simp only [Array.push_append, Array.size_append, Array.size_push, Array.size_replicate]; omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof

theorem getX_push' {α : Type} [Inhabited α] (a : Array α) (x : α) (i : Nat) :
    (a.push x).getX i = if i = a.size then x else a.getX i :=
  OrderMaintenance.Proof.Array.getX_push a x i

theorem size_setX' {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = max a.size (i + 1) := by
  rw [OrderMaintenance.Proof.Array.size_setX]
  split <;> omega

theorem getX_setX' {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) (j : Nat) :
    (a.setX i v).getX j = if j = i then v else a.getX j :=
  OrderMaintenance.Proof.Array.getX_setX a i j v

theorem getX_modify' {α : Type} [Inhabited α] (a : Array α) (f : α → α) (i j : Nat) :
    (a.modify i f).getX j = if j = i ∧ i < a.size then f (a.getX j) else a.getX j := by
  simpa only [eq_comm] using (OrderMaintenance.Proof.Array.getX_modify a i j f)

end OrderMaintenance.Proof.Top
