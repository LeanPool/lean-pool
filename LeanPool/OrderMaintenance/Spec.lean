/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module


/-!
# The list specification

The order-maintenance problem (`docs/PROOF.md` §1) as a pure function on lists. Theorem A
states that the machine program answers every operation as `Spec.run` does.

Elements are named by creation time: the `k`-th insertion (counting from 0) creates element
`k`. An implementation hands out its own handles; the correctness theorem relates them to these
names through the client's record of which handle each insertion returned.
-/


@[expose] public section

namespace OrderMaintenance.Spec

/-- Fresh natural-number names used by the list specification. -/
abbrev Elem := Nat

/-- External insertion, deletion and order-comparison operations. -/
inductive Op where
  | insertFirst
  | insertAfter (x : Elem)
  | delete (x : Elem)
  | order (x y : Elem)
  deriving DecidableEq, Repr

/-- Observable answers returned by specification operations. -/
inductive Ans where
  | inserted
  | deleted
  | bool (b : Bool)
  deriving DecidableEq, Repr

/-- The ordered live element list and its next fresh name. -/
structure State where
  /-- Live element names in their current order. -/
  list : List Elem
  /-- The name of the next inserted element. -/
  fresh : Nat
  deriving DecidableEq, Repr

/-- The empty ordered list with fresh names starting at zero. -/
def State.empty : State := ⟨[], 0⟩

/-- Insert `y` immediately after the first occurrence of `x`. -/
def insertAfterL (x y : Elem) : List Elem → List Elem
  | [] => []
  | a :: l => if a = x then a :: y :: l else a :: insertAfterL x y l

/-- Does `x` occur before `y`? -/
def precedes (l : List Elem) (x y : Elem) : Bool := decide (l.idxOf x < l.idxOf y)

/-- Preconditions (`PROOF.md` §1): every argument is a live element. -/
def Op.Valid (s : State) : Op → Prop
  | .insertFirst => True
  | .insertAfter x => x ∈ s.list
  | .delete x => x ∈ s.list
  | .order x y => x ∈ s.list ∧ y ∈ s.list

/-- Execute one specification operation and return its state and answer. -/
def step (s : State) : Op → State × Ans
  | .insertFirst => (⟨s.fresh :: s.list, s.fresh + 1⟩, .inserted)
  | .insertAfter x => (⟨insertAfterL x s.fresh s.list, s.fresh + 1⟩, .inserted)
  | .delete x => (⟨s.list.erase x, s.fresh⟩, .deleted)
  | .order x y => (s, .bool (precedes s.list x y))

/-- The state after a sequence of operations. -/
def final (s : State) : List Op → State
  | [] => s
  | op :: ops => final (step s op).1 ops

/-- The answers to a sequence of operations. -/
def run (s : State) : List Op → List Ans
  | [] => []
  | op :: ops => (step s op).2 :: run (step s op).1 ops

/-- Every operation of the sequence is valid in the state where it is issued. -/
def Valid (s : State) : List Op → Prop
  | [] => True
  | op :: ops => op.Valid s ∧ Valid (step s op).1 ops

/-! ### Basic invariant: distinct elements, all named below `fresh` -/

/-- Live names are distinct and smaller than the next fresh name. -/
def Inv (s : State) : Prop := s.list.Nodup ∧ ∀ e ∈ s.list, e < s.fresh

theorem mem_insertAfterL {x y e : Elem} {l : List Elem} (hx : x ∈ l) :
    e ∈ insertAfterL x y l ↔ e = y ∨ e ∈ l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [insertAfterL]
    split
    · grind
    · have hx' : x ∈ l := by grind
      grind

theorem nodup_insertAfterL {x y : Elem} {l : List Elem} (hx : x ∈ l) (hy : y ∉ l)
    (hl : l.Nodup) : (insertAfterL x y l).Nodup := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [insertAfterL]
    split
    · grind
    · have hx' : x ∈ l := by grind
      have := mem_insertAfterL (y := y) (e := a) hx'
      grind

theorem step_inv {s : State} {op : Op} (h : Inv s) (hv : op.Valid s) : Inv (step s op).1 := by
  rcases h with ⟨hn, hf⟩
  cases op with
  | insertFirst =>
    have : s.fresh ∉ s.list := fun hm => Nat.lt_irrefl _ (hf _ hm)
    simp only [step, Inv]
    grind
  | insertAfter x =>
    have hfr : s.fresh ∉ s.list := fun hm => Nat.lt_irrefl _ (hf _ hm)
    refine ⟨nodup_insertAfterL hv hfr hn, ?_⟩
    intro e he
    rcases (mem_insertAfterL hv).1 he with rfl | he
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hf e he)
  | delete x =>
    exact ⟨hn.erase x, fun e he => hf e (List.mem_of_mem_erase he)⟩
  | order x y => exact ⟨hn, hf⟩

theorem final_inv {s : State} {ops : List Op} (h : Inv s) (hv : Valid s ops) :
    Inv (final s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih (step_inv h hv.1) hv.2

end OrderMaintenance.Spec
