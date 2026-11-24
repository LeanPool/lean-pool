/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.InsertionComparisons
public import LeanPool.ShellsortMean.PermutationGeometry

/-! A deterministic comparison tree acts on original slot labels. Only a question
node can inspect their ordering. The input permutation is an argument of the
interpreter, never an argument of the tree builder. -/
@[expose] public section

namespace Shellsort.ComparisonAudit

/-- A finite comparison tree whose queries name the original slots of two keys. -/
inductive Tree (n : ℕ) (α : Type) where
  | leaf (value : α)
  | ask (i j : Fin n) (yes no : Tree n α)

namespace Tree

/-- Continue each leaf with the comparison tree chosen by its output. -/
def bind {n : ℕ} {α β : Type} (t : Tree n α) (next : α → Tree n β) : Tree n β :=
  match t with
  | .leaf a => next a
  | .ask i j yes no => .ask i j (yes.bind next) (no.bind next)

/-- Run the comparisons on a rank placement and record the answers in order. -/
def run {n : ℕ} {α : Type} (t : Tree n α) (p : RankPlacement n) : α × List Bool :=
  match t with
  | .leaf a => (a, [])
  | .ask i j yes no =>
    if p.symm i < p.symm j then
      let z := yes.run p
      (z.1, true :: z.2)
    else
      let z := no.run p
      (z.1, false :: z.2)

theorem run_bind {n : ℕ} {α β : Type} (t : Tree n α) (next : α → Tree n β)
    (p : RankPlacement n) :
    (t.bind next).run p =
      (((next (t.run p).1).run p).1, (t.run p).2 ++ ((next (t.run p).1).run p).2) := by
  induction t with
  | leaf a => simp [bind, run]
  | ask i j yes no hy hn =>
    by_cases h : p.symm i < p.symm j <;> simp [bind, run, h, hy, hn]

end Tree

/-- The comparison tree for inserting one slot label into a reversed sorted chain. -/
def insertTree {n : ℕ} (x : Fin n) : List (Fin n) → Tree n (List (Fin n))
  | [] => .leaf [x]
  | b :: l => .ask x b
      ((insertTree x l).bind fun tail => .leaf (b :: tail))
      (.leaf (x :: b :: l))

theorem insertTree_spec {n : ℕ} (x : Fin n) (l : List (Fin n)) (p : RankPlacement n) :
    ((insertTree x l).run p).1.map p.symm = (insertCompared (p.symm x) (l.map p.symm)).output ∧
    ((insertTree x l).run p).2.length = (insertCompared (p.symm x) (l.map p.symm)).comparisons := by
  induction l with
  | nil => simp [insertTree, Tree.run, insertCompared]
  | cons b l ih =>
    by_cases h : p.symm x < p.symm b <;>
      simp [insertTree, Tree.run, Tree.run_bind, insertCompared, h, ih.1, ih.2]

/-- Symbolic insertion processes the chain in increasing physical slot order,
carrying the sorted portion backwards for comparison with its last element. -/
def chainBack {n : ℕ} (l : List (Fin n)) : Tree n (List (Fin n)) :=
  List.reverseRec (motive := fun _ => Tree n (List (Fin n))) (.leaf [])
    (fun _ x old => old.bind (insertTree x)) l

theorem chainBack_spec {n : ℕ} (l : List (Fin n)) (p : RankPlacement n) :
    ((chainBack l).run p).1.map p.symm = (insertionComparedBack (l.map p.symm)).output ∧
    ((chainBack l).run p).2.length = (insertionComparedBack (l.map p.symm)).comparisons := by
  induction l using List.reverseRecOn with
  | nil => simp [chainBack, Tree.run, insertionComparedBack_nil]
  | append_singleton l a ih =>
    have next := insertTree_spec a ((chainBack l).run p).1 p
    rw [ih.1] at next
    have step : chainBack (l ++ [a]) = (chainBack l).bind (insertTree a) := by
      simp [chainBack, List.reverseRec_concat]
    simp [step, Tree.run_bind, insertionComparedBack_append, next.1, next.2, ih.2]

/-- The comparison tree for insertion-sorting a chain of original slot labels. -/
def chainTree {n : ℕ} (l : List (Fin n)) : Tree n (List (Fin n)) :=
  (chainBack l).bind fun z => .leaf z.reverse

theorem chainTree_spec {n : ℕ} (l : List (Fin n)) (p : RankPlacement n) :
    ((chainTree l).run p).1.map p.symm = (insertionComparedExecution (l.map p.symm)).output ∧
    ((chainTree l).run p).2.length = (insertionComparedExecution (l.map p.symm)).comparisons := by
  have back := chainBack_spec l p
  simp [chainTree, Tree.run_bind, Tree.run, insertionComparedExecution, List.map_reverse, back.1,
    back.2]

end Shellsort.ComparisonAudit
