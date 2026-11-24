/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.ComparisonTreeInsertion
public import LeanPool.ShellsortMean.HarvestOperationalAudit

/-! A fixed gap word acts on the labels of original slots. Its tree can
be built before assigning any values to these labels. -/
@[expose] public section

namespace Shellsort.ComparisonAudit
open HarvestBlockIteration HarvestOperationalAudit

/-- Execute a list of comparison trees in order and collect their outputs. -/
def collect {n : ℕ} {α : Type} : List (Tree n α) → Tree n (List α)
  | [] => .leaf []
  | x :: xs => x.bind fun a => (collect xs).bind fun l => .leaf (a :: l)

private theorem collect_spec {n : ℕ} {α : Type} (xs : List (Tree n α)) (p : RankPlacement n) :
    ((collect xs).run p).1 = xs.map (fun t => (t.run p).1) ∧
    ((collect xs).run p).2.length = (xs.map (fun t => (t.run p).2.length)).sum := by
  induction xs with
  | nil => simp [collect, Tree.run]
  | cons x xs ih => simp [collect, Tree.run_bind, Tree.run, ih.1, ih.2]

/-- The comparison tree for one gap pass, with outputs reassembled into slot order. -/
def passTree {n : ℕ} (a : Vector (Fin n) n) (h : {k : ℕ // 0 < k}) :
    Tree n (Vector (Fin n) n) :=
  let trees := List.ofFn fun s : Fin h.val => chainTree (physicalChain a h s)
  (collect trees).bind fun rows => .leaf (assembleChains a h (fun s => rows[s.val]?.getD []))

theorem passTree_spec {n : ℕ} (a : Vector (Fin n) n) (h : {k : ℕ // 0 < k})
    (p : RankPlacement n) :
    ((passTree a h).run p).1.map p.symm = (runPass (a.map p.symm) h).1 ∧
    ((passTree a h).run p).2.length = (runPass (a.map p.symm) h).2 := by
  let trees := List.ofFn fun s : Fin h.val => chainTree (physicalChain a h s)
  have scans := collect_spec trees p
  have chain (s : Fin h.val) := chainTree_spec (physicalChain a h s) p
  simp_rw [physicalChain_map] at chain
  constructor
  · apply Vector.ext
    intro i hi
    simp only [passTree, assembleChains, Tree.run_bind, Tree.run, Vector.getElem_map,
      Vector.getElem_ofFn]
    change p.symm (_[i / h.val]?.getD a[i]) = _
    rw [show ((collect trees).run p).1 = _ from scans.1]
    let s : Fin h.val := ⟨i % h.val, Nat.mod_lt _ h.property⟩
    have he : (trees.map (fun t => (t.run p).1))[s.val]? =
        some ((chainTree (physicalChain a h s)).run p).1 := by
      simp [trees, List.map_ofFn, s.isLt, Function.comp_def]
    rw [he]
    simp only [Option.getD_some]
    rw [← Option.getD_map p.symm, ← List.getElem?_map, (chain s).1]
    simp [runPass, assembleChains, s]
  · simp only [passTree, Tree.run_bind, Tree.run, List.append_nil]
    change ((collect trees).run p).2.length = _
    rw [scans.2]
    simp only [trees, List.map_ofFn, Function.comp_def, runPass, Vector.getElem_ofFn]
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext s
    exact (chain s).2

/-- The comparison tree for the complete execution of a predetermined gap word. -/
def wordTree {n : ℕ} (a : Vector (Fin n) n) : PositiveWord → Tree n (Vector (Fin n) n)
  | [] => .leaf a
  | h :: t => (passTree a h).bind fun b => wordTree b t

theorem wordTree_spec {n : ℕ} (a : Vector (Fin n) n) (w : PositiveWord) (p : RankPlacement n) :
    ((wordTree a w).run p).1.map p.symm = (runWord (a.map p.symm) w).1 ∧
    ((wordTree a w).run p).2.length = (runWord (a.map p.symm) w).2 := by
  induction w generalizing a with
  | nil => simp [wordTree, Tree.run, runWord]
  | cons h t ih =>
    have first := passTree_spec a h p
    have rest := ih ((passTree a h).run p).1
    rw [first.1] at rest
    simp [wordTree, Tree.run_bind, runWord, rest.1, rest.2, first.2]

theorem initial_wordTree {n : ℕ} (w : PositiveWord) (p : RankPlacement n) :
    ((wordTree (Vector.ofFn id) w).run p).1.map p.symm = (runWord (slots p) w).1 ∧
    ((wordTree (Vector.ofFn id) w).run p).2.length = ordinaryWordComparisons p w := by
  have sp := wordTree_spec (Vector.ofFn id) w p
  have start : (Vector.ofFn (id : Fin n → Fin n)).map p.symm = slots p := by
    simp [slots, Vector.map_ofFn]
  rw [start] at sp
  exact ⟨sp.1, sp.2.trans (congrArg Prod.snd (runWord_slots p w))⟩

end Shellsort.ComparisonAudit
