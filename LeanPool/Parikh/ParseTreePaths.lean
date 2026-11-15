/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.GrammarTrees

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Why simple trees have bounded height

A simple tree has no repeated production label along any downward path.
To turn this condition into a height bound, we need two facts: every path
label belongs to the tree's support, and some label path has length equal
to the tree's height. Terminals and holes contribute no production label.

This file proves those facts. `simple_height` in `Decomposition.lean` then
compares the longest path with the finite set of active nonterminals.

Source: `lem:simple-height`.
-/
namespace Parikh.ParseTree
variable {T N : Type*}

/-- Every production label on a path belongs to the tree's support. -/
theorem labelPath_subset_support (t : ParseTree T N) (path : List N)
    (hpath : path ∈ t.labelPaths) : ∀ A ∈ path, A ∈ t.support := by
  induction t using ParseTree.rec (motive_2 := fun cs =>
    ∀ c ∈ cs, ∀ path ∈ c.labelPaths, ∀ A ∈ path, A ∈ c.support) generalizing path with
  | terminal a =>
    simp only [labelPaths, List.mem_singleton] at hpath
    subst path
    simp
  | hole A =>
    simp only [labelPaths, List.mem_singleton] at hpath
    subst path
    simp
  | node r cs ih =>
    simp only [labelPaths, List.mem_cons, List.mem_map, ← List.flatMap_def,
      List.mem_flatMap] at hpath
    rcases hpath with rfl | ⟨tail, ⟨c, hc, htail⟩, rfl⟩
    · intro A hA
      have heq : A = r.input := by simpa using hA
      simp [support, productionLabels, heq]
    · intro A hA
      simp only [List.mem_cons] at hA
      rcases hA with rfl | hA
      · simp [support, productionLabels]
      · have hchild := ih c hc tail htail A hA
        simp only [support, productionLabels, Set.mem_ofPred_eq, List.mem_cons,
          ← List.flatMap_def, List.mem_flatMap]
        exact Or.inr ⟨c, hc, hchild⟩
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rename_i path hp A hA
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc path hp A hA
    · exact hcs d hd path hp A hA

/-- A longest production-label path realizes production height (`def:statistics`).
An empty-production node has the singleton root path; terminals and holes have the empty path. -/
theorem exists_labelPath_height (t : ParseTree T N) :
    ∃ path ∈ t.labelPaths, path.length = t.height := by
  induction t using ParseTree.rec (motive_2 := fun cs =>
    ∀ c ∈ cs, ∃ path ∈ c.labelPaths, path.length = c.height) with
  | terminal a => exact ⟨[], by simp [labelPaths], by simp [height]⟩
  | hole A => exact ⟨[], by simp [labelPaths], by simp [height]⟩
  | node r cs ih =>
    by_cases hcs : cs = []
    · subst cs
      exact ⟨[r.input], by simp [labelPaths], by simp [height]⟩
    · have hheights : cs.map height ≠ [] := fun h => hcs (List.map_eq_nil_iff.mp h)
      obtain ⟨c, hc, hmax⟩ := List.mem_map.mp (List.max_mem hheights)
      obtain ⟨path, hp, hlen⟩ := ih c hc
      refine ⟨r.input :: path, ?_, ?_⟩
      · simp only [labelPaths, List.mem_cons, List.mem_map, ← List.flatMap_def,
          List.mem_flatMap]
        exact Or.inr ⟨path, ⟨c, hc, hp⟩, rfl⟩
      · simp only [List.length_cons, height, List.foldl_max_eq_max hheights,
          Nat.zero_max, hlen, hmax]
        omega
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd

end Parikh.ParseTree
