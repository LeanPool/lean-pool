/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.GrammarTrees
import LeanPool.Parikh.ParseTreePaths
import Mathlib.Algebra.Order.Group.Nat

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Finding a small context inside a non-simple tree

A repeated label on a path suggests a removable cycle, but an arbitrary
choice could leave very large side branches in that cycle. We instead find
a minimal non-simple subtree: all its children are simple, so their heights
are bounded. A repeated occurrence of its root then determines a bounded cut.

These lemmas justify the selection, bounds, and reversible replacement used
by `bounded_cut`. Progress is measured by production nodes, because removing
a cycle need not shorten the terminal word.

Source: `lem:cut`.
-/
namespace Parikh
variable {T N : Type*}

namespace ParseTree

/-- Filling holes cannot reduce production height. -/
theorem height_le_height_plug (E t : ParseTree T N) : E.height ≤ (E.plug t).height := by
  induction E using ParseTree.rec (motive_2 := fun cs =>
    ∀ c ∈ cs, c.height ≤ (c.plug t).height) with
  | terminal a => simp [height, plug]
  | hole A => simp [height, plug]
  | node r cs ih =>
    simp only [plug, height, List.map_map, List.foldl_map]
    apply Nat.add_le_add_left
    exact List.foldl_rel (r := (· ≤ ·)) (Nat.le_refl 0)
      (fun c hc a b hab => max_le_max hab (ih c hc))
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd

/-- Replacement retains the selected position and can be undone exactly. -/
theorem subtree_replacement (t : ParseTree T N) (q : List ℕ) (u v : ParseTree T N)
    (hpos : t.subtree q = some u) :
    ∃ t', t.replaceAt q v = some t' ∧ t'.subtree q = some v ∧
      t'.replaceAt q u = some t := by
  induction q generalizing t with
  | nil =>
    simp only [subtree, Option.some.injEq] at hpos
    subst u
    exact ⟨v, rfl, rfl, rfl⟩
  | cons i q ih =>
    cases t with
    | terminal a => simp [subtree] at hpos
    | hole A => simp [subtree] at hpos
    | node r cs =>
      obtain ⟨c, hi, hpos⟩ := Option.bind_eq_some_iff.mp hpos
      obtain ⟨c', hreplace, hsub, hundo⟩ := ih c hpos
      obtain ⟨hlt, helem⟩ := List.getElem?_eq_some_iff.mp hi
      have hset : cs.set i c = cs := by
        rw [← helem]
        exact List.set_getElem_self hlt
      refine ⟨.node r (cs.set i c'), ?_, ?_, ?_⟩
      · simp [replaceAt, hi, hreplace]
      · simp [subtree, List.getElem?_set_self hlt, hsub]
      · simp [replaceAt, List.getElem?_set_self hlt, hundo, List.set_set, hset]

/-- A proper subtree has strictly fewer production nodes than its parent tree. -/
theorem productionSize_subtree_bound (t : ParseTree T N) (q : List ℕ)
    (u : ParseTree T N) (hpos : t.subtree q = some u) :
    u.productionSize ≤ t.productionSize ∧
      (q ≠ [] → u.productionSize < t.productionSize) := by
  induction q generalizing t with
  | nil =>
    simp only [subtree, Option.some.injEq] at hpos
    subst u
    exact ⟨le_rfl, by simp⟩
  | cons i q ih =>
    cases t with
    | terminal a => simp [subtree] at hpos
    | hole A => simp [subtree] at hpos
    | node r cs =>
      obtain ⟨c, hi, hpos⟩ := Option.bind_eq_some_iff.mp hpos
      have huc := (ih c hpos).1
      have hmem : c.productionSize ∈ cs.map productionSize :=
        List.mem_map_of_mem (List.mem_of_getElem? hi)
      have hsum := List.single_le_sum (fun n _ => Nat.zero_le n) _ hmem
      simp only [productionSize]
      constructor <;> omega

/-- With simple children, a non-simple node repeats its root in a child. -/
theorem exists_root_mem_child_support (r : ContextFreeRule T N)
    (cs : List (ParseTree T N)) (hs : ¬ (node r cs).Simple)
    (hc : ∀ c ∈ cs, c.Simple) : ∃ c ∈ cs, r.input ∈ c.support := by
  by_contra h
  apply hs
  intro path hp
  simp only [labelPaths, List.mem_cons, List.mem_map, ← List.flatMap_def,
    List.mem_flatMap] at hp
  rcases hp with rfl | ⟨tail, ⟨c, hcmem, htail⟩, rfl⟩
  · simp
  · apply List.nodup_cons.mpr
    refine ⟨?_, hc c hcmem tail htail⟩
    intro hA
    exact h ⟨c, hcmem, c.labelPath_subset_support tail htail r.input hA⟩

end ParseTree

/-- Descend through non-simple children until every child is simple. This selects
the source's minimal non-simple occurrence without a finite ambient alphabet. -/
theorem Complete.exists_minimal_nonsimple_subtree {g : ContextFreeGrammar T}
    {t : ParseTree T g.NT} (ht : Complete g t) (hs : ¬ t.Simple) :
    ∃ q r cs, t.subtree q = some (.node r cs) ∧ Complete g (.node r cs) ∧
      ¬ (ParseTree.node r cs).Simple ∧ ∀ c ∈ cs, c.Simple := by
  obtain ⟨hv, hh⟩ := ht
  induction hv with
  | terminal a => simp [ParseTree.Simple, ParseTree.labelPaths] at hs
  | hole A => simp [ParseTree.holes] at hh
  | node r cs hr hc roots ih =>
    have hholes : ∀ c ∈ cs, c.holes = [] := by
      simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
    by_cases hsimple : ∀ c ∈ cs, c.Simple
    · exact ⟨[], r, cs, rfl, ⟨.node r cs hr hc roots, hh⟩, hs, hsimple⟩
    · push Not at hsimple
      obtain ⟨c, hcmem, hcs⟩ := hsimple
      obtain ⟨q, r', cs', hq, ht', hs', hchildren⟩ :=
        ih c hcmem hcs (hholes c hcmem)
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcmem
      exact ⟨i :: q, r', cs', by simp [ParseTree.subtree, hi, hq], ht', hs', hchildren⟩

end Parikh
