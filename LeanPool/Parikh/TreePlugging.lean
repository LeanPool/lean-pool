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
# Filling a context with a tree

Plugging replaces each hole of an open tree by a supplied tree. For the
one-hole contexts used later, this joins two pieces of a derivation: their
terminal counts and production counts add, and their supports are united.

This file proves structural formulas for arbitrary numbers of holes and
establishes validity and completeness when the inserted root matches the hole
labels. The public theorem `Parikh.plugging` in `Decomposition.lean` packages the
one-hole consequences used by insertion.

Source: `lem:plug`.
-/
namespace Parikh
variable {T N : Type*}

/-- Filling matching holes with a complete tree preserves validity and the root. -/
theorem Valid.plug_complete {g : ContextFreeGrammar T} {E t : ParseTree T g.NT}
    (hE : Valid g E) (ht : Complete g t)
    (hmatch : ∀ A ∈ E.holes, t.root = .nonterminal A) :
    Complete g (E.plug t) ∧ (E.plug t).root = E.root := by
  induction hE with
  | terminal a =>
    simp only [ParseTree.plug, Complete, ParseTree.holes]
    exact ⟨⟨.terminal a, True.intro⟩, True.intro⟩
  | hole A =>
    simpa only [ParseTree.plug, ParseTree.root] using
      And.intro ht (hmatch A (by simp [ParseTree.holes]))
  | node r children hr hc roots ih =>
    have children_plug : ∀ c ∈ children,
        Complete g (c.plug t) ∧ (c.plug t).root = c.root := by
      intro c hcmem
      apply ih c hcmem
      intro A hA
      apply hmatch A
      simp only [ParseTree.holes, ← List.flatMap_def, List.mem_flatMap]
      exact ⟨c, hcmem, hA⟩
    refine ⟨⟨?_, ?_⟩, by simp [ParseTree.plug, ParseTree.root]⟩
    · simp only [ParseTree.plug]
      refine Valid.node r _ hr ?_ ?_
      · intro c hc
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        exact (children_plug d hd).1.1
      · rw [List.map_map, ← roots]
        exact List.map_congr_left fun c hc => (children_plug c hc).2
    · simp only [ParseTree.plug, ParseTree.holes, List.flatten_eq_nil_iff,
        List.forall_mem_map]
      intro c hc
      exact (children_plug c hc).1.2

namespace ParseTree
/-- Each hole contributes one copy of the inserted tree's production count. -/
theorem productionSize_plug (E t : ParseTree T N) :
    (E.plug t).productionSize = E.productionSize + E.holes.length * t.productionSize := by
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, (c.plug t).productionSize =
      c.productionSize + c.holes.length * t.productionSize) with
  | terminal a => simp [plug.eq_1, productionSize.eq_1, holes.eq_1]
  | hole A => simp [plug.eq_2, productionSize.eq_2, holes.eq_2]
  | node r cs ih =>
    simp only [plug.eq_3, productionSize.eq_3, holes.eq_3, List.length_flatten, List.map_map,
      Function.comp_def]
    have hs := List.map_congr_left ih
    rw [hs, List.sum_map_add, List.sum_map_mul_right]
    omega
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd

/-- Terminal counts add once for each hole, regardless of its frontier position. -/
theorem count_yield_plug [DecidableEq T] (E t : ParseTree T N) (a : T) :
    (E.plug t).yield.count a = E.yield.count a + E.holes.length * t.yield.count a := by
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, (c.plug t).yield.count a =
      c.yield.count a + c.holes.length * t.yield.count a) with
  | terminal b => simp [plug.eq_1, yield.eq_1, holes.eq_1]
  | hole A => simp [plug.eq_2, yield.eq_2, holes.eq_2]
  | node r cs ih =>
    simp only [plug.eq_3, yield.eq_3, holes.eq_3, List.count_flatten, List.length_flatten,
      List.map_map,
      Function.comp_def]
    have hs := List.map_congr_left ih
    rw [hs, List.sum_map_add, List.sum_map_mul_right]
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd

/-- Plugging adds the inserted support exactly when the context has a hole. -/
theorem mem_support_plug (E t : ParseTree T N) (A : N) :
    A ∈ (E.plug t).support ↔ A ∈ E.support ∨ (E.holes ≠ [] ∧ A ∈ t.support) := by
  classical
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, A ∈ (c.plug t).support ↔
      A ∈ c.support ∨ (c.holes ≠ [] ∧ A ∈ t.support)) with
  | terminal a => simp [plug.eq_1, support, productionLabels.eq_1, holes.eq_1]
  | hole B => simp [plug.eq_2, support, productionLabels.eq_2, holes.eq_2]
  | node r cs ih =>
    have hholes : (node r cs).holes ≠ [] ↔ ∃ c ∈ cs, c.holes ≠ [] := by
      simp only [holes.eq_3, ne_eq, List.flatten_eq_nil_iff, List.forall_mem_map]
      push Not
      rfl
    have hlabels : ∀ c ∈ cs,
        A ∈ (c.plug t).productionLabels ↔
          A ∈ c.productionLabels ∨ (c.holes ≠ [] ∧ A ∈ t.productionLabels) := ih
    simp only [plug.eq_3, support, productionLabels.eq_3, List.map_map, Set.mem_ofPred_eq,
      List.mem_cons, ← List.flatMap_def, List.mem_flatMap, hholes]
    aesop
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd
end ParseTree

end Parikh
