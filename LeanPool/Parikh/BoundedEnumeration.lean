/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Construction
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.Sections

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Computing all valid trees up to a height bound

At height zero, enumerate every terminal leaf and every declared nonterminal hole.
At the next height, choose a production and a smaller tree for each right-hand-side
symbol. Mathlib's `List.sections` enumerates these ordered Cartesian products;
filtering the child families by root makes every generated node valid.

The result includes open trees, unused declared symbols and empty productions.
Duplicate input productions are removed before expansion. The accepted interface
requires exact membership, without prescribing duplicate multiplicities.

Source: `lem:finite`, `sec:effective`.
-/
namespace Parikh

namespace ParseTree
variable {T N : Type*}

/-- The height of a production node in terms of its child heights. -/
theorem height_node_eq (r : ContextFreeRule T N) (children : List (ParseTree T N)) :
    (node r children).height = 1 + (children.map height).foldl max 0 := by
  exact height.eq_3 r children

/-- A node fits the next height bound exactly when every child fits the current bound. -/
theorem height_node_le_iff (r : ContextFreeRule T N) (children : List (ParseTree T N))
    (H : ℕ) : (node r children).height ≤ H + 1 ↔ ∀ c ∈ children, c.height ≤ H := by
  rw [height_node_eq]
  constructor
  · intro hh c hc
    have hm : c.height ∈ children.map height := List.mem_map_of_mem hc
    have hmax := List.le_max_of_mem hm
    rw [List.foldl_max_eq_max (List.ne_nil_of_mem hm), Nat.zero_max] at hh
    omega
  · intro hchildren
    have hfold : (children.map height).foldl max 0 ≤ H := by
      by_cases hnil : children = []
      · simp [hnil]
      · have hne : children.map height ≠ [] := fun h => hnil (List.map_eq_nil_iff.mp h)
        rw [List.foldl_max_eq_max hne, Nat.zero_max]
        apply (List.max_le_iff hne).mpr
        intro n hn
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        exact hchildren c hc
    omega

/-- Root-filtered Cartesian products preserve both child membership and child order. -/
theorem mem_root_sections [DecidableEq T] [DecidableEq N]
    (family : List (ParseTree T N)) (symbols : List (Symbol T N))
    (children : List (ParseTree T N)) :
    children ∈ (symbols.map (fun s => family.filter (fun t => decide (t.root = s)))).sections ↔
      (∀ c ∈ children, c ∈ family) ∧ children.map root = symbols := by
  rw [List.mem_sections, List.forall₂_map_right_iff]
  simp only [List.mem_filter, decide_eq_true_eq]
  rw [List.forall₂_and_left, ← List.forall₂_map_left_iff, List.forall₂_eq_eq_eq]
end ParseTree

/-- The three checks required at a production node, as a reusable elimination rule. -/
theorem Valid.node_iff {T : Type*} (g : ContextFreeGrammar T)
    (r : ContextFreeRule T g.NT) (children : List (ParseTree T g.NT)) :
    Valid g (.node r children) ↔ r ∈ g.rules ∧
      (∀ c ∈ children, Valid g c) ∧ children.map ParseTree.root = r.output := by
  constructor
  · intro hv
    cases hv with
    | node _ _ hr hc roots => exact ⟨hr, hc, roots⟩
  · rintro ⟨hr, hc, roots⟩
    exact Valid.node (g := g) r children hr hc roots

namespace EncodedGrammar

/-- Every declared leaf, including holes for nonterminals absent from productions. -/
@[expose] def leaves (g : EncodedGrammar) :
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :=
  (List.finRange g.terminalCount).map ParseTree.terminal ++
    (List.finRange (g.extraNonterminalCount + 1)).map ParseTree.hole

/-- The height-zero family is exactly all valid leaves (`lem:finite`). -/
theorem leaves_correct (g : EncodedGrammar)
    (t : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    t ∈ g.leaves ↔ Valid g.decode t ∧ t.height = 0 := by
  constructor
  · intro ht
    simp only [leaves, List.mem_append, List.mem_map, List.mem_finRange, true_and] at ht
    rcases ht with ⟨a, rfl⟩ | ⟨A, rfl⟩
    · exact ⟨Valid.terminal (g := g.decode) a, by simp [ParseTree.height]⟩
    · exact ⟨Valid.hole (g := g.decode) A, by simp [ParseTree.height]⟩
  · rintro ⟨hv, hh⟩
    cases t with
    | terminal a => simp [leaves]
    | hole A => simp [leaves]
    | node r children =>
      rw [ParseTree.height_node_eq] at hh
      omega

/-- Enumerate valid open trees by height, using finite ordered child products.
Explicit natural-number recursion supplies a computable implementation. -/
@[expose] def enumerateTrees (g : EncodedGrammar) (H : ℕ) :
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :=
  Nat.rec (motive := fun _ =>
      List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))))
    g.leaves
    (fun _ smaller => g.leaves ++ g.rules.dedup.flatMap (fun r =>
      ((r.output.map (fun s => smaller.filter (fun t => decide (t.root = s)))).sections).map
        (ParseTree.node r))) H

/-- Every generated tree is valid and within the bound, and every such tree is
generated. This is the exact accepted enumeration contract (`lem:finite`). -/
theorem enumerateTrees_correct (g : EncodedGrammar) (H : ℕ)
    (t : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    t ∈ g.enumerateTrees H ↔ Valid g.decode t ∧ t.height ≤ H := by
  induction H generalizing t with
  | zero =>
    change t ∈ g.leaves ↔ _
    simpa only [Nat.le_zero_eq] using g.leaves_correct t
  | succ H ih =>
    change t ∈ g.leaves ++ g.rules.dedup.flatMap (fun r =>
      ((r.output.map (fun s => (g.enumerateTrees H).filter (fun c => decide (c.root =
        s)))).sections).map
        (ParseTree.node r)) ↔ _
    constructor
    · intro ht
      rcases List.mem_append.mp ht with hleaf | hnode
      · have h := (g.leaves_correct t).mp hleaf
        exact ⟨h.1, by omega⟩
      · obtain ⟨r, hr, hmap⟩ := List.mem_flatMap.mp hnode
        obtain ⟨cs, hsection, rfl⟩ := List.mem_map.mp hmap
        have h := (ParseTree.mem_root_sections _ _ _).mp hsection
        have hchildren : ∀ c ∈ cs, Valid g.decode c ∧ c.height ≤ H :=
          fun c hc => (ih c).mp (h.1 c hc)
        refine ⟨Valid.node (g := g.decode) r cs ?_ (fun c hc => (hchildren c hc).1) h.2, ?_⟩
        · change r ∈ g.rules.toFinset
          exact List.mem_toFinset.mpr (List.mem_dedup.mp hr)
        · exact (ParseTree.height_node_le_iff r cs H).mpr (fun c hc => (hchildren c hc).2)
    · rintro ⟨hv, hh⟩
      cases t with
      | terminal a =>
        exact List.mem_append_left _ ((g.leaves_correct _).mpr
          ⟨Valid.terminal (g := g.decode) a, by simp [ParseTree.height]⟩)
      | hole A =>
        exact List.mem_append_left _ ((g.leaves_correct _).mpr
          ⟨Valid.hole (g := g.decode) A, by simp [ParseTree.height]⟩)
      | node r cs =>
        obtain ⟨hr, hchildren, roots⟩ := (Valid.node_iff g.decode r cs).mp hv
        change r ∈ g.rules.toFinset at hr
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨r, List.mem_dedup.mpr (List.mem_toFinset.mp hr),
          List.mem_map.mpr ⟨cs, ?_, rfl⟩⟩
        apply (ParseTree.mem_root_sections _ _ _).mpr
        refine ⟨?_, roots⟩
        have hheight := (ParseTree.height_node_le_iff r cs H).mp hh
        exact fun c hc => (ih c).mpr ⟨hchildren c hc, hheight c hc⟩
end EncodedGrammar

/-- An executable value of the accepted enumeration interface, with its complete
correctness proof and no classical runtime selection (`lem:finite`). -/
@[expose] def boundedEnumeration : BoundedEnumeration where
  enumerate := EncodedGrammar.enumerateTrees
  correct := EncodedGrammar.enumerateTrees_correct

end Parikh
