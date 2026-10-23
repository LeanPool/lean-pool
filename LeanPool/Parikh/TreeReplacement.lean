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
# Selecting and replacing a particular occurrence

A nonterminal may occur many times in a tree. Support membership says that an
occurrence exists; a position, given by child indices, selects which one.

The results here connect these two views and extract the outer context around
a selected subtree. Filling its hole recovers the original tree; filling it
with a different matching subtree implements replacement. This lets later
proofs reason about insertion locally while preserving the surrounding tree.

Source: `lem:enabled`, `lem:insertion-laws`.
-/
namespace Parikh
variable {T N : Type*}

namespace ParseTree
/-- A complete side branch is unchanged when another subtree fills holes. -/
theorem plug_of_holes_eq_nil (E t : ParseTree T N) (hE : E.holes = []) :
    E.plug t = E := by
  induction E using ParseTree.rec (motive_2 := fun (cs : List (ParseTree T N)) =>
    ∀ c ∈ cs, c.holes = [] → c.plug t = c) with
  | terminal a => simp [plug]
  | hole A => simp [holes] at hE
  | node r cs ih =>
    have hc : ∀ c ∈ cs, c.holes = [] := by
      simpa only [holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hE
    simp only [plug]
    congr 1
    simpa using List.map_congr_left (fun c h => ih c h (hc c h))
  | nil c hc => simp at hc
  | cons c cs hc hcs d hd hh =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc hh
    · exact hcs d hd hh
end ParseTree

/-- In a complete tree, support is exactly the labels of nonterminal-rooted subtrees. -/
theorem Complete.mem_support_iff_subtree {g : ContextFreeGrammar T}
    {t : ParseTree T g.NT} (ht : Complete g t) (A : g.NT) :
    A ∈ t.support ↔ ∃ q u, t.subtree q = some u ∧ u.root = .nonterminal A := by
  obtain ⟨hv, hh⟩ := ht
  induction hv with
  | terminal a =>
    simp only [ParseTree.support, ParseTree.productionLabels, Set.mem_ofPred_eq,
      List.not_mem_nil, false_iff]
    rintro ⟨q, u, hq, hu⟩
    cases q with
    | nil => simp [ParseTree.subtree] at hq; subst u; simp [ParseTree.root] at hu
    | cons i q => simp [ParseTree.subtree] at hq
  | hole B => simp [ParseTree.holes] at hh
  | node r cs hr hc roots ih =>
    have hholes : ∀ c ∈ cs, c.holes = [] := by
      simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
    simp only [ParseTree.support, ParseTree.productionLabels, Set.mem_ofPred_eq,
      List.mem_cons, ← List.flatMap_def, List.mem_flatMap]
    constructor
    · rintro (hA | ⟨c, hcmem, hA⟩)
      · subst A
        exact ⟨[], .node r cs, rfl, rfl⟩
      · obtain ⟨q, u, hq, hu⟩ := (ih c hcmem (hholes c hcmem)).mp hA
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcmem
        exact ⟨i :: q, u, by simp [ParseTree.subtree, hi, hq], hu⟩
    · rintro ⟨q, u, hq, hu⟩
      cases q with
      | nil =>
        simp only [ParseTree.subtree, Option.some.injEq] at hq
        subst u
        exact Or.inl (by simpa only [ParseTree.root, Symbol.nonterminal.injEq] using hu.symm)
      | cons i q =>
        obtain ⟨c, hi, hq⟩ := Option.bind_eq_some_iff.mp hq
        have hcmem := List.mem_of_getElem? hi
        exact Or.inr ⟨c, hcmem, (ih c hcmem (hholes c hcmem)).mpr ⟨q, u, hq, hu⟩⟩

/-- A selected nonterminal occurrence can be cut out and replaced through its
outer one-hole context. The selected subtree and all side branches are complete. -/
theorem Complete.subtree_context {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Complete g t) (q : List ℕ) (u : ParseTree T g.NT)
    (hpos : t.subtree q = some u) (A : g.NT) (hu : u.root = .nonterminal A) :
    Complete g u ∧ ∃ E, OneHole g E A ∧ E.root = t.root ∧ E.plug u = t ∧
      ∀ v, t.replaceAt q v = some (E.plug v) := by
  induction q generalizing t with
  | nil =>
    simp only [ParseTree.subtree, Option.some.injEq] at hpos
    subst u
    refine ⟨ht, .hole A, ⟨.hole A, by simp [ParseTree.holes]⟩, ?_, ?_, ?_⟩
    · exact hu.symm
    · simp [ParseTree.plug]
    · intro v; simp [ParseTree.replaceAt, ParseTree.plug]
  | cons i q ih =>
    cases t with
    | terminal a => simp [ParseTree.subtree] at hpos
    | hole B => simp [ParseTree.subtree] at hpos
    | node r cs =>
      obtain ⟨c, hi, hpos⟩ := Option.bind_eq_some_iff.mp hpos
      have hcmem := List.mem_of_getElem? hi
      obtain ⟨hv, hh⟩ := ht
      cases hv with
      | node _ _ hr hc roots =>
        have hholes : ∀ d ∈ cs, d.holes = [] := by
          simpa only [ParseTree.holes, List.flatten_eq_nil_iff, List.forall_mem_map] using hh
        obtain ⟨huc, E, hE, hroot, hplug, hreplace⟩ :=
          ih ⟨hc c hcmem, hholes c hcmem⟩ hpos
        obtain ⟨hlt, helem⟩ := List.getElem?_eq_some_iff.mp hi
        have hset : cs.set i c = cs := by rw [← helem]; exact List.set_getElem_self hlt
        have hmaps (v : ParseTree T g.NT) : cs.map (fun d => d.plug v) = cs := by
          have hm : cs.map (fun d => d.plug v) = cs.map id :=
            List.map_congr_left (fun d hd => d.plug_of_holes_eq_nil v (hholes d hd))
          simpa using hm
        refine ⟨huc, .node r (cs.set i E), ⟨?_, ?_⟩, rfl, ?_, ?_⟩
        · refine Valid.node r _ hr ?_ ?_
          · intro d hd
            rcases List.mem_or_eq_of_mem_set hd with hd | rfl
            · exact hc d hd
            · exact hE.1
          · rw [List.map_set, hroot, ← roots]
            simpa only [List.map_set] using congrArg (List.map ParseTree.root) hset
        · have hprefix : ((cs.take i).map ParseTree.holes).flatten = [] := by
            simp only [List.flatten_eq_nil_iff, List.forall_mem_map]
            intro d hd
            exact hholes d (List.mem_of_mem_take hd)
          have hsuffix : ((cs.drop (i + 1)).map ParseTree.holes).flatten = [] := by
            simp only [List.flatten_eq_nil_iff, List.forall_mem_map]
            intro d hd
            exact hholes d (List.mem_of_mem_drop hd)
          simp only [ParseTree.holes, List.set_eq_take_append_cons_drop, ite_eq_left hlt,
            List.map_append, List.map_cons, List.flatten_append, List.flatten_cons,
            hprefix, hsuffix, hE.2, List.nil_append, List.append_nil]
        · simp only [ParseTree.plug, List.map_set, hmaps, hplug, hset]
        · intro v
          simp [ParseTree.replaceAt, hi, hreplace v, ParseTree.plug, List.map_set, hmaps]

end Parikh
