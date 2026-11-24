/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks

/-!
# Point sets of concatenated trace walks

For the assembly in XII (2.1), Case 1, page 244, concatenating
walks unions their point sets. A single edge step adds its closure,
and a two-edge region visit has precisely the union of its two edge
closures as point set. These identities identify the circle assembled
from the deformed region paths with the trace drawing's point set.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The point set of a concatenated walk is the union of the point
sets of the two walks. -/
theorem walkDrawing_U_append
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S) {u v w : S}
    (P : GraphWalk K.toGraph u v) (Q : GraphWalk K.toGraph v w) :
    (walkDrawing K (P.append Q)).U = (walkDrawing K P).U ∪ (walkDrawing K Q).U := by
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append, mem_union]
  constructor
  · rintro ((h | h) | ⟨e, (he | he), hxe⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, he, hxe⟩)
    · exact Or.inr (Or.inr ⟨e, he, hxe⟩)
  · rintro ((h | ⟨e, he, hxe⟩) | (h | ⟨e, he, hxe⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨e, Or.inl he, hxe⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨e, Or.inr he, hxe⟩

/-- A zero-edge walk has just its vertex as point set. -/
theorem walkDrawing_U_nil
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S) {u : S} (hu : u ∈ K.V) :
    (walkDrawing K (GraphWalk.nil hu)).U = {u} := by
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.support, GraphWalk.edges, List.mem_singleton,
    List.not_mem_nil, false_and, exists_false, or_false, mem_singleton_iff]

/-- An edge step adds exactly its edge closure to the point set. -/
theorem walkDrawing_U_cons
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S) {u v w : S} {e : Set S}
    (hl : K.toGraph.IsLink e u v) (P : GraphWalk K.toGraph v w) :
    (walkDrawing K (GraphWalk.cons hl P)).U = closure e ∪ (walkDrawing K P).U := by
  have hu : u ∈ closure e := by
    have h : u ∈ closure e ∩ K.V := hl.2.2.2.symm ▸ Or.inl rfl
    exact h.1
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.support, GraphWalk.edges, List.mem_cons, mem_union]
  constructor
  · rintro ((rfl | h) | ⟨f, (rfl | hf), hxf⟩)
    · exact Or.inl hu
    · exact Or.inr (Or.inl h)
    · exact Or.inl hxf
    · exact Or.inr (Or.inr ⟨f, hf, hxf⟩)
  · rintro (h | h | ⟨f, hf, hxf⟩)
    · exact Or.inr ⟨e, Or.inl rfl, h⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨f, Or.inr hf, hxf⟩

/-- A two-edge region visit has the two edge closures as its whole
point set. -/
theorem walkDrawing_U_two_edges
    {S : Type*} [TopologicalSpace S] [T1Space S] (K : Drawing S)
    {u v w : S} {e e' : Set S} (hl : K.toGraph.IsLink e u v) (hl' : K.toGraph.IsLink e' v w) :
    (walkDrawing K (GraphWalk.cons hl (GraphWalk.cons hl' (.nil hl'.right_mem)))).U =
      closure e ∪ closure e' := by
  rw [walkDrawing_U_cons, walkDrawing_U_cons, walkDrawing_U_nil K (u := w) hl'.right_mem]
  have hw : w ∈ closure e' := by
    have h : w ∈ closure e' ∩ K.V := hl'.2.2.2.symm ▸ Or.inr rfl
    exact h.1
  rw [union_eq_left.mpr (singleton_subset_iff.mpr hw)]

end GraphMinor.GM12
