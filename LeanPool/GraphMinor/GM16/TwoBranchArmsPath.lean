/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic

/-!
# Joining two branch arms through a chosen edge

In the subdivision step of XVI (4.2), page 54, take an arm from each
of two disjoint branch sets and the chosen edge between their ends.
Their union is a path between the branch centres. Its vertices are
exactly the vertices of the two arms, and its edges are exactly the
arm edges together with the chosen edge.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09
universe u v

/-- Join disjoint arms by one edge, keeping exact vertex and edge sets.
This is the edge-path construction in XVI (4.2), page 54. -/
theorem exists_path_between_branch_arms {α : Type u} {β : Type v}
    {G A B : Graph α β} {m x n y : α} {e : β}
    (hA : IsGraphPathWithEnds G A m x) (hB : IsGraphPathWithEnds G B n y)
    (hDisj : Disjoint V(A) V(B)) (hEdge : G.IsLink e x y) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P m n ∧
      V(P) = V(A) ∪ V(B) ∧ E(P) = (E(A) ∪ {e}) ∪ E(B) := by
  have hxy : x ≠ y := hDisj.ne_of_mem hA.right_mem hB.right_mem
  let W : GraphWalk G x y := .cons hEdge (.nil hEdge.right_mem)
  let Q := walkSubgraph W
  have hW : W.IsSimple := by
    change [x,y].Nodup
    exact List.nodup_cons.mpr ⟨by simpa only [List.mem_singleton] using hxy,
      List.nodup_singleton y⟩
  have hQ : IsGraphPathWithEnds G Q x y := isGraphPathWithEnds_walkSubgraph hW
  have hVQ : V(Q) = {x,y} := by
    rw [vertexSet_walkSubgraph]
    ext z
    change z ∈ [x,y] ↔ z ∈ ({x,y} : Set α)
    simp only [List.mem_cons, List.not_mem_nil, or_false, mem_insert_iff, mem_singleton_iff]
  have hEQ : E(Q) = {e} := by
    rw [edgeSet_walkSubgraph]
    ext f
    change f ∈ [e] ↔ f ∈ ({e} : Set β)
    simp only [List.mem_singleton, mem_singleton_iff]
  have hAQ : V(A) ∩ V(Q) = {x} := by
    rw [hVQ]
    apply Subset.antisymm
    · rintro z ⟨hzA, hz⟩
      rcases hz with rfl | hz
      · exact mem_singleton _
      · rw [mem_singleton_iff] at hz
        subst z
        exact ((disjoint_left.mp hDisj) hzA hB.right_mem).elim
    · rintro z rfl
      exact ⟨hA.right_mem, mem_insert _ _⟩
  let AQ := subgraphUnion G A Q
  have hPathAQ : IsGraphPathWithEnds G AQ m y := hA.subgraphUnion hQ hAQ
  have hAQB : V(AQ) ∩ V(B) = {y} := by
    change (V(A) ∪ V(Q)) ∩ V(B) = {y}
    rw [hVQ]
    apply Subset.antisymm
    · rintro z ⟨hzA | hzQ, hzB⟩
      · exact ((disjoint_left.mp hDisj) hzA hzB).elim
      · rcases hzQ with rfl | hz
        · exact ((disjoint_left.mp hDisj) hA.right_mem hzB).elim
        · exact hz
    · rintro z rfl
      exact ⟨Or.inr (mem_insert_of_mem _ (mem_singleton _)), hB.right_mem⟩
  let P := subgraphUnion G AQ B
  refine ⟨P, hPathAQ.subgraphUnion hB.symm hAQB, ?_, ?_⟩
  · change (V(A) ∪ V(Q)) ∪ V(B) = V(A) ∪ V(B)
    rw [hVQ]
    apply Subset.antisymm
    · rintro z ((hzA | hzQ) | hzB)
      · exact Or.inl hzA
      · rcases hzQ with rfl | hz
        · exact Or.inl hA.right_mem
        · rw [mem_singleton_iff] at hz
          subst z
          exact Or.inr hB.right_mem
      · exact Or.inr hzB
    · exact union_subset (fun _ h => Or.inl (Or.inl h)) (fun _ h => Or.inr h)
  · change E(subgraphUnion G AQ B) = _
    rw [edgeSet_subgraphUnion hPathAQ.le hB.le,
      edgeSet_subgraphUnion hA.le hQ.le, hEQ]

end GraphMinor.GM16
