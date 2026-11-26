/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM16.Section6HairUnion
import LeanPool.GraphMinor.GM16.Section9Attachments
import LeanPool.GraphMinor.GM09.Basic

/-!
# An old hair and two exit paths contain a new hair

Join the old hair to the paths taking its two old ends to the
cleared drawing. The connected union meets that drawing only at
the two new ends and has no edge there. A path in the union is
therefore a hair of the cleared drawing. This supplies the graph
step in XVI (7.1), Claim (6), page 70.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM14
universe u v

/-- The connected union of an old hair and its two exit paths
contains a path relative to the new drawing with the new ends. -/
theorem exists_hPath_between_exits {α : Type u} {β : Type v}
    {G H K A Q B : Graph α β} {y r p q : α}
    (hKH : K ≤ H) (hQ : IsHPathWithEnds G H Q y r)
    (hA : IsGraphPathWithEnds G A y p) (hB : IsGraphPathWithEnds G B r q)
    (hAK : V(A) ∩ V(K) = {p}) (hBK : V(B) ∩ V(K) = {q})
    (hyK : y ∉ V(K)) (hpK : p ∈ V(K)) (hqK : q ∈ V(K)) (hpq : p ≠ q) :
    ∃ R : Graph α β, IsHPathWithEnds G K R p q := by
  have hKG := hKH.trans hQ.1
  have hQE : Disjoint E(Q) E(K) := hQ.2.2.2.2.2.2.mono Subset.rfl hKH.edgeSet_mono
  have hAE := path_edges_disjoint_of_singleton_inter hKG hA hAK.subset
  have hBE := path_edges_disjoint_of_singleton_inter hKG hB hBK.subset
  have hQK : V(Q) ∩ V(K) ⊆ {q} := by
    rintro x ⟨hxQ, hxK⟩
    have hxEnds : x ∈ ({y, r} : Set α) := hQ.2.2.2.2.2.1 ▸ ⟨hxQ, hKH.vertexSet_mono hxK⟩
    rcases hxEnds with hxy | hxr
    · exact False.elim (hyK (hxy ▸ hxK))
    · rw [mem_singleton_iff] at hxr
      subst x
      exact hBK ▸ ⟨hB.left_mem, hxK⟩
  let J₁ := subgraphUnion G A Q
  have hJ₁G : J₁ ≤ G := subgraphUnion_le hA.1 hQ.2.1.1
  have hAJ₁ : A ≤ J₁ := le_subgraphUnion_left hA.1 hQ.2.1.1
  have hQJ₁ : Q ≤ J₁ := le_subgraphUnion_right hA.1 hQ.2.1.1
  have hConn₁ : IsGraphConnected J₁ := isGraphConnected_subgraphUnion hA.1 hQ.2.1.1
    (graphPath_isGraphConnected hA) (graphPath_isGraphConnected hQ.2.1)
    ⟨y, hA.left_mem, hQ.2.1.left_mem⟩
  let J := subgraphUnion G J₁ B
  have hJG : J ≤ G := subgraphUnion_le hJ₁G hB.1
  have hJ₁J : J₁ ≤ J := le_subgraphUnion_left hJ₁G hB.1
  have hBJ : B ≤ J := le_subgraphUnion_right hJ₁G hB.1
  have hConn : IsGraphConnected J := isGraphConnected_subgraphUnion hJ₁G hB.1 hConn₁
    (graphPath_isGraphConnected hB) ⟨r, hQJ₁.vertexSet_mono hQ.2.1.right_mem, hB.left_mem⟩
  have hJV : V(J) = (V(A) ∪ V(Q)) ∪ V(B) := by
    rw [show J = subgraphUnion G J₁ B from rfl, vertexSet_subgraphUnion,
      show J₁ = subgraphUnion G A Q from rfl, vertexSet_subgraphUnion]
  have hJE : E(J) = (E(A) ∪ E(Q)) ∪ E(B) := by
    rw [show J = subgraphUnion G J₁ B from rfl, edgeSet_subgraphUnion hJ₁G hB.1,
      show J₁ = subgraphUnion G A Q from rfl, edgeSet_subgraphUnion hA.1 hQ.2.1.1]
  have hJK : V(J) ∩ V(K) ⊆ {p, q} := by
    rintro x ⟨hxJ, hxK⟩
    rw [hJV] at hxJ
    rcases hxJ with (hxA | hxQ) | hxB
    · exact Or.inl (mem_singleton_iff.mp (hAK ▸ ⟨hxA, hxK⟩))
    · exact Or.inr (hQK ⟨hxQ, hxK⟩)
    · exact Or.inr (hBK ▸ ⟨hxB, hxK⟩)
  have hJEdges : Disjoint E(J) E(K) := by rw [hJE]; exact (hAE.union_left hQE).union_left hBE
  obtain ⟨W⟩ := hConn.2 p (hJ₁J.vertexSet_mono (hAJ₁.vertexSet_mono hA.right_mem))
    q (hBJ.vertexSet_mono hB.right_mem)
  obtain ⟨R, hR, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
  refine ⟨R, hKG, hR.mono hJG, hpq, hpK, hqK, ?_, hJEdges.mono hR.1.edgeSet_mono Subset.rfl⟩
  apply subset_antisymm
  · exact fun x hx => hJK ⟨hR.1.vertexSet_mono hx.1, hx.2⟩
  · rintro x (rfl | hxq)
    · exact ⟨hR.left_mem, hpK⟩
    · rw [mem_singleton_iff] at hxq
      subst x
      exact ⟨hR.right_mem, hqK⟩

end GraphMinor.GM16
