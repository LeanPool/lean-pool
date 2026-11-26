/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# A connected subgraph avoiding a separator

If a connected subgraph misses the separator, all its vertices and
edges lie on one side. Walk along the subgraph from a fixed vertex.
A first edge on the other side would put its starting vertex in the
separator. This supplies the uncut-row step in XVI (4.2), Claim (1).
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph GM10
universe u v

/-- A connected subgraph disjoint from the separator lies on one side
of the separation. -/
theorem connected_subgraph_in_one_side {α : Type u} {β : Type v}
    {G K : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    {A B : Hypergraph α β} (hSep : (Hypergraph.ofGraph G hV hE).IsSeparation A B)
    (hK : K ≤ G) (hConn : GraphConnected K)
    (hAvoid : Disjoint V(K) (A.vertexSet ∩ B.vertexSet)) :
    (V(K) ⊆ A.vertexSet ∧ E(K) ⊆ A.edgeSet) ∨
      (V(K) ⊆ B.vertexSet ∧ E(K) ⊆ B.edgeSet) := by
  have propagate (A B : Hypergraph α β)
      (hSep : (Hypergraph.ofGraph G hV hE).IsSeparation A B)
      (hAvoid : Disjoint V(K) (A.vertexSet ∩ B.vertexSet))
      (x : α) (hxK : x ∈ V(K)) (hxA : x ∈ A.vertexSet) :
      V(K) ⊆ A.vertexSet ∧ E(K) ⊆ A.edgeSet := by
    have hVertices : V(K) ⊆ A.vertexSet := by
      intro y hy
      have hwalk := hConn.2 x hxK y hy
      have hresult : y ∈ V(K) ∧ y ∈ A.vertexSet := by
        induction hwalk with
        | refl => exact ⟨hxK, hxA⟩
        | @tail z w _ hzw ih =>
          obtain ⟨e, hlink⟩ := hzw
          have ih₀ := ih hlink.left_mem
          have hG := hK.isLink_mono hlink
          have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hSep.edgeSet_union.symm ▸ hG.edge_mem
          refine ⟨hlink.right_mem, ?_⟩
          rcases heAB with heA | heB
          · exact A.vertex_mem_of_inc ((inc_iff_of_le hSep.left_le heA).mpr hG.inc_right)
          · have hzB := B.vertex_mem_of_inc ((inc_iff_of_le hSep.right_le heB).mpr hG.inc_left)
            exact ((disjoint_left.mp hAvoid) ih₀.1 ⟨ih₀.2, hzB⟩).elim
      exact hresult.2
    refine ⟨hVertices, ?_⟩
    intro e heK
    obtain ⟨z, w, hlink⟩ := exists_isLink_of_mem_edgeSet heK
    have hG := hK.isLink_mono hlink
    have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hSep.edgeSet_union.symm ▸ hG.edge_mem
    rcases heAB with heA | heB
    · exact heA
    · have hzB := B.vertex_mem_of_inc ((inc_iff_of_le hSep.right_le heB).mpr hG.inc_left)
      exact ((disjoint_left.mp hAvoid) hlink.left_mem ⟨hVertices hlink.left_mem, hzB⟩).elim
  obtain ⟨x, hxK⟩ := hConn.1
  have hxAB : x ∈ A.vertexSet ∪ B.vertexSet :=
    hSep.vertexSet_union.symm ▸ hK.vertexSet_mono hxK
  rcases hxAB with hxA | hxB
  · exact Or.inl (propagate A B hSep hAvoid x hxK hxA)
  · exact Or.inr (propagate B A hSep.symm (by simpa only [Set.inter_comm] using hAvoid) x hxK hxB)

end GraphMinor.GM16
