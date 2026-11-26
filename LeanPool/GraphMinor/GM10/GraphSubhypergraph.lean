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
# Subgraphs associated with subhypergraphs of a graph

On subhypergraphs of the incidence hypergraph of a graph, restriction to
the given vertices and edges gives the inverse correspondence.
-/

@[expose] public section

namespace GraphMinor.GM10

open Set Graph Hypergraph

universe u v
variable {α : Type u} {β : Type v}

/-- If `u ≠ v` and `e` is incident with both `u` and `v` in `G : Graph α β`, then `G.IsLink e u v`.
-/
theorem isLink_of_inc_of_inc_of_ne {G : Graph α β} {e : β} {u v : α}
    (hu : G.Inc e u) (hv : G.Inc e v) (huv : u ≠ v) : G.IsLink e u v := by
  rcases hu with ⟨x, hux⟩
  rcases hv with ⟨y, hvy⟩
  rcases G.eq_or_eq_of_isLink_of_isLink hvy hux.symm with rfl | rfl
  · exact hux
  · exact (huv rfl).elim

/-- Reachability in `(Hypergraph.ofGraph H hVH hEH).skeleton` implies `Relation.ReflTransGen H.Adj`.
-/
theorem reflTransGen_adj_of_skeleton_walk {H : Graph α β}
    {hVH : V(H).Finite} {hEH : E(H).Finite} {u v : α}
    (w : (Hypergraph.ofGraph H hVH hEH).skeleton.Walk u v) :
    Relation.ReflTransGen H.Adj u v := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c hadj _ ih =>
    rcases hadj with ⟨hab, e, ha_inc, hb_inc⟩
    exact Relation.ReflTransGen.head ⟨e, isLink_of_inc_of_inc_of_ne ha_inc hb_inc hab⟩ ih

/-- The subgraph of `G` corresponding to a subhypergraph `H ≤ Hypergraph.ofGraph G hV hE`. -/
def subgraphOfSubhypergraph (G : Graph α β) (H : Hypergraph α β) : Graph α β :=
  (G.induce H.vertexSet).restrict H.edgeSet

@[simp]
theorem vertexSet_subgraphOfSubhypergraph (G : Graph α β) (H : Hypergraph α β) :
    V(subgraphOfSubhypergraph G H) = H.vertexSet := rfl

theorem subgraphOfSubhypergraph_le {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {H : Hypergraph α β} (hH : H ≤ Hypergraph.ofGraph G hV hE) :
    subgraphOfSubhypergraph G H ≤ G :=
  restrict_le.trans (G.induce_le hH.vertexSet_subset)

@[simp]
theorem edgeSet_subgraphOfSubhypergraph {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {H : Hypergraph α β} (hH : H ≤ Hypergraph.ofGraph G hV hE) :
    E(subgraphOfSubhypergraph G H) = H.edgeSet := by
  ext e
  simp only [subgraphOfSubhypergraph, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce]
  refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
  have heG : e ∈ E(G) := hH.edgeSet_subset he
  obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet heG
  have hx_end : x ∈ (Hypergraph.ofGraph G hV hE).ends e := ⟨y, hlink⟩
  have hy_end : y ∈ (Hypergraph.ofGraph G hV hE).ends e := ⟨x, hlink.symm⟩
  rw [hH.ends_eq e he] at hx_end hy_end
  exact ⟨x, y, hlink, H.vertex_mem_of_inc hx_end, H.vertex_mem_of_inc hy_end⟩

theorem subgraphOfSubhypergraph_mono {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {H₁ H₂ : Hypergraph α β} (h₁ : H₁ ≤ Hypergraph.ofGraph G hV hE)
    (h₂ : H₂ ≤ Hypergraph.ofGraph G hV hE) (hle : H₁ ≤ H₂) :
    subgraphOfSubhypergraph G H₁ ≤ subgraphOfSubhypergraph G H₂ := by
  rw [(Compatible.of_le_le (subgraphOfSubhypergraph_le h₁) (subgraphOfSubhypergraph_le h₂)).le_iff]
  rw [vertexSet_subgraphOfSubhypergraph, vertexSet_subgraphOfSubhypergraph,
    edgeSet_subgraphOfSubhypergraph h₁, edgeSet_subgraphOfSubhypergraph h₂]
  exact ⟨hle.vertexSet_subset, hle.edgeSet_subset⟩

theorem ofGraph_subgraphOfSubhypergraph {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {H : Hypergraph α β} (hH : H ≤ Hypergraph.ofGraph G hV hE) :
    Hypergraph.ofGraph (subgraphOfSubhypergraph G H) H.vertexSet_finite
      (H.edgeSet_finite.subset (by rw [edgeSet_subgraphOfSubhypergraph hH])) = H := by
  have hleG : subgraphOfSubhypergraph G H ≤ G := subgraphOfSubhypergraph_le hH
  have hle_of : Hypergraph.ofGraph (subgraphOfSubhypergraph G H) H.vertexSet_finite
      (H.edgeSet_finite.subset (by rw [edgeSet_subgraphOfSubhypergraph hH])) ≤
      Hypergraph.ofGraph G hV hE := by
    refine ⟨hH.vertexSet_subset, ?_, ?_⟩
    · change E(subgraphOfSubhypergraph G H) ⊆ E(G)
      rw [edgeSet_subgraphOfSubhypergraph hH]
      exact hH.edgeSet_subset
    · intro e he
      ext v
      exact (hleG.inc_congr he).symm
  exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle_of hH rfl
    (edgeSet_subgraphOfSubhypergraph hH)

theorem subgraphOfSubhypergraph_ofGraph {G H : Graph α β} (hH : H ≤ G)
    (hVH : V(H).Finite) (hEH : E(H).Finite) :
    subgraphOfSubhypergraph G (Hypergraph.ofGraph H hVH hEH) = H := by
  have hle : subgraphOfSubhypergraph G (Hypergraph.ofGraph H hVH hEH) ≤ G :=
    restrict_le.trans (G.induce_le hH.vertexSet_mono)
  refine (Compatible.of_le_le hle hH).ext rfl ?_
  ext e
  simp only [subgraphOfSubhypergraph, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce,
    Hypergraph.ofGraph]
  refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
  obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, hlink.mono hH, hlink.left_mem, hlink.right_mem⟩

end GraphMinor.GM10
