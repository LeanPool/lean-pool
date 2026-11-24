/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model

/-!
# The union graph of a path system

The subdivision subgraph in XVI (4.2), page 54, consists of the
replacement paths and all branch centres. The separate centre set
keeps isolated source vertices. Restrict to precisely the path edges
so that the union has no additional edges from the ambient graph.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph
universe u v w
variable {α : Type u} {β : Type v} {ι : Type w}

/-- The union of the given graphs, together with a set of additional
vertices, using exactly the edges of those graphs. -/
def pathSystemGraph (G : Graph α β) (C : Set α) (P : ι → Graph α β) : Graph α β :=
  (G.induce (C ∪ ⋃ i, V(P i))).restrict (⋃ i, E(P i))

/-- The vertices of the union graph. -/
theorem pathSystemGraph_vertexSet (G : Graph α β) (C : Set α) (P : ι → Graph α β) :
    V(pathSystemGraph G C P) = C ∪ ⋃ i, V(P i) := by rfl

/-- The union graph is contained in the ambient graph. -/
theorem pathSystemGraph_le {G : Graph α β} {C : Set α} {P : ι → Graph α β}
    (hC : C ⊆ V(G)) (hP : ∀ i, P i ≤ G) : pathSystemGraph G C P ≤ G :=
  Graph.restrict_le.trans (G.induce_le (union_subset hC (iUnion_subset fun i =>
    (hP i).vertexSet_mono)))

/-- Every member of the system is a subgraph of the union graph. -/
theorem le_pathSystemGraph {G : Graph α β} {C : Set α} {P : ι → Graph α β}
    (hP : ∀ i, P i ≤ G) (i : ι) : P i ≤ pathSystemGraph G C P := by
  refine ⟨fun x hx => Or.inr (mem_iUnion.mpr ⟨i,hx⟩), ?_⟩
  intro e x y hlink
  exact ⟨mem_iUnion.mpr ⟨i,hlink.edge_mem⟩, (hP i).isLink_mono hlink,
    Or.inr (mem_iUnion.mpr ⟨i,hlink.left_mem⟩),
    Or.inr (mem_iUnion.mpr ⟨i,hlink.right_mem⟩)⟩

/-- The edge set of the union graph is exactly the union of the edge
sets in the path system. -/
theorem pathSystemGraph_edgeSet {G : Graph α β} {C : Set α} {P : ι → Graph α β}
    (hP : ∀ i, P i ≤ G) : E(pathSystemGraph G C P) = ⋃ i, E(P i) := by
  apply Subset.antisymm
  · exact inter_subset_right
  · intro e he
    obtain ⟨i, hi⟩ := mem_iUnion.mp he
    exact (le_pathSystemGraph hP i).edgeSet_mono hi

end GraphMinor.GM16
