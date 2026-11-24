/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Putting the deleted vertex on both sides of a separation

In XII (7.3), Claim (1), page 262, enlarge both sides of an old
separation by the single vertex being deleted, adding no edges.
The result is still a separation. Its order increases by at most
one and stays fixed if the vertex was already on both sides.
When the new order is below the tangle order, X (2.9) preserves
the selected orientation.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph GM10

/-- Adding the same vertex to both sides, without edges, preserves
the separation, as in XII (7.3), Claim (1), page 262. -/
theorem isSeparation_adjoin_vertex
    {α β : Type*} {G A B : Hypergraph α β} (hsep : G.IsSeparation A B)
    {v : α} (hv : v ∈ G.vertexSet) :
    G.IsSeparation (A ∪ vertexHypergraph v) (B ∪ vertexHypergraph v) := by
  rw [isSeparation_iff_of_le
    (union_le hsep.left_le (vertexHypergraph_le hv))
    (union_le hsep.right_le (vertexHypergraph_le hv))]
  refine ⟨?_, ?_, ?_⟩
  · change (A.vertexSet ∪ {v}) ∪ (B.vertexSet ∪ {v}) = G.vertexSet
    calc
      _ = (A.vertexSet ∪ B.vertexSet) ∪ {v} := by
        ext x; simp only [mem_union, mem_singleton_iff]; tauto
      _ = G.vertexSet := by rw [hsep.vertexSet_union, union_singleton, insert_eq_of_mem hv]
  · simpa only [union_edgeSet, vertexHypergraph, union_empty] using hsep.edgeSet_union
  · simpa only [union_edgeSet, vertexHypergraph, union_empty, inter_edgeSet] using
    hsep.edgeSet_inter_eq

/-- The enlarged separator is the old separator with the one vertex
inserted. This is the order calculation in XII (7.3), Claim (1). -/
theorem separationOrder_adjoin_vertex
    {α β : Type*} (A B : Hypergraph α β) (v : α) :
    separationOrder (A ∪ vertexHypergraph v) (B ∪ vertexHypergraph v) =
      (insert v (A.vertexSet ∩ B.vertexSet)).ncard := by
  unfold separationOrder
  congr 1
  ext x
  change (x ∈ A.vertexSet ∨ x = v) ∧ (x ∈ B.vertexSet ∨ x = v) ↔ _
  simp only [mem_insert_iff, mem_inter_iff]
  tauto

/-- Adjoining the vertex increases the separation order by at most
one, the first order bound in XII (7.3), Claim (1), page 262. -/
theorem separationOrder_adjoin_vertex_le
    {α β : Type*} (A B : Hypergraph α β) (v : α) :
    separationOrder (A ∪ vertexHypergraph v) (B ∪ vertexHypergraph v) ≤
      separationOrder A B + 1 := by
  rw [separationOrder_adjoin_vertex]
  exact ncard_insert_le _ _

/-- A vertex already in the separator adds nothing to its order.
This is the saving of one in XII (7.3), Claim (1), page 262. -/
theorem separationOrder_adjoin_vertex_of_mem
    {α β : Type*} {A B : Hypergraph α β} {v : α}
    (hv : v ∈ A.vertexSet ∩ B.vertexSet) :
    separationOrder (A ∪ vertexHypergraph v) (B ∪ vertexHypergraph v) =
      separationOrder A B := by
  rw [separationOrder_adjoin_vertex, insert_eq_of_mem hv]
  rfl

/-- X (2.9) selects the enlarged separation when its order is still
small. This is the orientation step of XII (7.3), Claim (1), page 262. -/
theorem adjoin_vertex_mem_tangle
    {α β : Type*} {G A B : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T)
    (hm : (A, B) ∈ T) {v : α} (hv : v ∈ G.vertexSet)
    (hord : separationOrder (A ∪ vertexHypergraph v) (B ∪ vertexHypergraph v) < θ) :
    (A ∪ vertexHypergraph v, B ∪ vertexHypergraph v) ∈ T := by
  exact GraphMinor.GM10.theorem_2_9_proof hT hm (isSeparation_adjoin_vertex
    (hT.isSeparation hm) hv) hord
    (Or.inl subset_union_left)

/-- Deleting the adjoined vertex gives the same graph as deleting
it before adjoining. This identifies the sides in XII (7.3),
Claim (1), after passing to the deleted tangle. -/
theorem deleteVertices_adjoin_vertex
    {α β : Type*} (A : Hypergraph α β) (v : α) :
    (A ∪ vertexHypergraph v).deleteVertices {v} = A.deleteVertices {v} := by
  apply Hypergraph.ext
  · ext x
    change (x ∈ A.vertexSet ∪ {v} ∧ x ∉ ({v} : Set α)) ↔
      (x ∈ A.vertexSet ∧ x ∉ ({v} : Set α))
    simp only [mem_union, mem_singleton_iff]
    tauto
  · ext e
    simp only [deleteVertices, union_edgeSet, vertexHypergraph, union_empty, mem_ofPred_eq,
      union_inc, or_false]
  · funext e x
    simp only [deleteVertices, union_inc, vertexHypergraph, or_false]

private theorem delete_mono
    {α β : Type*} {G A : Hypergraph α β} (hA : A ≤ G) (Z : Set α) :
    A.deleteVertices Z ≤ G.deleteVertices Z where
  vertexSet_subset := sdiff_subset_sdiff hA.vertexSet_subset subset_rfl
  edgeSet_subset e he :=
    ⟨hA.edgeSet_subset he.1, fun v hv hi => he.2 v hv ((inc_iff_of_le hA he.1).2 hi)⟩
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq, deleteVertices]
    simp_rw [inc_iff_of_le hA he.1]

/-- Vertex deletion preserves a separation. This identifies the
separation used when passing from the enlarged sides to the new
tangle in XII (7.3), Claim (1). -/
theorem isSeparation_deleteVertices
    {α β : Type*} {G A B : Hypergraph α β} (hsep : G.IsSeparation A B) (Z : Set α) :
    (G.deleteVertices Z).IsSeparation (A.deleteVertices Z) (B.deleteVertices Z) := by
  rw [isSeparation_iff_of_le (delete_mono hsep.left_le Z) (delete_mono hsep.right_le Z)]
  refine ⟨?_, ?_, ?_⟩
  · change (A.vertexSet \ Z) ∪ (B.vertexSet \ Z) = G.vertexSet \ Z
    rw [← union_sdiff_distrib, hsep.vertexSet_union]
  · ext e
    constructor
    · rintro (he | he)
      · exact (delete_mono hsep.left_le Z).edgeSet_subset he
      · exact (delete_mono hsep.right_le Z).edgeSet_subset he
    · rintro ⟨he, hno⟩
      rcases hsep.edgeSet_union.symm ▸ he with heA | heB
      · exact Or.inl ⟨heA, fun v hv hi => hno v hv ((inc_iff_of_le hsep.left_le heA).1 hi)⟩
      · exact Or.inr ⟨heB, fun v hv hi => hno v hv ((inc_iff_of_le hsep.right_le heB).1 hi)⟩
  · apply eq_empty_iff_forall_notMem.mpr
    rintro e ⟨heA, heB⟩
    exact hsep.disjoint_edgeSet.le_bot ⟨heA.1, heB.1⟩

/-- Deleting the vertex decreases the enlarged separation order by
exactly one, since it occurs on both enlarged sides. -/
theorem separationOrder_adjoin_vertex_eq_delete_add_one
    {α β : Type*} (A B : Hypergraph α β) (v : α) :
    separationOrder (A ∪ vertexHypergraph v) (B ∪ vertexHypergraph v) =
      separationOrder (A.deleteVertices {v}) (B.deleteVertices {v}) + 1 := by
  rw [separationOrder_adjoin_vertex]
  have heq : insert v (A.vertexSet ∩ B.vertexSet) =
      insert v ((A.vertexSet \ {v}) ∩ (B.vertexSet \ {v})) := by
    ext x
    simp only [mem_insert_iff, mem_inter_iff, mem_sdiff, mem_singleton_iff]
    tauto
  have hfin : ((A.vertexSet \ {v}) ∩ (B.vertexSet \ {v})).Finite :=
    A.vertexSet_finite.subset (fun _ hx => hx.1.1)
  have hvnot : v ∉ (A.vertexSet \ {v}) ∩ (B.vertexSet \ {v}) :=
    fun hx => hx.1.2 rfl
  rw [heq, ncard_insert_of_notMem hvnot hfin]
  rfl

/-- After adjoining the vertex on both sides, X (2.9) and deletion
give the selected pair in the new tangle. This proves the tangle
membership step of XII (7.3), Claim (1), page 262. -/
theorem delete_pair_mem_tangle_of_adjoin_order
    {α β : Type*} {G A B : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hT : IsTangle G θ T)
    (hm : (A, B) ∈ T) {v : α} (hv : v ∈ G.vertexSet)
    (hord : separationOrder (A ∪ vertexHypergraph v) (B ∪ vertexHypergraph v) < θ) :
    (A.deleteVertices {v}, B.deleteVertices {v}) ∈ deleteVerticesTangle G {v} T θ := by
  have hm' := adjoin_vertex_mem_tangle hT hm hv hord
  refine ⟨isSeparation_deleteVertices (hT.isSeparation hm) {v}, ?_,
    (A ∪ vertexHypergraph v, B ∪ vertexHypergraph v), hm', ?_,
    deleteVertices_adjoin_vertex A v, deleteVertices_adjoin_vertex B v⟩
  · change separationOrder (A.deleteVertices {v}) (B.deleteVertices {v}) < θ - ({v} : Set α).ncard
    rw [ncard_singleton]
    rw [separationOrder_adjoin_vertex_eq_delete_add_one] at hord
    omega
  · intro x hx
    have hxv : x = v := hx
    subst x
    exact ⟨Or.inr rfl, Or.inr rfl⟩

end GraphMinor.GM12
