/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircuitVisitCount
public import LeanPool.GraphMinor.GM12.Section73DiscAttachment
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Ties

/-!
# Joining the boundary walks of disc pieces

The two-disc tie in XII (7.3), page 262, is enclosed by joining
the two circuit walks at their common vertex. Each circuit walk
visits a vertex at most once, so their concatenation visits it at
most twice. Their edges are disjoint, since the circuits meet in
only one point. Their total length is therefore bounded by the
length of any walk containing both circuits.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The circuit visit bound with a prescribed starting vertex. -/
theorem exists_circuit_walk_at_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T1Space S] {K C : Drawing S} {p : S}
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K) (hpC : p ∈ C.V) :
    ∃ W : GraphWalk K.toGraph p p, walkDrawing K W = C ∧
      W.length = C.length ∧ ∀ v, walkVertexCount v W ≤ 1 := by
  obtain ⟨P, hP, _, hV, hE⟩ := exists_walk_at hC hpC
  obtain ⟨W, hWS, hWE⟩ := hCK.exists_walk_up P
  have hW : W.IsSimpleClosed := by
    change W.support.tail.Nodup ∧ W.edges.Nodup
    rw [hWS, hWE]
    exact hP
  have hdraw : walkDrawing K W = C := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hWS, hV]
    · rw [walkDrawing_E, hWE, hE]
  have hlen : W.length = C.length := by
    change W.edges.length = C.E.ncard
    rw [hWE, hE]
    have hset : {e | e ∈ P.edges} = (P.edges.toFinset : Set (Set S)) := by ext e; simp
    rw [hset, ncard_coe_finset, List.toFinset_card_of_nodup hP.2]
  exact ⟨W, hdraw, hlen, walkVertexCount_le_one_of_isSimpleClosed hW⟩

/-- Subdrawings meeting in at most one point have disjoint edge
sets. A common edge would put its interior point in the vertex set. -/
theorem disjoint_edges_of_subsingleton_inter
    {S : Type*} [TopologicalSpace S] [T2Space S] {K C D : Drawing S}
    (hCK : C.IsSubdrawing K) (hDK : D.IsSubdrawing K)
    (hCD : (C.U ∩ D.U).Subsingleton) : Disjoint C.E D.E := by
  apply disjoint_left.mpr
  intro e heC heD
  obtain ⟨p, hpe⟩ := heC.1
  have hpC : p ∈ C.U := (heC.2.1 hpe).1
  have hpD : p ∈ D.U := (heD.2.1 hpe).1
  have hpV := mem_vertices_of_subdrawing_inter_singleton hCK hDK hpC hpD
    (fun x hx => hCD hx ⟨hpC, hpD⟩)
  exact ((hCK.2 heC).2.1 hpe).2 hpV

/-- The lengths of two edge-disjoint circuits contained in a walk
sum to at most the length of the walk. -/
theorem circuit_lengths_add_le_walk_length
    {S : Type*} [TopologicalSpace S] [T1Space S] {K C D : Drawing S}
    {u : S} (W : GraphWalk K.toGraph u u)
    (hCW : C.IsSubdrawing (walkDrawing K W))
    (hDW : D.IsSubdrawing (walkDrawing K W)) (hE : Disjoint C.E D.E) :
    C.length + D.length ≤ W.length := by
  change C.E.ncard + D.E.ncard ≤ W.edges.length
  rw [← ncard_union_eq hE C.finite_edges D.finite_edges]
  apply (ncard_le_ncard (fun e he => ?_) W.edges.finite_toSet).trans (ncard_mem_list_le W.edges)
  rcases he with he | he
  · have hh := hCW.2 he
    rwa [walkDrawing_E] at hh
  · have hh := hDW.2 he
    rwa [walkDrawing_E] at hh

end GraphMinor.GM12
