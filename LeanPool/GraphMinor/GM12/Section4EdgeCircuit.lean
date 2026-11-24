/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM12.Section4Separation
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# A short radial circuit enclosing an edge

The edge--region distance estimate in XII (4.3), claim (5),
page 250, can be witnessed around the edge. Put the edge and its
ends on the small side of their separation, whose order is at most
two. The third tangle axiom chooses this orientation. XII (1.1)
then gives a radial circuit enclosing the edge with at most two
original vertices.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 GM14 Hypergraph

/-- In order at least three, the edge with its ends is a tangle small side.
This is the orientation used to enclose an edge in XII (4.3). -/
theorem edge_small_side_mem_of_order_three
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) (hθ : 2 < θ)
    {e : Set S} (he : e ∈ Γ.E) :
    (edgeHypergraph Γ.toHypergraph e, Γ.toHypergraph.deleteEdges {e}) ∈ T := by
  have hsep := isSeparation_edgeHypergraph_deleteEdges (G := Γ.toHypergraph) he
  obtain ⟨a, b, hl⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he
  have hends : Γ.toHypergraph.ends e ⊆ {a, b} := by
    intro w hw
    rw [← hl.2.2.2]
    exact ⟨hw.2.2, hw.2.1⟩
  have hcount : (Γ.toHypergraph.ends e).ncard ≤ 2 :=
    (ncard_le_ncard hends (toFinite _)).trans ((ncard_insert_le a {b}).trans (by simp))
  have hord : separationOrder (edgeHypergraph Γ.toHypergraph e)
      (Γ.toHypergraph.deleteEdges {e}) ≤ 2 := by
    rw [separationOrder_edgeHypergraph_deleteEdges]
    exact hcount
  have hlt : separationOrder (edgeHypergraph Γ.toHypergraph e)
      (Γ.toHypergraph.deleteEdges {e}) < θ := hord.trans_lt hθ
  exact (hT.axiom1 hsep hlt).resolve_right fun h => hT.axiom3 h rfl

/-- An edge is enclosed by a short radial circuit with at most two
original vertices, providing the local metric witness in XII (4.3). -/
theorem exists_radial_circuit_around_edge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle Γ θ T) (hθ : 2 < θ)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {e : Set S} (he : e ∈ Γ.E) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
      (C.V ∩ Γ.V).ncard ≤ 2 ∧ e ⊆ ins C := by
  have hsep := isSeparation_edgeHypergraph_deleteEdges (G := Γ.toHypergraph) he
  obtain ⟨a, b, hl⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he
  have hends : Γ.toHypergraph.ends e ⊆ {a, b} := by
    intro w hw
    rw [← hl.2.2.2]
    exact ⟨hw.2.2, hw.2.1⟩
  have hcount : (Γ.toHypergraph.ends e).ncard ≤ 2 :=
    (ncard_le_ncard hends (toFinite _)).trans ((ncard_insert_le a {b}).trans (by simp))
  have hord : separationOrder (edgeHypergraph Γ.toHypergraph e)
      (Γ.toHypergraph.deleteEdges {e}) ≤ 2 := by
    rw [separationOrder_edgeHypergraph_deleteEdges]
    exact hcount
  have hlt : separationOrder (edgeHypergraph Γ.toHypergraph e)
      (Γ.toHypergraph.deleteEdges {e}) < θ := hord.trans_lt hθ
  have hm : (edgeHypergraph Γ.toHypergraph e, Γ.toHypergraph.deleteEdges {e}) ∈ T :=
    (hT.2.1.axiom1 hsep hlt).resolve_right fun h => hT.2.1.axiom3 h rfl
  obtain ⟨C, hC, hCs, hCl, hCV, heC⟩ :=
    (theorem_1_1_proof hS hT ⟨e, he⟩ hK hd hsep hlt).mp hm e (mem_singleton e)
  exact ⟨C, hC, hCs, hCl,
    (ncard_le_ncard hCV (edgeHypergraph Γ.toHypergraph e ∩
      Γ.toHypergraph.deleteEdges {e}).vertexSet_finite).trans hord, heC⟩

end GraphMinor.GM12
