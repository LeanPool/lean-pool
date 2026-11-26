/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM12.Section4NonfreeEdgeCircuit
import LeanPool.GraphMinor.GM12.Section4PathEdgeSplit
import LeanPool.GraphMinor.GM12.Section4PathCircuitSeparation
import LeanPool.GraphMinor.GM12.Section4PathInside
import LeanPool.GraphMinor.GM12.Section4CircuitAtomDistance
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Section7

/-!
# Free edges in a path between distant edges

This proves claim (1) in XII (4.3), pages 249--250. A nonfree
path edge lies inside a radial circuit with at most one original
vertex. One of the two remaining path portions misses the circuit.
It forces its incident chosen edge into the same inside. Traversing
the circuit then bounds their distance by one, a contradiction.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM10 GM11 GM14

/-- Graph Minors XII (4.3), claim (1), pages 249--250: a path edge
at distance at least two from both chosen end edges has distinct
ends and those ends form a free set. -/
theorem free_path_edge_of_distant_ends
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle Γ θ T) (hθ : 2 ≤ θ)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {x y : S} (W : GraphWalk Γ.toGraph x y) (hW : W.IsSimple)
    {g₁ g₂ : Set S} (hg₁ : g₁ ∈ Γ.E) (hg₂ : g₂ ∈ Γ.E)
    (hx : x ∈ closure g₁) (hy : y ∈ closure g₂)
    {f : Set S} (hf : f ∈ W.edges)
    (hd₁ : 2 ≤ tangleMetric Γ K ins θ g₁ f)
    (hd₂ : 2 ≤ tangleMetric Γ K ins θ g₂ f) :
    ∃ a b, Γ.toGraph.IsLink f a b ∧ a ≠ b ∧ IsFreeSet Γ.toHypergraph T θ {a, b} := by
  obtain ⟨a, b, P, Q, hl, _, hPQ⟩ := exists_path_edge_split W hW hf
  have hab : a ≠ b := by
    intro heq
    exact Set.disjoint_left.mp hPQ P.end_mem_support (heq ▸ Q.start_mem_support)
  refine ⟨a, b, hl, hab, ?_⟩
  by_contra hfree
  obtain ⟨C, hC, hCs, hCl, _, hcount, hfC⟩ :=
    exists_short_radial_circuit_of_nonfree_edge hS hT hθ hK hd hl hab hfree
  have hdisc := (hd C hC hCs hCl).1
  have hbd : frontier (ins C) = C.U := by
    rw [← subBd_eq_frontier]
    exact (hd C hC hCs hCl).2.1
  have hfcl : closure f ⊆ ins C := hdisc.isClosed.closure_subset_iff.mpr hfC
  have ha : a ∈ ins C := hfcl (by
    have h : a ∈ closure f ∩ Γ.V := by rw [hl.2.2.2]; simp
    exact h.1)
  have hb : b ∈ ins C := hfcl (by
    have h : b ∈ closure f ∩ Γ.V := by rw [hl.2.2.2]; simp
    exact h.1)
  have hfA : f ∈ Γ.A := Or.inl (Or.inr hl.edge_mem)
  have hmeetf : (f ∩ ins C).Nonempty := by
    obtain ⟨z, hz⟩ := hl.edge_mem.1
    exact ⟨z, hz, hfC hz⟩
  rcases path_portion_disjoint_short_radial_circuit hK hCs hcount P Q hPQ with hP | hQ
  · have hgC := incident_edge_subset_of_path_inside hK hCs hdisc.isClosed hbd P hP ha hg₁ hx
    have hmeetg : (g₁ ∩ ins C).Nonempty := by
      obtain ⟨z, hz⟩ := hg₁.1
      exact ⟨z, hz, hgC hz⟩
    have hdist := atom_distance_le_circuit_vertex_count hS hK hd hC hCs hCl
      (Or.inl (Or.inr hg₁)) hfA hmeetg hmeetf
    exact (Nat.not_succ_le_self 1) (hd₁.trans (hdist.trans hcount))
  · have hgC := incident_edge_subset_of_path_inside hK hCs hdisc.isClosed hbd Q.reverse
      (by
        have heq : (walkDrawing Γ Q.reverse).U = (walkDrawing Γ Q).U := by
          ext z
          simp only [mem_walkDrawing_U, GraphWalk.support_reverse,
            GraphWalk.edges_reverse, List.mem_reverse]
        rw [heq]
        exact hQ) hb hg₂ hy
    have hmeetg : (g₂ ∩ ins C).Nonempty := by
      obtain ⟨z, hz⟩ := hg₂.1
      exact ⟨z, hz, hgC hz⟩
    have hdist := atom_distance_le_circuit_vertex_count hS hK hd hC hCs hCl
      (Or.inl (Or.inr hg₂)) hfA hmeetg hmeetf
    exact (Nat.not_succ_le_self 1) (hd₂.trans (hdist.trans hcount))

/-- Claim (1) of XII (4.3), expressed using the metric of the tangle. -/
theorem free_path_edge_of_metric_distant_ends
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d) (hθ : 2 ≤ θ)
    {x y : S} (W : GraphWalk Γ.toGraph x y) (hW : W.IsSimple)
    {g₁ g₂ : Set S} (hg₁ : g₁ ∈ Γ.E) (hg₂ : g₂ ∈ Γ.E)
    (hx : x ∈ closure g₁) (hy : y ∈ closure g₂)
    {f : Set S} (hf : f ∈ W.edges) (hd₁ : 2 ≤ d g₁ f) (hd₂ : 2 ≤ d g₂ f) :
    ∃ a b, Γ.toGraph.IsLink f a b ∧ a ≠ b ∧ IsFreeSet Γ.toHypergraph T θ {a, b} := by
  obtain ⟨hT, K, ins, hK, hd, heq⟩ := hm
  have hfE : f ∈ Γ.E := (walkDrawing_isSubdrawing Γ W).2
    ((walkDrawing_E Γ W).symm ▸ hf)
  have hfA : f ∈ Γ.A := Or.inl (Or.inr hfE)
  rw [heq g₁ (Or.inl (Or.inr hg₁)) f hfA] at hd₁
  rw [heq g₂ (Or.inl (Or.inr hg₂)) f hfA] at hd₂
  exact free_path_edge_of_distant_ends hS hT hθ hK hd W hW hg₁ hg₂ hx hy hf hd₁ hd₂

end GraphMinor.GM12
