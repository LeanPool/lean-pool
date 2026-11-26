/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section4PathFacts
import LeanPool.GraphMinor.GM12.Section4ConnectedSideBound
import LeanPool.GraphMinor.GM11.Walks

/-!
# Turning the connecting drawings into a controlled minor

The last paragraph of XII (4.3), page 251, uses the connected
subdrawings supplied by (3.2) as the branch subgraphs, and the
selected free edges as their joining edges. The graph links give
the two required incidences. The connected-branch order bound
supplies the remaining tangle-control condition.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14 Hypergraph

/-- Walk-connected drawing branches are connected as hypergraphs. -/
theorem isConnectedSub_toHypergraph_of_connected_drawing
    {S : Type*} [TopologicalSpace S] {H : Drawing S} (hH : IsConnectedDrawing H) :
    IsConnectedSub H.toHypergraph := by
  intro x hx y hy
  obtain ⟨W⟩ := hH x hx y hy
  induction W with
  | nil hv => exact .refl _
  | @cons x z y e hl R ih =>
    by_cases hxz : x = z
    · subst z
      exact ih hl.right_mem hy
    · have hxe : H.toHypergraph.Inc e x := by
        refine ⟨hl.edge_mem, hl.left_mem, ?_⟩
        have h : x ∈ closure e ∩ H.V := by rw [hl.2.2.2]; simp
        exact h.1
      have hze : H.toHypergraph.Inc e z := by
        refine ⟨hl.edge_mem, hl.right_mem, ?_⟩
        have h : z ∈ closure e ∩ H.V := by rw [hl.2.2.2]; simp
        exact h.1
      have hadj : H.toHypergraph.skeleton.Adj x z := ⟨hxz, e, hxe, hze⟩
      exact hadj.reachable.trans (ih hl.right_mem hy)

/-- The branch-assembly step of XII (4.3), page 251, for a
loopless target. Each branch contains ends of two sufficiently
distant edges, which ensures the required separation-order bound. -/
theorem controlsMinor_of_connecting_drawings
    {S α β : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {L : Graph α β} {θ k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (H : α → Drawing S) (f : β → Set S)
    (hHs : ∀ v ∈ L.vertexSet, (H v).IsSubdrawing Γ)
    (hconn : ∀ v ∈ L.vertexSet, IsConnectedDrawing (H v))
    (hdisj : ∀ u ∈ L.vertexSet, ∀ v ∈ L.vertexSet, u ≠ v → Disjoint (H u).V (H v).V)
    (hlinks : ∀ e u v, L.IsLink e u v →
      ∃ x ∈ (H u).V, ∃ y ∈ (H v).V, Γ.toGraph.IsLink (f e) x y)
    (hloopless : ∀ e v, ¬ L.IsLink e v v)
    (hinj : ∀ e ∈ L.edgeSet, ∀ g ∈ L.edgeSet, e ≠ g → f e ≠ f g)
    (hcard : L.vertexSet.ncard ≤ θ) (hk : 2 * L.vertexSet.ncard ≤ k)
    (hwitness : ∀ v ∈ L.vertexSet, ∃ (e g : Set S) (x y : S),
      e ∈ Γ.E ∧ g ∈ Γ.E ∧ x ∈ (H v).V ∧ y ∈ (H v).V ∧
        x ∈ closure e ∧ y ∈ closure g ∧ k + 4 ≤ d e g) :
    ControlsMinor Γ.toHypergraph θ T L := by
  refine ⟨fun v => (H v).toHypergraph, f, ?_, ?_, ?_, ?_, hinj, hcard, ?_⟩
  · intro v hv
    obtain ⟨e, g, x, y, _, _, hx, _, _⟩ := hwitness v hv
    exact ⟨subdrawing_toHypergraph_le (hHs v hv), ⟨x, hx⟩,
      isConnectedSub_toHypergraph_of_connected_drawing (hconn v hv)⟩
  · exact hdisj
  · intro e u v hl _
    obtain ⟨x, hx, y, hy, hxy⟩ := hlinks e u v hl
    refine ⟨hxy.edge_mem, ⟨x, hx, ?_⟩, y, hy, ?_⟩
    · refine ⟨hxy.edge_mem, hxy.left_mem, ?_⟩
      have h : x ∈ closure (f e) ∩ Γ.V := by rw [hxy.2.2.2]; simp
      exact h.1
    · refine ⟨hxy.edge_mem, hxy.right_mem, ?_⟩
      have h : y ∈ closure (f e) ∩ Γ.V := by rw [hxy.2.2.2]; simp
      exact h.1
  · intro e v hl
    exact False.elim (hloopless e v hl)
  · intro A B hAB hord v hv hsub
    obtain ⟨e, g, x, y, he, hg, hx, hy, hxe, hyg, hfar⟩ := hwitness v hv
    have hbound := separation_order_ge_of_connected_distant_edges hS hm (hconn v hv)
      (hHs v hv) he hg hx hy hxe hyg hfar hk hAB hsub
    exact (not_lt_of_ge hbound) hord

end GraphMinor.GM12
