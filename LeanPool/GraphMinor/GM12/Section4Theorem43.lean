/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Induced
public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4NormalizedTarget
import LeanPool.GraphMinor.GM12.Section4TargetOrientation
import LeanPool.GraphMinor.GM12.Section4TopologicalFeasibility
import LeanPool.GraphMinor.GM12.Section4FeasibleControl
import LeanPool.GraphMinor.GM12.Section3GeometricReduction
import LeanPool.GraphMinor.GM12.Section4FreeEdgeDiscs
import LeanPool.GraphMinor.GM12.Section4Monotone

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.3): controlling a drawable minor

Replace the drawable target by a loopless drawable graph with two
incident edges at every vertex. Select widely separated free edges
of the host drawing and empty discs around them. The source target
drawing and the marked-disc homeomorphism prove topological
feasibility. Apply (3.2), verify control using (4.1), and pass back
to the original target by (4.2).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

universe u

/-- A drawing gives the same incidence hypergraph through its graph representation. -/
theorem drawing_hypergraph_eq_ofGraph
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S) :
    Γ.toHypergraph = Hypergraph.ofGraph Γ.toGraph Γ.finite_V Γ.finite_edges := by
  refine Hypergraph.ext (x := Γ.toHypergraph)
    (y := Hypergraph.ofGraph Γ.toGraph Γ.finite_V Γ.finite_edges) ?_ ?_ ?_
  · rfl
  · rfl
  funext e v
  apply propext
  change (e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e) ↔ ∃ w, Γ.toGraph.IsLink e v w
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet h.1
    have hv : v ∈ ({x, y} : Set S) := hxy.2.2.2 ▸ (show v ∈ closure e ∩ Γ.V from ⟨h.2.2, h.2.1⟩)
    rcases hv with hv | hv
    · subst v
      exact ⟨y, hxy⟩
    · have heq := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨x, hxy.symm⟩
  · rintro ⟨w, he, hv, hw, hcap⟩
    exact ⟨he, hv, ((hcap.symm).subset (by simp)).1⟩

/-- Graph Minors XII (4.3), pages 249--251, for the drawing itself.
The threshold is enlarged by taking a maximum with the connection
threshold, also covering an edgeless target. The only statement
hypotheses are the cited VII (7.5), (5.1), and (5.5). -/
theorem theorem_4_3_drawing
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {α β : Type*} {L : Graph α β} (D : GraphDrawing L S) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ),
      HasTangleMetric Γ θ T d → N ≤ θ → ControlsMinor Γ.toHypergraph θ T L := by
  obtain ⟨p, t, K, DK, hKV, hKE, hminor, hloop, htwo⟩ :=
    exists_normalized_target_replacement hS D
  obtain ⟨κ, hassign, hslots⟩ := exists_target_end_assignment K hKE hloop htwo
  have hl : ∀ i, K.IsLink i (κ (i, true)) (κ (i, false)) := by
    intro i
    obtain ⟨v, w, h⟩ := K.exists_isLink_of_mem_edgeSet (hKE ▸ mem_univ i)
    rcases hassign i v w h with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · rw [hv, hw]; exact h
    · rw [hv, hw]; exact h.symm
  have hne : ∀ i, κ (i, true) ≠ κ (i, false) := by
    intro i heq
    exact hloop i (κ (i, false)) (heq ▸ hl i)
  obtain ⟨k, hk, _, hcontrol⟩ :=
    exists_threshold_for_control_from_feasible_discs hS K κ hloop hassign hslots
  let N := max k (5 + t * (k + 7))
  refine ⟨N, hk.trans (le_max_left _ _), ?_⟩
  intro Γ θ T d hm hN
  have hkθ : k ≤ θ := (le_max_left _ _).trans hN
  obtain ⟨f, a, b, Δ, r, hdata, hdisj, hreg, hsep⟩ :=
    exists_spaced_free_edge_discs hS hm hk ((le_max_right _ _).trans hN)
  have hfeas := topologicallyFeasible_of_drawn_target hS K hKV hKE DK κ hl hne Δ a b
    (fun i => ⟨(hdata i).2.2.1, (hdata i).2.1, (hdata i).2.2.2.2.1⟩) hdisj
  have hc : ControlsMinor Γ.toHypergraph θ T K := hcontrol Γ θ T d f a b Δ r hm hkθ
    (fun i => ⟨(hdata i).1, (hdata i).2.1⟩)
    (fun i => ⟨(hdata i).2.2.1, (hdata i).2.2.2.2.2.1,
      (hdata i).2.2.2.2.2.1.symm.trans (hdata i).2.2.2.1⟩)
    hdisj hsep (fun i => ⟨(hdata i).2.2.2.2.2.2.2.1, (hdata i).2.2.2.2.2.2.2.2.2⟩)
    hreg (fun i => (hdata i).2.2.2.2.2.2.1) hfeas
  have heq := drawing_hypergraph_eq_ofGraph Γ
  rw [heq] at hc
  have hfinal := theorem_4_2_proof (G := Γ.toGraph) Γ.finite_V Γ.finite_edges
    (Set.toFinite _) (Set.toFinite _) hminor hc
  rwa [← heq] at hfinal

/-- Graph Minors XII (4.3), pages 249--251. The tangle induced in
an overgraph controls every drawable target once its order exceeds
the threshold. The overgraph is written as a hypergraph with the
same vertex and edge labels as the drawing. -/
theorem theorem_4_3_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {α β : Type*} {L : Graph α β} (D : GraphDrawing L S) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (G : Hypergraph S (Set S)),
      HasTangleMetric Γ θ T d → N ≤ θ → Γ.toHypergraph ≤ G →
      ControlsMinor G θ (inducedBySubgraph G Γ.toHypergraph θ T) L := by
  obtain ⟨N, hN, hdraw⟩ := theorem_4_3_drawing hS D
  refine ⟨N, hN, ?_⟩
  intro Γ θ T d G hm hθ hΓG
  exact controlsMinor_inducedBySubgraph hΓG (hdraw Γ θ T d hm hθ)

end GraphMinor.GM12
