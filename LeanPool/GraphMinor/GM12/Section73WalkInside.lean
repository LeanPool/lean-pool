/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73HubCircuitInside
import LeanPool.GraphMinor.GM12.Section73UnchangedCircuit

/-!
# The lifted-walk inside containment

This proves the inside comparison of XII (7.3), Claim (1),
page 262, for the short new walks used by its metric argument.
Outside the merged region the walk point sets agree. Each circuit
of the new walk either avoids the hub and is unchanged, or passes
through the hub and has the proved old splice. Both circuit
comparisons place its inside in the old walk's inside together
with the merged region. Taking their union proves the claim.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 Hypergraph

/-- Graph Minors XII, (7.3), Claim (1), page 262, for new walks
of length less than twice the new tangle order. These are the
walks used in both distance comparisons. The old and new
circuit cases and their selected-disc comparisons are discharged. -/
theorem theorem_7_3_claim_1_short_walk
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    {v : S} {ins ins' : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hins' : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins')
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J)
    {B : Set S} (hB : IsClosedDisc B) (hBr : B ⊆ r')
    (hAB : ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ⊆ discInt B)
    (hfixB : ∀ x ∉ discInt B, f x = x)
    {a : S} (W : GraphWalk J.toGraph a a) (W' : GraphWalk K.toGraph a a)
    (hWshort : W.length < 2 * (θ - 1))
    (hpoints : (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r')
    (hedges : ∀ e ∈ W.edges, ∀ g ∈ spokeReplacementEdges K J v f e, g ∈ W'.edges) :
    insWalk ins' J W ⊆ insWalk ins K W' ∪ r' := by
  have hV : J.V ⊆ K.V := by
    intro x hx
    rw [hJV, image_radial_vertices_eq hS hK hE hv hr' hvr' hfix hcollapse] at hx
    rcases hx with hx | hxv
    · exact hx.1
    · exact hxv ▸ hK.2.1.2.1 hv
  have hvJ : v ∈ J.V := hJV.symm ▸ ⟨v, hK.2.1.2.1 hv, hcollapse v (Or.inl rfl)⟩
  have hretain : ∀ e x y, J.toGraph.IsLink e x y → x ≠ v → y ≠ v → e ∈ K.E := by
    intro e x y hel
    obtain ⟨_, _, _, _, hret⟩ := exists_edge_walk_lift hS hK hE hv hr' hvr'
      f hfix hcollapse hfibre hJV hJE hel
    exact hret
  intro z hz
  change z ∈ insOf ins' (walkDrawing J W) at hz
  rcases hz with hz | hz
  · by_cases hzr : z ∈ r'
    · exact Or.inr hzr
    · have hzOld : z ∈ (walkDrawing K W').U := (hpoints.superset ⟨hz, hzr⟩).1
      exact Or.inl (Or.inl hzOld)
  · obtain ⟨C, ⟨hC, hCW⟩, hzC⟩ := mem_iUnion₂.mp hz
    have hClen : C.length ≤ W.length := by
      apply (ncard_le_ncard (fun e he => ?_) W.edges.finite_toSet).trans (ncard_mem_list_le W.edges)
      have hem := hCW.2 he
      rwa [walkDrawing_E] at hem
    have hCshort : C.length + 2 < 2 * θ := by omega
    by_cases hvC : v ∈ C.V
    · exact circuit_inside_subset_lifted_walk_through_hub hS hθ hT hins hins'
        hK hE hv hr' hvr' f hfix hcollapse hfibre hJV hJE hJ.2.1 hJ.1
        hB hBr hAB hfixB W W' hpoints hedges hC hCW hvC hCshort hzC
    · exact Or.inl (circuit_inside_subset_lifted_walk_of_notMem_hub hS hθ hT hv
        hK.2.1 hJ hr' hvr' hvJ hV hretain hins hins' W W' hpoints hC hCW hvC hCshort hzC)

end GraphMinor.GM12
