/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkInside
import LeanPool.GraphMinor.GM12.Section73HubWalkImage
import LeanPool.GraphMinor.GM12.Section73UnchangedCircuit

/-!
# The merged hub stays inside the lifted walk

For XII (7.3)(ii), page 262, the new walk encloses the merged
hub. If the walk visits it, a replacement star spoke puts the
deleted vertex in the old walk. Otherwise a circuit whose inside
contains the hub omits the hub itself. That circuit is unchanged
and has the same old inside. Thus the deleted vertex lies in
the inside of the lifted walk in either case.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 Hypergraph

/-- A new walk enclosing the merged hub lifts to a walk enclosing
the deleted vertex. This proves the point-inside assertion at the
end of XII (7.3)(ii), page 262. -/
theorem hub_mem_inside_lifted_walk
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
    {a : S} (W : GraphWalk J.toGraph a a) (W' : GraphWalk K.toGraph a a)
    (hWshort : W.length < 2 * (θ - 1))
    (hpoints : (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r')
    (hedges : ∀ e ∈ W.edges, ∀ g ∈ spokeReplacementEdges K J v f e, g ∈ W'.edges)
    (hvInside : v ∈ insWalk ins' J W) : v ∈ insWalk ins K W' := by
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
  have hwalk : v ∈ (walkDrawing J W).U → v ∈ insWalk ins K W' := by
    intro hvWU
    exact Or.inl (hub_mem_lifted_walk_of_mem_walk hS hK hE hv hr' hvr' f hfix hfibre
      hJV hJE hvJ W W' hedges hvWU)
  change v ∈ insOf ins' (walkDrawing J W) at hvInside
  rcases hvInside with hvWU | hvC
  · exact hwalk hvWU
  · obtain ⟨C, ⟨hC, hCW⟩, hvC⟩ := mem_iUnion₂.mp hvC
    by_cases hvCV : v ∈ C.V
    · exact hwalk (hCW.U_subset (C.V_subset_U hvCV))
    · have hClen : C.length ≤ W.length := by
        apply (ncard_le_ncard (fun e he => ?_) W.edges.finite_toSet).trans
          (ncard_mem_list_le W.edges)
        have hem := hCW.2 he
        rwa [walkDrawing_E] at hem
      have hshort : C.length + 2 < 2 * θ := by omega
      exact circuit_inside_subset_lifted_walk_of_notMem_hub hS hθ hT hv hK.2.1 hJ hr' hvr'
        hvJ hV hretain hins hins' W W' hpoints hC hCW hvCV hshort hvC

end GraphMinor.GM12
