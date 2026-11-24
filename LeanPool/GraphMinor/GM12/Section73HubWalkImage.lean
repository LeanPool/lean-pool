/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkLiftEdges
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# A visited merged hub remains in the lifted walk

At the end of XII (7.3), page 262, a new walk used for distance
to the merged region must retain the deleted vertex after lifting.
If the hub is its initial vertex this holds directly. Otherwise
split the walk at a hub visit. Its next edge has a two-edge
replacement using a star spoke, whose old endpoint is the deleted
vertex. The recorded replacement edges put that spoke in the lift.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- If the merged hub belongs to the point set of the new walk,
it belongs to the point set of its constructed lift. This is the
walk-point assertion used in XII (7.3)(ii), page 262. -/
theorem hub_mem_lifted_walk_of_mem_walk
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hvJ : v ∈ J.V)
    {a : S} (W : GraphWalk J.toGraph a a) (W' : GraphWalk K.toGraph a a)
    (hedges : ∀ e ∈ W.edges, ∀ g ∈ spokeReplacementEdges K J v f e, g ∈ W'.edges)
    (hvW : v ∈ (walkDrawing J W).U) : v ∈ (walkDrawing K W').U := by
  have hvSupport : v ∈ W.support := by
    have hvV := (isSubdrawing_U_inter_V (walkDrawing_isSubdrawing J W)).subset ⟨hvW, hvJ⟩
    rw [walkDrawing_V] at hvV
    exact hvV
  by_cases hva : v = a
  · have haV : a ∈ (walkDrawing K W').V := by rw [walkDrawing_V]; exact W'.start_mem_support
    exact hva.symm ▸ (walkDrawing K W').V_subset_U haV
  obtain ⟨P, Q, hsplit⟩ := W.exists_append_of_mem hvSupport
  cases hQ : Q with
  | nil h => exact (hva rfl).elim
  | @cons _ z _ e hel R =>
    have heW : e ∈ W.edges := by
      rw [hsplit, GraphWalk.edges_append, hQ, GraphWalk.edges_cons]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨g, p, _, hvg, hfg, hpr, hpK, hpn, _, hgl⟩ :=
      exists_old_spoke_at_contracted_vertex hS hK hv hr' f hfix hfibre hJV hJE hel
    obtain ⟨k, _, hkl⟩ := exists_spoke_to_hub_in_deleted_region hS hK hE hv hr' hvr' hpK hpn hpr
    have hkW : k ∈ (walkDrawing K W').E := by
      rw [walkDrawing_E]
      exact hedges e heW k ⟨z, g, p, hel, hvg, hfg, hgl, Or.inr hkl⟩
    exact (walkDrawing K W').closure_subset_U hkW (hkl.2.2.2.superset (Or.inl rfl)).1

end GraphMinor.GM12
