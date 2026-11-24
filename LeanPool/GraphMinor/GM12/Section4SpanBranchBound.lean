/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section4SpanSeparation
import LeanPool.GraphMinor.GM12.Section4ConnectedSideBound

/-!
# The small-side bound for an enlarged embedded branch

At the end of XII (4.4), page 252, an enlarged branch contains a
connected drawn subgraph joining two distant selected vertices.
If an ambient small side contained that branch, pull the separation
back to the drawing. Its order cannot increase. The control
condition puts it in the drawing tangle, and (4.1) gives the
contradictory lower bound on its order.
-/

public section

namespace GraphMinor.GM12

open Set Surface Hypergraph GM14 GM15

/-- The final order estimate in XII (4.4), page 252, also used in
(4.5), page 253. An enlarged branch containing a distant connected
drawn subgraph cannot lie on an ambient small side. -/
theorem not_subset_small_side_of_embedded_distant_drawing
    {S α β : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {G : Graph α β} {Γ D : Drawing S}
    (η : SpanEmbedding Γ G) {θstar θ m : ℕ}
    {Tstar : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hC : IsControllingTangle G Γ η θstar θ Tstar T) (hmθ : m ≤ θ)
    (hD : IsConnectedDrawing D) (hDΓ : D.IsSubdrawing Γ)
    {u v : S} (hu : u ∈ D.V) (hv : v ∈ D.V) (hfar : 2 * m ≤ d {u} {v})
    {X : Set α} (hDX : η.vMap '' D.V ⊆ X)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ Tstar) (horder : separationOrder A B < m) :
    ¬ X ⊆ A.vertexSet := by
  intro hXA
  have hsep := hC.isTangle_star.isTangle.isSeparation hAB
  obtain ⟨AH, BH, hRestr, hAV, _, _, _, horderH⟩ :=
    exists_span_restricted_separation hC.isTangle_star.finite_V hC.isTangle_star.finite_E Γ η hsep
  have hmem : (AH, BH) ∈ T := (hC.controls hsep (horder.trans_le hmθ) hRestr).mp hAB
  have hDA : D.V ⊆ AH.vertexSet := by
    intro x hx
    rw [hAV]
    exact ⟨hDΓ.1 hx, hXA (hDX (mem_image_of_mem η.vMap hx))⟩
  have hbound := separation_order_ge_of_connected_distant_vertices hS hm hD hDΓ hu hv hfar hmem hDA
  exact (not_lt_of_ge (hbound.trans horderH)) horder

end GraphMinor.GM12
