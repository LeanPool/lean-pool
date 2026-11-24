/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section4
import LeanPool.GraphMinor.GM12.Section4EdgeRegionDistance
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM09.Basic

/-!
# A connected branch containing distant ends cannot be small

The final paragraph of XII (4.3), page 251, chooses two ends
of different selected edges inside one connected branch. A path
in that branch remains on the proposed small side. XII (4.1)
bounds the distance of its ends by twice the separation order.
The selected-edge distance forces that order to be large enough
to establish the control condition.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14 Hypergraph

/-- The connected-branch application of XII (4.1) in the final
paragraph of XII (4.3), page 251. -/
theorem separation_order_ge_of_connected_distant_vertices
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ H : Drawing S} {θ m : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hH : IsConnectedDrawing H) (hHs : H.IsSubdrawing Γ)
    {u v : S} (hu : u ∈ H.V) (hv : v ∈ H.V) (hfar : 2 * m ≤ d {u} {v})
    {A B : Hypergraph S (Set S)} (hAB : (A, B) ∈ T) (hHV : H.V ⊆ A.vertexSet) :
    m ≤ separationOrder A B := by
  obtain ⟨W₀⟩ := hH u hu v hv
  obtain ⟨W, hW, _, _⟩ := GM09.exists_isSimple_subwalk W₀
  let P := walkDrawing H W
  have hP : P.IsPathBetween u v := walkDrawing_isPathBetween H hW
  have hPs : P.IsSubdrawing H := walkDrawing_isSubdrawing H W
  have hbound := theorem_4_1_proof Γ P θ T d A B u v hS inferInstance hm (hHs.1 hu) (hHs.1 hv)
    hP (hPs.trans hHs) hAB (hPs.1.trans hHV)
  omega

/-- The order bound from two distinct selected-edge ends, used to
verify control in XII (4.3), page 251. -/
theorem separation_order_ge_of_connected_distant_edges
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ H : Drawing S} {θ m k : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hH : IsConnectedDrawing H) (hHs : H.IsSubdrawing Γ)
    {e f : Set S} (he : e ∈ Γ.E) (hf : f ∈ Γ.E)
    {u v : S} (hu : u ∈ H.V) (hv : v ∈ H.V)
    (hue : u ∈ closure e) (hvf : v ∈ closure f)
    (hfar : k + 4 ≤ d e f) (hk : 2 * m ≤ k)
    {A B : Hypergraph S (Set S)} (hAB : (A, B) ∈ T) (hHV : H.V ⊆ A.vertexSet) :
    m ≤ separationOrder A B := by
  have hdist := distant_edges_endpoints_distance_ge hS hm he hf (hHs.1 hu) (hHs.1 hv) hue hvf hfar
  exact separation_order_ge_of_connected_distant_vertices hS hm hH hHs hu hv
    (hk.trans hdist) hAB hHV

end GraphMinor.GM12
