/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73LiftedSpokeEdges
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# The edges of the replacement paths

In XII (7.3), page 261, a new spoke at the merged hub is replaced
by the old surviving spoke and the star spoke to its old region
hub. Record these old edges from their incidence and image data.
When the star spokes are unique, every two-edge lift with the
required image contains these edges.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The old edges of the two-edge paths replacing a spoke in
XII (7.3), page 261. The surviving spoke maps to the new edge,
and the other spoke joins its old hub to the deleted vertex. -/
@[expose] def spokeReplacementEdges
    {S : Type*} [TopologicalSpace S] (K J : Drawing S) (v : S) (f : S → S)
    (e : Set S) : Set (Set S) :=
  {d | ∃ (z : S) (g : Set S) (u : S), J.toGraph.IsLink e v z ∧
    v ∉ closure g ∧ f '' g = e ∧ K.toGraph.IsLink g u z ∧
    (d = g ∨ K.toGraph.IsLink d v u)}

open Classical in
/-- Every old replacement edge occurs in a one- or two-edge lift
of the new edge with the specified image. The uniqueness of star
spokes identifies the first edge of the two-edge lift. This is
the edge containment needed for XII (7.3), Claim (1), page 262. -/
theorem spokeReplacementEdges_subset_edge_lift
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    (f : S → S)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {e : Set S} {x y : S} (hel : J.toGraph.IsLink e x y)
    (W : GraphWalk K.toGraph x y)
    (hlen : W.length = if x = v ∨ y = v then 2 else 1)
    (himage : f '' (walkDrawing K W).U = closure e) :
    ∀ d ∈ spokeReplacementEdges K J v f e, d ∈ W.edges := by
  rintro d ⟨z, g, u, hnew, hvg, hfg, hgu, hd⟩
  have hgW : g ∈ W.edges := old_edge_mem_lift_of_image hS hK hv hgu.1 hvg f hfibre W (by
    rw [himage, hfg]
    exact subset_closure)
  rcases hd with rfl | hd
  · exact hgW
  · have hstar : ∀ a ∈ K.E, K.toGraph.IsLink a v u → a = d :=
      fun a ha hal => hunique a ha d hd.1 u hal hd
    rcases hel.eq_and_eq_or_eq_and_eq hnew with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have htwo : W.length = 2 := by simpa only [true_or, ite_true] using hlen
      exact star_edge_mem_two_edge_lift hgu hvg hstar W htwo hgW
    · have htwo : W.reverse.length = 2 := by
        rw [GraphWalk.length_reverse]
        simpa only [or_true, ite_true] using hlen
      have hgRev : g ∈ W.reverse.edges := by
        rwa [GraphWalk.edges_reverse, List.mem_reverse]
      have hdRev := star_edge_mem_two_edge_lift hgu hvg hstar W.reverse htwo hgRev
      rwa [GraphWalk.edges_reverse, List.mem_reverse] at hdRev

end GraphMinor.GM12
