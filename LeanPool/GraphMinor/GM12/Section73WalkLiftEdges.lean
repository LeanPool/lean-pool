/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkLift
public import LeanPool.GraphMinor.GM12.Section73ReplacementEdges
import LeanPool.GraphMinor.GM12.Section73WalkSubstitutionEdges
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# The lifted walk contains all its replacement edges

For XII (7.3), Claim (1), page 262, retain the edge containment
from each spoke replacement when assembling the lifted walk.
This supplements its length, image, and outside point-set identities
with the old edges needed to build the lifted circuit.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

open Classical in
/-- The constructed closed lift contains every old edge of the
replacement paths for the new spokes it uses. This is the
circuit-containment step of XII (7.3), Claim (1), page 262. -/
theorem exists_closed_walk_lift_with_edges
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hJpre : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsPreRadialDrawing J)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {a : S} (W : GraphWalk J.toGraph a a) :
    ∃ W' : GraphWalk K.toGraph a a,
      W'.length = W.length + 2 * walkVertexCount v W ∧
      f '' (walkDrawing K W').U = (walkDrawing J W).U ∧
      (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r' ∧
      ∀ e ∈ W.edges, ∀ g ∈ spokeReplacementEdges K J v f e, g ∈ W'.edges := by
  obtain ⟨hV, hfixV, hloopless⟩ :=
    walk_lift_vertex_properties hS hK hE hv hr' hvr' f hfix hcollapse hJV hJpre
  have hpaths : ∀ e x y, J.toGraph.IsLink e x y →
      ∃ P : GraphWalk K.toGraph x y,
        P.length = (if x = v ∨ y = v then 2 else 1) ∧
        f '' (walkDrawing K P).U = closure e ∧
        (walkDrawing K P).U \ r' = closure e \ r' ∧
        ∀ g ∈ spokeReplacementEdges K J v f e, g ∈ P.edges := by
    intro e x y hel
    obtain ⟨P, hP, hPimage, hPpts, _⟩ := exists_edge_walk_lift hS hK hE hv hr' hvr' f hfix
      hcollapse hfibre hJV hJE hel
    exact ⟨P, hP, hPimage, hPpts,
      spokeReplacementEdges_subset_edge_lift hS ⟨hK.1, hK.2.1⟩ hv f hfibre hunique hel P hP hPimage⟩
  exact exists_closed_walk_substitution_with_edge_sets (spokeReplacementEdges K J v f)
    f hfixV hV hloopless hpaths W

end GraphMinor.GM12
