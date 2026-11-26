/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73EdgeWalkLift
public import LeanPool.GraphMinor.GM12.Section73WalkSubstitution

/-!
# Lifting walks of the cleaned contraction

In XII (7.3), page 261, replace every spoke at the merged hub by its
two-edge old path, and use one old edge for every other spoke. All
new radial vertices are old vertices. The resulting closed walk has
length larger by twice the number of visits to the merged hub.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The cleaned radial vertices are fixed old vertices, and its links have distinct ends. -/
theorem walk_lift_vertex_properties
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hJV : J.V = f '' K.V)
    (hJpre : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsPreRadialDrawing J) :
    J.V ⊆ K.V ∧ (∀ x ∈ J.V, f x = x) ∧
      (∀ e x y, J.toGraph.IsLink e x y → x ≠ y) := by
  have hvertices : ∀ x ∈ J.V, x ∈ K.V ∧ f x = x := by
    intro x hx
    rw [hJV, image_radial_vertices_eq hS hK hE hv hr' hvr' hfix hcollapse] at hx
    rcases hx with hx | hxv
    · exact ⟨hx.1, hfix x hx.2⟩
    · have heq : x = v := hxv
      subst x
      exact ⟨hK.2.1.2.1 hv, hcollapse v (Or.inl rfl)⟩
  refine ⟨fun x hx => (hvertices x hx).1, fun x hx => (hvertices x hx).2, ?_⟩
  intro e x y hel hxy
  subst y
  have hb := bipartite_of_preRadial hJpre e x x hel
  by_cases hx : x ∈ (deleteVertices Γ {v}).V
  · exact (hb.mp hx) hx
  · exact hx (hb.mpr hx)

open Classical in
/-- The lifted closed walk in Graph Minors XII, (7.3), page 261,
exists and has length exactly twice the number of hub occurrences
more than the new walk. The replacement paths are constructed from
the old radial drawing, with no assumed walk-lifting step. -/
theorem exists_closed_walk_lift
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
    {a : S} (W : GraphWalk J.toGraph a a) :
    ∃ W' : GraphWalk K.toGraph a a,
      W'.length = W.length + 2 * walkVertexCount v W ∧
      f '' (walkDrawing K W').U = (walkDrawing J W).U ∧
      (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r' := by
  obtain ⟨hV, hfixV, hloopless⟩ :=
    walk_lift_vertex_properties hS hK hE hv hr' hvr' f hfix hcollapse hJV hJpre
  have hpaths : ∀ e x y, J.toGraph.IsLink e x y →
      ∃ P : GraphWalk K.toGraph x y,
        P.length = (if x = v ∨ y = v then 2 else 1) ∧
        f '' (walkDrawing K P).U = closure e ∧
        (walkDrawing K P).U \ r' = closure e \ r' := by
    intro e x y hel
    obtain ⟨P, hP, hPimage, hPpts, _⟩ := exists_edge_walk_lift hS hK hE hv hr' hvr' f hfix
      hcollapse hfibre hJV hJE hel
    exact ⟨P, hP, hPimage, hPpts⟩
  exact exists_closed_walk_substitution_with_points f hfixV hV hloopless hpaths W

end GraphMinor.GM12
