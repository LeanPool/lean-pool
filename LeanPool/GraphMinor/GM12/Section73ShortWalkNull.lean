/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkPathLift
public import LeanPool.GraphMinor.GM12.Section73EdgeWalkLift
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Null-homotopy of short walks after vertex deletion

For the representativity step of XII (7.3), page 261, lift a closed
walk of the new radial drawing to the old one. If its increased
length is below the old slope bound, the realized old path is
null-homotopic. Composing its contraction with the star-collapse map
and comparing edge paths gives a null-homotopy of the realized new
walk. The comparison uses the constructed replacement paths.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

open Classical in
/-- A new radial walk whose lifted length is below the old slope
bound is null-homotopic. This proves the old-to-new short-walk step
in the representativity argument of XII (7.3), page 261. -/
theorem walkPath_null_of_vertex_deletion_lift
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
    {k : ℕ} {ins : Drawing S → Set S} (hs : IsSlope K k ins)
    (q : ∀ e x y, J.toGraph.IsLink e x y → Path x y)
    (hq : ∀ e x y (h : J.toGraph.IsLink e x y), range (q e x y h) ⊆ closure e)
    {a : S} (W : GraphWalk J.toGraph a a)
    (hshort : W.length + 2 * walkVertexCount v W < k) :
    (walkPath q W).Homotopic (Path.refl a) := by
  have hloopK : ∀ e x y, K.toGraph.IsLink e x y → x ≠ y := by
    intro e x y hel hxy
    subst y
    have hb := bipartite_of_preRadial hK.2.1 e x x hel
    by_cases hx : x ∈ Γ.V
    · exact (hb.mp hx) hx
    · exact hx (hb.mpr hx)
  have hloopJ : ∀ e x y, J.toGraph.IsLink e x y → x ≠ y := by
    intro e x y hel hxy
    subst y
    have hb := bipartite_of_preRadial hJpre e x x hel
    by_cases hx : x ∈ (deleteVertices Γ {v}).V
    · exact (hb.mp hx) hx
    · exact hx (hb.mpr hx)
  obtain ⟨p, hp⟩ := exists_edge_paths hloopK
  have hp' : ∀ e x y (h : K.toGraph.IsLink e x y), range (p e x y h) ⊆ closure e :=
    fun e x y h => (hp e x y h).subset
  have hV : J.V ⊆ K.V := by
    intro x hx
    rw [hJV, image_radial_vertices_eq hS hK hE hv hr' hvr' hfix hcollapse] at hx
    rcases hx with hx | hxv
    · exact hx.1
    · exact hxv ▸ hK.2.1.2.1 hv
  have hfixV : ∀ x ∈ J.V, f x = x := by
    intro x hx
    rw [hJV, image_radial_vertices_eq hS hK hE hv hr' hvr' hfix hcollapse] at hx
    rcases hx with hx | hxv
    · exact hfix x hx.2
    · have hxv' : x = v := hxv
      rw [hxv']
      exact hcollapse v (Or.inl rfl)
  have hlines : ∀ e ∈ J.E, IsLine (closure e) := by
    intro e he
    obtain ⟨x, hx, y, hy, hcap⟩ := hJpre.2.2.2.2.1 e he
    have hxy : x ≠ y := fun h => hy.2 (h ▸ hx)
    obtain ⟨p, _, _⟩ := isLine_closure he hxy hcap
    exact ⟨p⟩
  have hpaths : ∀ e x y, J.toGraph.IsLink e x y →
      ∃ P : GraphWalk K.toGraph x y,
        P.length = (if x = v ∨ y = v then 2 else 1) ∧
        f '' (walkDrawing K P).U = closure e := by
    intro e x y hel
    obtain ⟨P, hP, hPimage, _⟩ := exists_edge_walk_lift hS hK hE hv hr' hvr'
      f hfix hcollapse hfibre hJV hJE hel
    exact ⟨P, hP, hPimage⟩
  obtain ⟨W', hWlen, hWhom⟩ := exists_closed_walk_path_lift f hfixV hV hloopJ hlines
    p hp' q hq hpaths W
  have hshort' : W'.length < k := hWlen ▸ hshort
  have hnull := walkPath_homotopic_refl_of_short_slope hS hs p hp' W' hshort'
  have hfa : f a = a := hfixV a (W.mem_vertexSet_of_mem_support W.start_mem_support)
  have hmapnull : (mapPathFixed f hfa hfa (walkPath p W')).Homotopic (Path.refl a) := by
    have hm := (hnull.map f).pathCast hfa.symm hfa.symm
    change (mapPathFixed f hfa hfa (walkPath p W')).Homotopic
      (mapPathFixed f hfa hfa (Path.refl a)) at hm
    have heq : mapPathFixed f hfa hfa (Path.refl a) = Path.refl a := by
      ext t
      exact hfa
    rw [heq] at hm
    exact hm
  exact hWhom.symm.trans hmapnull

end GraphMinor.GM12
