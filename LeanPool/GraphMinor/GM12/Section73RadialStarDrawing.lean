/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73RadialStar
public import LeanPool.GraphMinor.GM12.Section73StarDrawing
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# The drawing after contraction of the radial star

In XII (7.3), page 261, collapse all radial spokes at the deleted
vertex. A surviving spoke has one old end different from that
vertex. It can meet the collapsed star only at its other end, so
its image remains a line. The image drawing has exactly the images
of the surviving edges and fixes the drawing after vertex deletion.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A surviving radial edge meets the collapsed star in at most one
vertex. This is the geometric condition needed for the image drawing
in XII (7.3), page 261. -/
theorem radial_edge_inter_star
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    {g : Set S} (hg : g ∈ K.E) (hvg : v ∉ closure g) :
    (closure g ∩ ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)).Subsingleton ∧
      closure g ∩ ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ⊆ K.V := by
  let A : Set S := {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e
  have hvertex : closure g ∩ A ⊆ K.V := by
    rintro x ⟨hxg, hxA⟩
    rcases hxA with rfl | hxA
    · exact False.elim (hvg hxg)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxA
      exact closure_inter_subset_V hg he.1 (fun h => hvg (h.symm ▸ he.2)) ⟨hxg, hxe⟩
  have hOld : A ∩ Γ.U ⊆ {v} := by
    rintro x ⟨hxA, hxΓ⟩
    rcases hxA with hxv | hxA
    · exact hxv
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxA
      obtain ⟨r, hr, u, hu, hel, hline, hsub⟩ := radial_spoke_ends_at_vertex hS hK hv he.1 he.2
      rcases hsub hxe with hxr | hxv
      · exact False.elim (region_subset hr hxr hxΓ)
      · exact hxv
  obtain ⟨a, ha, r, hr, b, hb, hbK, hcap, _⟩ := spoke_ends hK hS hg
  have hsubset : closure g ∩ A ⊆ {b} := by
    rintro x ⟨hxg, hxA⟩
    rcases hcap.subset ⟨hxg, hvertex ⟨hxg, hxA⟩⟩ with hxa | hxb
    · have hxΓ : x ∈ Γ.U := by rw [hxa]; exact Γ.V_subset_U ha
      have hxv : x = v := hOld ⟨hxA, hxΓ⟩
      exact False.elim (hvg (hxv ▸ hxg))
    · exact hxb
  exact ⟨fun _ hx _ hy => (hsubset hx).trans (hsubset hy).symm, hvertex⟩

/-- The image of the radial drawing under an exact star collapse
is a drawing with precisely the surviving edge images. This is the
drawing construction in XII (7.3), page 261. -/
theorem exists_radial_star_image_drawing
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    (f : C(S, S))
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) :
    ∃ H : Drawing S, H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} := by
  let C : Set (Set S) := {e ∈ K.E | v ∈ closure e}
  have hnot : ∀ g ∈ K.E \ C, v ∉ closure g := by
    intro g hg hvg
    exact hg.2 ⟨hg.1, hvg⟩
  have hlines : ∀ g ∈ K.E \ C, ∃ a b, IsLineWithEnds (closure g) a b ∧
      closure g ∩ K.V = {a, b} := by
    intro g hg
    obtain ⟨a, ha, r, hr, b, hb, hbK, hcap, _⟩ := spoke_ends hK hS hg.1
    have hab : a ≠ b := fun h => region_subset hr (h ▸ hb) (Γ.V_subset_U ha)
    exact ⟨a, b, isLine_closure hg.1 hab hcap, hcap⟩
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_drawing_of_star_collapse (hK.2.2.1 hv) (Or.inl rfl)
    (fun e he x hx => Or.inr (mem_iUnion₂.mpr ⟨e, he, hx⟩)) hlines
    (fun g hg => (radial_edge_inter_star hS hK hv hg.1 (hnot g hg)).1)
    (fun g hg => (radial_edge_inter_star hS hK hv hg.1 (hnot g hg)).2) f hcollapse hfibre
  have hCE : K.E \ C = {g ∈ K.E | v ∉ closure g} := by
    ext g
    exact ⟨fun hg => ⟨hg.1, hnot g hg⟩, fun hg => ⟨hg.1, fun h => hg.2 h.2⟩⟩
  exact ⟨H, hHU, hHV, hCE ▸ hHE⟩

/-- Construct the drawing after the radial-star contraction in XII
(7.3), page 261. Its vertices and surviving edges are exactly the
images of the old ones, and the deleted drawing is fixed pointwise. -/
theorem exists_contracted_radial_star_drawing
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g) :
    ∃ (f : C(S, S)) (H : Drawing S), Function.Surjective f ∧
      (∀ x ∈ (deleteVertices Γ {v}).U, f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) ∧
      H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} := by
  obtain ⟨f, hsurj, hfix, hcollapse, hfibre⟩ := exists_radial_star_collapse hS hK hv hunique
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_radial_star_image_drawing hS hK hv f hcollapse hfibre
  exact ⟨f, H, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE⟩

/-- The contracted radial-star drawing agrees with the original
outside the region of the deleted vertex. This establishes the
unchanged part of the drawing in XII (7.3), page 261, before deleting
parallel spokes that bound empty discs. -/
theorem exists_contracted_radial_star_drawing_in_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    ∃ (f : C(S, S)) (H : Drawing S), Function.Surjective f ∧
      (∀ x ∉ r', f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) ∧
      H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} ∧
      H.U \ r' = K.U \ r' ∧ H.V \ r' = K.V \ r' ∧
      (∀ B : Set S, (f '' B) \ r' = B \ r') := by
  obtain ⟨f, hsurj, hfix, hcollapse, hfibre⟩ :=
    exists_radial_star_collapse_in_region hS hK hv hunique hr' hvr'
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_radial_star_image_drawing hS hK hv f hcollapse hfibre
  have hsub := radial_star_subset_deleted_region hS hK hv hr' hvr'
  have himage := (collapse_image_diff_eq hfibre hfix hsub).2
  refine ⟨f, H, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE, ?_, ?_, himage⟩
  · rw [hHU]
    exact himage K.U
  · rw [hHV]
    exact himage K.V

end GraphMinor.GM12
