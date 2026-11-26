/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73RadialStarDrawing
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM12.Section73MergedHub
import LeanPool.GraphMinor.GM12.Section73CellularContraction

/-!
# Incidence in the contracted radial drawing

In XII (7.3), page 261, the star collapse fixes the drawing after
vertex deletion. Its exact fibres then imply that the image radial
drawing meets that drawing precisely in its vertices. A surviving
edge closure has exactly the images of its old ends as ends, because
its intersection with the collapsed star contains only vertices.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The ends of a surviving edge under an exact collapse are the
images of its old ends when its closure meets the collapsed set only
in vertices. This is used for XII (7.3), page 261. -/
theorem closure_image_inter_vertices
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S}
    {A g : Set S} {u w : S} (hline : IsLineWithEnds (closure g) u w)
    (hvertex : closure g ∩ A ⊆ K.V) (f : C(S, S))
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A)) :
    closure (f '' g) ∩ (f '' K.V) = f '' (closure g ∩ K.V) := by
  rw [closure_image_eq_of_compact_closure f.continuous hline.isCompact]
  apply Subset.antisymm
  · rintro y ⟨⟨z, hzg, hzy⟩, ⟨a, haV, hay⟩⟩
    have hzV : z ∈ K.V := by
      rcases (hfibre z a).mp (hzy.trans hay.symm) with hza | hzA
      · exact hza ▸ haV
      · exact hvertex ⟨hzg, hzA.1⟩
    exact ⟨z, ⟨hzg, hzV⟩, hzy⟩
  · rintro y ⟨z, ⟨hzg, hzV⟩, rfl⟩
    exact ⟨⟨z, hzg, rfl⟩, ⟨z, hzV, rfl⟩⟩

/-- The image radial drawing meets the deleted drawing exactly in
its vertices, all of which remain radial vertices. This proves
condition (i) in the construction of XII (7.3), page 261. -/
theorem image_radial_inter_deleted_drawing
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    {f : S → S} (hfix : ∀ x ∉ r', f x = x)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) :
    (deleteVertices Γ {v}).U ∩ (f '' K.U) = (deleteVertices Γ {v}).V ∧
      (deleteVertices Γ {v}).V ⊆ f '' K.V := by
  have hdelete := deleteVertices_isSubdrawing Γ {v}
  have hAR := radial_star_subset_deleted_region hS hK hv hr' hvr'
  have hout : ∀ x ∈ (deleteVertices Γ {v}).U, x ∉ r' :=
    fun x hx hxr => region_subset hr' hxr hx
  have hVsub : (deleteVertices Γ {v}).V ⊆ f '' K.V := by
    intro x hx
    exact ⟨x, hK.2.2.1 (hdelete.1 hx), hfix x (hout x ((deleteVertices Γ {v}).V_subset_U hx))⟩
  refine ⟨Subset.antisymm ?_ ?_, hVsub⟩
  · rintro x ⟨hxD, ⟨y, hyK, hyx⟩⟩
    have hyx' : y = x := by
      have heq : f y = f x := hyx.trans (hfix x (hout x hxD)).symm
      rcases (hfibre y x).mp heq with hyx' | hAx
      · exact hyx'
      · exact False.elim (hout x hxD (hAR hAx.2))
    have hxK : x ∈ K.U := hyx' ▸ hyK
    have hxΓV : x ∈ Γ.V := hK.2.1.subset ⟨hdelete.U_subset hxD, hxK⟩
    exact (isSubdrawing_U_inter_V hdelete).subset ⟨hxD, hxΓV⟩
  · intro x hxV
    obtain ⟨y, hyKV, hyx⟩ := hVsub hxV
    exact ⟨(deleteVertices Γ {v}).V_subset_U hxV, y, K.V_subset_U hyKV, hyx⟩

/-- Each surviving spoke image joins a vertex of the deleted
drawing to an image hub. This proves condition (iii) of the radial
construction in XII (7.3), page 261. -/
theorem image_radial_edge_ends
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    {g : Set S} (hg : g ∈ K.E) (hvg : v ∉ closure g) :
    ∃ a ∈ (deleteVertices Γ {v}).V, ∃ b ∈ (f '' K.V) \ (deleteVertices Γ {v}).V,
      closure (f '' g) ∩ (f '' K.V) = {a, b} := by
  have hdelete := deleteVertices_isSubdrawing Γ {v}
  have hout : ∀ x ∈ (deleteVertices Γ {v}).U, x ∉ r' :=
    fun x hx hxr => region_subset hr' hxr hx
  obtain ⟨a, ha, r, hr, b, hb, hbK, hcap, _⟩ := spoke_ends hK hS hg
  have hab : a ≠ b := fun h => region_subset hr (h ▸ hb) (Γ.V_subset_U ha)
  have haV : a ∈ (deleteVertices Γ {v}).V := by
    rw [deleteVertices_V]
    refine ⟨ha, ?_⟩
    intro hav
    exact hvg (hav ▸ (hcap.superset (Or.inl rfl)).1)
  have hfa : f a = a := hfix a (hout a ((deleteVertices Γ {v}).V_subset_U haV))
  have hfbnot : f b ∉ (deleteVertices Γ {v}).V := by
    intro hfbV
    have hfbU := (deleteVertices Γ {v}).V_subset_U hfbV
    have hfixfb : f (f b) = f b := hfix (f b) (hout (f b) hfbU)
    rcases (hfibre b (f b)).mp hfixfb.symm with hbfb | hAb
    · have hbV : b ∈ Γ.V := hbfb ▸ hdelete.1 hfbV
      exact region_subset hr hb (Γ.V_subset_U hbV)
    · exact hout (f b) hfbU (radial_star_subset_deleted_region hS hK hv hr' hvr' hAb.2)
  refine ⟨a, haV, f b, ⟨mem_image_of_mem f hbK, hfbnot⟩, ?_⟩
  rw [closure_image_inter_vertices (isLine_closure hg hab hcap)
    (radial_edge_inter_star hS hK hv hg hvg).2 f hfibre, hcap, image_pair, hfa]

/-- The drawing obtained by contracting the reduced radial star is
two-cell and satisfies the intersection, region-hub, and bipartition
conditions for a radial drawing of the deleted drawing. This is the
construction in XII (7.3), page 261, before the empty-disc cleanup. -/
theorem exists_contracted_radial_incidence
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
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
      (PaintingOrDrawing.drawing H).IsTwoCell ∧
      (deleteVertices Γ {v}).U ∩ H.U = (deleteVertices Γ {v}).V ∧
      (deleteVertices Γ {v}).V ⊆ H.V ∧
      (∀ s ∈ (deleteVertices Γ {v}).R, ∃! w, w ∈ s ∧ w ∈ H.V) ∧
      (∀ w ∈ H.V \ (deleteVertices Γ {v}).V, ∃ s ∈ (deleteVertices Γ {v}).R, w ∈ s) ∧
      (∀ e ∈ H.E, ∃ a ∈ (deleteVertices Γ {v}).V,
        ∃ b ∈ H.V \ (deleteVertices Γ {v}).V, closure e ∩ H.V = {a, b}) := by
  obtain ⟨f, H, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE, _, _, _⟩ :=
    exists_contracted_radial_star_drawing_in_region hS ⟨hK.1, hK.2.1⟩ hv hunique hr' hvr'
  have hinter := image_radial_inter_deleted_drawing hS ⟨hK.1, hK.2.1⟩ hv hr' hvr' hfix hfibre
  have hcap : (deleteVertices Γ {v}).U ∩ H.U = (deleteVertices Γ {v}).V := by
    rw [hHU]
    exact hinter.1
  refine ⟨f, H, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE,
    radial_star_image_isTwoCell hS hK hv f hsurj hfibre hHU, hcap, ?_, ?_, ?_, ?_⟩
  · rw [hHV]
    exact hinter.2
  · rw [hHV]
    exact image_radial_region_hub_unique hS hK hE hv hr' hvr' hfix hcollapse hfibre
  · intro w hw
    apply exists_region_of_notMem
    intro hwU
    exact hw.2 (hcap.subset ⟨hwU, H.V_subset_U hw.1⟩)
  · intro e he
    obtain ⟨g, hg, rfl⟩ := hHE.subset he
    obtain ⟨a, ha, b, hb, hends⟩ := image_radial_edge_ends hS ⟨hK.1, hK.2.1⟩ hv hr' hvr'
      f hfix hfibre hg.1 hg.2
    rw [hHV]
    exact ⟨a, ha, b, hb, hends⟩

end GraphMinor.GM12
