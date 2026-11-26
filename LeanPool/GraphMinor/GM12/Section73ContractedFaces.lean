/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CellularContraction
public import LeanPool.GraphMinor.GM12.Section73RadialStar
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM12.Section73ImageIncidence

/-!
# Edges inside the contracted radial regions

For the cleanup in XII (7.3), page 261, each contracted radial
region comes from one old radial region and contains the image of
its old drawing edge. It contains at most one edge of the drawing
after vertex deletion. Indeed, those edges stay fixed, so any two
would already lie in the same old radial region, contradicting the
unique-edge property of a radial drawing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A contracted radial region contains an old edge image and at
most one surviving drawing edge. These are the faces to be cleaned
up in XII (7.3), page 261. -/
theorem contracted_radial_region_edges
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K H : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hsurj : Function.Surjective f) (hfix : ∀ x ∉ r', f x = x)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hHU : H.U = f '' K.U) {q : Set S} (hq : q ∈ H.R) :
    ∃ r ∈ K.R, q = f '' r ∧
      (∃ e ∈ Γ.E, f '' e ⊆ q) ∧
      (∀ e ∈ (deleteVertices Γ {v}).E, ∀ g ∈ (deleteVertices Γ {v}).E,
        e ⊆ q → g ⊆ q → e = g) := by
  let : CompactSpace S := hS.1
  have hAK : {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e ⊆ K.U := by
    intro x hx
    rcases hx with rfl | hx
    · exact K.V_subset_U (hK.2.1.2.1 hv)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact K.closure_subset_U he.1 hxe
  obtain ⟨r, hr, hqr, _⟩ := exists_region_image_of_collapse hAK f hsurj hfibre hHU hq
  have hfacts := regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  obtain ⟨e, he, her⟩ := hfacts.1 r hr
  refine ⟨r, hr, hqr, ⟨e, he, ?_⟩, ?_⟩
  · rw [hqr]
    exact image_mono her
  · have hpre : ∀ x, f x ∈ q → x ∈ r := by
      intro x hfx
      rw [hqr] at hfx
      obtain ⟨y, hyr, hyx⟩ := hfx
      rcases (hfibre x y).mp hyx.symm with hxy | hAxy
      · exact hxy ▸ hyr
      · exact False.elim (region_subset hr hyr (hAK hAxy.2))
    have hsub : ∀ g ∈ (deleteVertices Γ {v}).E, g ⊆ q → g ⊆ r := by
      intro g hg hgq x hxg
      have hxU : x ∈ (deleteVertices Γ {v}).U :=
        (deleteVertices Γ {v}).closure_subset_U hg (subset_closure hxg)
      have hxn : x ∉ r' := fun hxr' => region_subset hr' hxr' hxU
      apply hpre x
      rw [hfix x hxn]
      exact hgq hxg
    intro a ha b hb haq hbq
    have hdelete := deleteVertices_isSubdrawing Γ {v}
    exact hfacts.2.1 r hr a (hdelete.2 ha) b (hdelete.2 hb) (hsub a ha haq) (hsub b hb hbq)

end GraphMinor.GM12
