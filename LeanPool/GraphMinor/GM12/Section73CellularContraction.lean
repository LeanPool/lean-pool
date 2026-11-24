/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CollapseComplement
public import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.RadialTwoCell

/-!
# Two-cell drawings under a contraction

In XII (7.3), page 261, contracting the radial star preserves the
regions of the radial drawing. A homeomorphism of complements takes
connected components to connected components. Thus every new region
is homeomorphic to an old region, and remains an open disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A homeomorphism between drawing complements pairs each region
of the second drawing with a homeomorphic region of the first.
This transfers the radial regions in XII (7.3), page 261. -/
theorem exists_region_homeomorph_of_complement
    {S : Type*} [TopologicalSpace S] {K H : Drawing S}
    (e : ↥(K.Uᶜ) ≃ₜ ↥(H.Uᶜ)) {q : Set S} (hq : q ∈ H.R) :
    ∃ r, ∃ hr : r ∈ K.R, ∃ h : r ≃ₜ q,
      ∀ x : r, (h x).val = (e ⟨x.val, region_subset hr x.property⟩).val := by
  obtain ⟨y, hyq⟩ := region_nonempty hq
  let g : q → S := fun z => (e.symm ⟨z.val, region_subset hq z.property⟩).val
  have hgc : Continuous g := continuous_subtype_val.comp (e.symm.continuous.comp
    (continuous_subtype_val.subtype_mk fun z => region_subset hq z.property))
  let : PreconnectedSpace q := isPreconnected_iff_preconnectedSpace.mp (region_isPreconnected hq)
  have hgnot : ∀ z : q, g z ∉ K.U := fun z => (e.symm ⟨z.val, region_subset hq z.property⟩).property
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (hgnot ⟨y, hyq⟩)
  have hgr : range g ⊆ r := subset_region hr (isPreconnected_range hgc)
    (disjoint_left.mpr fun _ ⟨z, hzx⟩ hx => hgnot z (hzx ▸ hx))
    (mem_range_self ⟨y, hyq⟩) hxr
  let p : r → S := fun z => (e ⟨z.val, region_subset hr z.property⟩).val
  have hpc : Continuous p := continuous_subtype_val.comp (e.continuous.comp
    (continuous_subtype_val.subtype_mk fun z => region_subset hr z.property))
  let : PreconnectedSpace r := isPreconnected_iff_preconnectedSpace.mp (region_isPreconnected hr)
  have hpnot : ∀ z : r, p z ∉ H.U := fun z => (e ⟨z.val, region_subset hr z.property⟩).property
  have hpx : p ⟨g ⟨y, hyq⟩, hxr⟩ = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, region_subset
    hq hyq⟩)
  have hpq : range p ⊆ q := subset_region hq (isPreconnected_range hpc)
    (disjoint_left.mpr fun _ ⟨z, hzx⟩ hx => hpnot z (hzx ▸ hx))
    ⟨⟨g ⟨y, hyq⟩, hxr⟩, hpx⟩ hyq
  refine ⟨r, hr, {
    toFun := fun z => ⟨p z, hpq (mem_range_self z)⟩
    invFun := fun z => ⟨g z, hgr (mem_range_self z)⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := hpc.subtype_mk _
    continuous_invFun := hgc.subtype_mk _ }, ?_⟩
  · intro z
    apply Subtype.ext
    change (e.symm (e ⟨z.val, region_subset hr z.property⟩)).val = z.val
    exact congrArg (fun x : ↥(K.Uᶜ) => x.val) (e.symm_apply_apply ⟨z.val,
      region_subset hr z.property⟩)
  · intro z
    apply Subtype.ext
    change (e (e.symm ⟨z.val, region_subset hq z.property⟩)).val = z.val
    exact congrArg (fun x : ↥(H.Uᶜ) => x.val) (e.apply_symm_apply ⟨z.val,
      region_subset hq z.property⟩)
  · intro z
    rfl

/-- A homeomorphism of drawing complements preserves the two-cell
property. This supplies the region-topology step in the contraction
of XII (7.3), page 261. -/
theorem isTwoCell_of_complement_homeomorph
    {S : Type*} [TopologicalSpace S] [LocallyConnectedSpace S]
    {K H : Drawing S} (hK : (PaintingOrDrawing.drawing K).IsTwoCell)
    (e : ↥(K.Uᶜ) ≃ₜ ↥(H.Uᶜ)) : (PaintingOrDrawing.drawing H).IsTwoCell := by
  refine ⟨hK.1, ?_⟩
  intro q hq
  obtain ⟨r, hr, erq, _⟩ := exists_region_homeomorph_of_complement e hq
  obtain ⟨er⟩ := (hK.2 r hr).2
  exact ⟨region_isOpen hq, ⟨er.trans erq⟩⟩

/-- A surjective collapse inside a two-cell drawing preserves its
two-cell property. This is the contraction step of XII (7.3),
page 261, before the empty-disc cleanup. -/
theorem isTwoCell_image_of_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [LocallyConnectedSpace S] {K H : Drawing S}
    (hK : (PaintingOrDrawing.drawing K).IsTwoCell)
    {A : Set S} (hAK : A ⊆ K.U) (f : C(S, S)) (hsurj : Function.Surjective f)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hHU : H.U = f '' K.U) : (PaintingOrDrawing.drawing H).IsTwoCell := by
  obtain ⟨e, _⟩ := exists_homeomorph_collapse_complement hAK f hsurj hfibre
  exact isTwoCell_of_complement_homeomorph hK
    (e.trans (Homeomorph.setCongr (congrArg compl hHU.symm)))

/-- The radial-star image drawing is two-cell before parallel
spokes bounding empty discs are deleted. This is the topological
contraction used in XII (7.3), page 261. -/
theorem radial_star_image_isTwoCell
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K H : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {v : S} (hv : v ∈ Γ.V) (f : C(S, S)) (hsurj : Function.Surjective f)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hHU : H.U = f '' K.U) : (PaintingOrDrawing.drawing H).IsTwoCell := by
  let : CompactSpace S := hS.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hAK : {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e ⊆ K.U := by
    intro x hx
    rcases hx with rfl | hx
    · exact K.V_subset_U (hK.2.1.2.1 hv)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact K.closure_subset_U he.1 hxe
  exact isTwoCell_image_of_collapse
    (radial_isTwoCell_of_drawing hS hK) hAK f hsurj hfibre hHU

/-- Every region of a collapsed drawing is exactly the image of an
old region, with the collapse restricting to a homeomorphism there.
This locates the faces used in the empty-disc cleanup of XII (7.3),
page 261. -/
theorem exists_region_image_of_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    {K H : Drawing S} {A : Set S} (hAK : A ⊆ K.U)
    (f : C(S, S)) (hsurj : Function.Surjective f)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hHU : H.U = f '' K.U) {q : Set S} (hq : q ∈ H.R) :
    ∃ r ∈ K.R, q = f '' r ∧ Nonempty (r ≃ₜ q) := by
  obtain ⟨e, he⟩ := exists_homeomorph_collapse_complement hAK f hsurj hfibre
  let e' : ↥(K.Uᶜ) ≃ₜ ↥(H.Uᶜ) :=
    e.trans (Homeomorph.setCongr (congrArg compl hHU.symm))
  have he' : ∀ x : ↥(K.Uᶜ), (e' x).val = f x := he
  obtain ⟨r, hr, h, hh⟩ := exists_region_homeomorph_of_complement e' hq
  have hmap : ∀ x : r, (h x).val = f x := fun x =>
    (hh x).trans (he' ⟨x.val, region_subset hr x.property⟩)
  refine ⟨r, hr, ?_, ⟨h⟩⟩
  apply Eq.symm
  apply Subset.antisymm
  · rintro y ⟨x, hxr, rfl⟩
    rw [← hmap ⟨x, hxr⟩]
    exact (h ⟨x, hxr⟩).property
  · intro y hyq
    let x : r := h.symm ⟨y, hyq⟩
    exact ⟨x.val, x.property,
      (hmap x).symm.trans (congrArg Subtype.val (h.apply_symm_apply ⟨y, hyq⟩))⟩

end GraphMinor.GM12
