/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DeletedRegions
public import LeanPool.GraphMinor.GM12.Section73RadialStar
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM12.Section73ImageArc

/-!
# The hub of the merged region

In XII (7.3), page 261, the radial-star contraction makes the deleted
vertex the hub of its new region. Every old radial vertex in that
region belongs to the star: an old drawing vertex there must be the
deleted vertex, and every old region hub there has a spoke to it by
radial maximality. Hence the image drawing has exactly one vertex
in the merged region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- All old radial vertices in the merged region belong to the
contracted star. This identifies the new hub in XII (7.3), page 261. -/
theorem radial_vertices_in_deleted_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    K.V ∩ r' ⊆ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e := by
  rintro w ⟨hwK, hwr'⟩
  by_cases hwΓ : w ∈ Γ.V
  · by_cases hwv : w = v
    · exact Or.inl hwv
    · have hwV : w ∈ (deleteVertices Γ {v}).V := by
        rw [deleteVertices_V]
        exact ⟨hwΓ, hwv⟩
      exact False.elim (region_subset hr' hwr' ((deleteVertices Γ {v}).V_subset_U hwV))
  · obtain ⟨r, hr, hwr⟩ := hK.2.1.2.2.2.1 w ⟨hwK, hwΓ⟩
    have hvcl : v ∈ closure r := deleted_vertex_mem_closure_of_region_meeting hS hv hr hr' hvr'
      ⟨w, hwr, hwr'⟩
    obtain ⟨e, he, hcap⟩ := exists_spoke_at ⟨hK.1, hK.2.1⟩ hK.2.2 hS hE hr hwr hwK hv hvcl
    have hve : v ∈ closure e := (hcap.superset (Or.inl rfl)).1
    have hwe : w ∈ closure e := (hcap.superset (Or.inr rfl)).1
    exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hve⟩, hwe⟩)

/-- An exact radial-star collapse fixing the outside of the merged
region puts precisely the new hub at the deleted vertex. This is
condition (ii) there for the construction in XII (7.3), page 261. -/
theorem image_radial_vertices_inter_deleted_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    {f : S → S} (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) :
    (f '' K.V) ∩ r' = {v} := by
  apply Subset.antisymm
  · rintro y ⟨⟨x, hxK, hxy⟩, hyr'⟩
    have hxr' : x ∈ r' := by
      by_contra hxn
      exact hxn ((hfix x hxn).symm.trans hxy ▸ hyr')
    have hxA := radial_vertices_in_deleted_region hS hK hE hv hr' hvr' ⟨hxK, hxr'⟩
    exact hxy.symm.trans (hcollapse x hxA)
  · intro y hy
    have hyv : y = v := hy
    rw [hyv]
    exact ⟨⟨v, hK.2.1.2.1 hv, hcollapse v (Or.inl rfl)⟩, hvr'⟩

/-- The image drawing has one hub in every region after vertex
deletion. The merged region has hub `v`; every other region keeps
its old hub. This proves condition (ii) of the radial construction
in XII (7.3), page 261, before removing empty parallel discs. -/
theorem image_radial_region_hub_unique
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    {f : S → S} (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) :
    ∀ s ∈ (deleteVertices Γ {v}).R, ∃! w, w ∈ s ∧ w ∈ f '' K.V := by
  intro s hs
  by_cases hsr : s = r'
  · subst s
    have hcap := image_radial_vertices_inter_deleted_region hS hK hE hv hr' hvr' hfix hcollapse
    refine ⟨v, ⟨hvr', ?_⟩, ?_⟩
    · exact (hcap.superset rfl).1
    · intro w hw
      exact hcap.subset ⟨hw.2, hw.1⟩
  · have hvs : v ∉ s := fun h => hsr (region_eq_of_mem hs hr' h hvr')
    have hsΓ : s ∈ Γ.R := deleted_region_of_not_mem_vertex hS hv hs hvs
    have hsout : ∀ x ∈ s, x ∉ r' := fun x hx hxr => hsr (region_eq_of_mem hs hr' hx hxr)
    have hsub := radial_star_subset_deleted_region hS ⟨hK.1, hK.2.1⟩ hv hr' hvr'
    have himage := (collapse_image_diff_eq hfibre hfix hsub).2 K.V
    obtain ⟨w, hw, huniq⟩ := hK.2.1.2.2.1 s hsΓ
    refine ⟨w, ⟨hw.1, ?_⟩, ?_⟩
    · exact ⟨w, hw.2, hfix w (hsout w hw.1)⟩
    · intro z hz
      have hzK : z ∈ K.V := (himage.subset ⟨hz.2, hsout z hz.1⟩).1
      exact huniq z ⟨hz.1, hzK⟩

end GraphMinor.GM12
