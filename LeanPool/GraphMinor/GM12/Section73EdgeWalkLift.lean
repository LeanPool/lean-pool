/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73SpokeImages
import LeanPool.GraphMinor.GM12.Section73WalkPointSets
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Replacing a contracted radial edge by an old path

In XII (7.3), page 261, a new spoke at the merged hub corresponds
to a two-edge path through an old hub. Every other new spoke is an
unchanged old spoke. The old radial vertices outside the merged
region stay fixed, and every old hub inside it has a spoke to the
deleted vertex. This file constructs the replacement paths in both
orientations and proves their lengths.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

open Classical in
/-- Each edge of the cleaned contraction lifts to one old edge,
or to two old edges when incident with the merged hub. This is the
edge replacement defining the lifted walk in XII (7.3), page 261. -/
theorem exists_edge_walk_lift
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
    {e : Set S} {x y : S} (hel : J.toGraph.IsLink e x y) :
    ∃ W : GraphWalk K.toGraph x y,
      W.length = (if x = v ∨ y = v then 2 else 1) ∧
      f '' (walkDrawing K W).U = closure e ∧
      (walkDrawing K W).U \ r' = closure e \ r' ∧
      (x ≠ v → y ≠ v → e ∈ K.E) := by
  classical
  obtain ⟨g, hg, rfl⟩ := hJE hel.1
  obtain ⟨w, hw, r, hr, u, hur, huK, hcap, _⟩ := spoke_ends ⟨hK.1, hK.2.1⟩ hS hg.1
  have hwv : w ≠ v := fun h => hg.2 (h ▸ (hcap.superset (Or.inl rfl)).1)
  have huv : u ≠ v := fun h => region_subset hr (h ▸ hur) (Γ.V_subset_U hv)
  have hun : u ∉ Γ.V := fun hu => region_subset hr hur (Γ.V_subset_U hu)
  have hwnew : w ∈ (deleteVertices Γ {v}).V := by
    rw [deleteVertices_V]
    exact ⟨hw, hwv⟩
  have hwnr : w ∉ r' := fun hwr => region_subset hr' hwr ((deleteVertices Γ {v}).V_subset_U hwnew)
  have hfw : f w = w := hfix w hwnr
  have hwu : w ≠ u := fun h => region_subset hr (h ▸ hur) (Γ.V_subset_U hw)
  have hcapimage : closure (f '' g) ∩ J.V = {w, f u} := by
    rw [hJV, closure_image_inter_vertices (isLine_closure hg.1 hwu hcap)
      (radial_edge_inter_star hS ⟨hK.1, hK.2.1⟩ hv hg.1 hg.2).2 f hfibre,
      hcap, image_pair, hfw]
  have hpair : ({x, y} : Set S) = {w, f u} := hel.2.2.2.symm.trans hcapimage
  have hgl : K.toGraph.IsLink g w u := ⟨hg.1, hK.2.1.2.1 hw, huK, hcap⟩
  have hclimage : closure (f '' g) = f '' closure g :=
    closure_image_eq_of_compact_closure f.continuous (isLine_closure hg.1 hwu hcap).isCompact
  have houtside : closure (f '' g) \ r' = closure g \ r' := by
    rw [hclimage]
    exact (collapse_image_diff_eq hfibre hfix
      (radial_star_subset_deleted_region hS ⟨hK.1, hK.2.1⟩ hv hr' hvr')).2 (closure g)
  by_cases hur' : u ∈ r'
  · have hfu : f u = v := hcollapse u
      (radial_vertices_in_deleted_region hS hK hE hv hr' hvr' ⟨huK, hur'⟩)
    obtain ⟨k, hk, hkl⟩ := exists_spoke_to_hub_in_deleted_region hS hK hE hv hr' hvr' huK hun hur'
    let P : GraphWalk K.toGraph v w := .cons hkl (.cons hgl.symm (.nil (hK.2.1.2.1 hw)))
    have hPlen : P.length = 2 := by rfl
    have hkR : closure k ⊆ r' := by
      intro z hz
      apply radial_star_subset_deleted_region hS ⟨hK.1, hK.2.1⟩ hv hr' hvr'
      exact Or.inr (mem_iUnion₂.mpr ⟨k, ⟨hk, (hkl.2.2.2.superset (Or.inl rfl)).1⟩, hz⟩)
    have himagek : f '' closure k = {v} := by
      apply Subset.antisymm
      · rintro z ⟨a, hak, haz⟩
        exact haz.symm.trans (hcollapse a (Or.inr (mem_iUnion₂.mpr
          ⟨k, ⟨hk, (hkl.2.2.2.superset (Or.inl rfl)).1⟩, hak⟩)))
      · intro z hz
        have hzv : z = v := hz
        rw [hzv]
        exact ⟨v, (hkl.2.2.2.superset (Or.inl rfl)).1, hcollapse v (Or.inl rfl)⟩
    have hvimg : v ∈ closure (f '' g) := by
      have hvimg' := (hcapimage.superset (Or.inr rfl)).1
      rwa [hfu] at hvimg'
    have hPimage : f '' (walkDrawing K P).U = closure (f '' g) := by
      change f '' (walkDrawing K (.cons hkl (.cons hgl.symm (.nil (hK.2.1.2.1 hw))))).U = _
      rw [walkDrawing_two_edges_points, image_union, himagek, ← hclimage]
      exact union_eq_right.mpr (singleton_subset_iff.mpr hvimg)
    have hPpoints : (walkDrawing K P).U \ r' = closure (f '' g) \ r' := by
      change (walkDrawing K (.cons hkl (.cons hgl.symm (.nil (hK.2.1.2.1 hw))))).U \ r' = _
      rw [walkDrawing_two_edges_points, union_sdiff_distrib, sdiff_eq_empty.mpr hkR, empty_union,
        houtside]
    rw [hfu] at hpair
    rcases pair_eq_pair_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨P.reverse, by simpa only [GraphWalk.length_reverse, or_true, ite_true] using hPlen,
        ?_, ?_, fun _ hyn => False.elim (hyn rfl)⟩
      · rw [walkDrawing_reverse_points]
        exact hPimage
      · rw [walkDrawing_reverse_points]
        exact hPpoints
    · exact ⟨P, by simpa only [true_or, ite_true] using hPlen, hPimage, hPpoints,
        fun hxn _ => False.elim (hxn rfl)⟩
  · have hfu : f u = u := hfix u hur'
    have hdis := spoke_closure_disjoint_deleted_region hS ⟨hK.1, hK.2.1⟩ hr'
      hg.1 hg.2 hw hr hur hcap hur'
    have himage : f '' g = g := by
      apply Subset.antisymm
      · rintro z ⟨a, hag, haz⟩
        have haf : f a = a := hfix a (fun har' => disjoint_left.mp hdis (subset_closure hag) har')
        exact (haf.symm.trans haz) ▸ hag
      · intro z hzg
        exact ⟨z, hzg, hfix z (fun hzr' => disjoint_left.mp hdis (subset_closure hzg) hzr')⟩
    let P : GraphWalk K.toGraph w u := .cons hgl (.nil huK)
    have hPlen : P.length = 1 := by rfl
    have hPimage : f '' (walkDrawing K P).U = closure (f '' g) := by
      rw [walkDrawing_one_edge_points]
      exact hclimage.symm
    have hPpoints : (walkDrawing K P).U \ r' = closure (f '' g) \ r' := by
      rw [walkDrawing_one_edge_points, houtside]
    rw [hfu] at hpair
    rcases pair_eq_pair_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨P, by simpa only [hwv, huv, false_or, ite_false] using hPlen, hPimage, hPpoints, ?_⟩
      intro _ _
      change f '' g ∈ K.E
      rw [himage]
      exact hg.1
    · refine ⟨P.reverse, by simpa only [GraphWalk.length_reverse, huv, hwv, false_or,
        ite_false] using hPlen,
        ?_, ?_, ?_⟩
      · rw [walkDrawing_reverse_points]
        exact hPimage
      · rw [walkDrawing_reverse_points]
        exact hPpoints
      · intro _ _
        change f '' g ∈ K.E
        rw [himage]
        exact hg.1

end GraphMinor.GM12
