/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73StarCollapse
public import LeanPool.GraphMinor.GM12.Section73NoParallel
public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM12.Section73EdgeContraction
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# The radial star at a deleted vertex

For XII (7.3), page 261, the spokes at the deleted vertex form a
finite star after the selected-disc reduction. Distinct spokes meet
only at their old end. Their closures miss the drawing after vertex
deletion. The finite-star collapse therefore fixes that drawing
pointwise and identifies exactly the star to its centre.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Orient a radial spoke incident with an old vertex toward its
region hub. This records its line and region for XII (7.3). -/
theorem radial_spoke_ends_at_vertex
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} (hK : PreRad (PaintingOrDrawing.drawing Γ) K)
    {v : S} (hv : v ∈ Γ.V) {e : Set S} (he : e ∈ K.E) (hve : v ∈ closure e) :
    ∃ r ∈ Γ.R, ∃ u, u ∈ r ∧ K.toGraph.IsLink e v u ∧
      IsLineWithEnds (closure e) v u ∧ closure e ⊆ r ∪ {v} := by
  obtain ⟨w, hw, r, hr, u, hur, huK, hcap, _⟩ := spoke_ends hK hS he
  have hvK : v ∈ K.V := hK.2.2.1 hv
  have hvw : v = w := by
    rcases hcap.subset ⟨hve, hvK⟩ with h | h
    · exact h
    · exact False.elim (region_subset hr (h ▸ hur) (Γ.V_subset_U hv))
  subst w
  have hvu : v ≠ u := fun h => region_subset hr (h ▸ hur) (Γ.V_subset_U hv)
  exact ⟨r, hr, u, hur, ⟨he, hvK, huK, hcap⟩,
    isLine_closure he hvu hcap,
    closure_spoke_subset_region_vertex hS hK.1 hK.2 he hr hur hcap⟩

/-- Distinct spokes of the reduced radial star are lines meeting
only at the centre, as used in XII (7.3), page 261. -/
theorem radial_star_lines_and_intersections
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} (hK : PreRad (PaintingOrDrawing.drawing Γ) K)
    {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g) :
    (∀ e ∈ {e ∈ K.E | v ∈ closure e}, ∃ u, IsLineWithEnds (closure e) v u) ∧
    (∀ e ∈ {e ∈ K.E | v ∈ closure e}, ∀ g ∈ {e ∈ K.E | v ∈ closure e},
      e ≠ g → closure e ∩ closure g ⊆ {v}) := by
  let E : Set (Set S) := {e ∈ K.E | v ∈ closure e}
  have hlines : ∀ e ∈ E, ∃ u, IsLineWithEnds (closure e) v u := by
    intro e he
    obtain ⟨r, hr, u, hu, hel, hline, _⟩ := radial_spoke_ends_at_vertex hS hK hv he.1 he.2
    exact ⟨u, hline⟩
  have halllines : ∀ g ∈ K.E, ∃ a b, IsLineWithEnds (closure g) a b ∧
      closure g ∩ K.V = {a, b} := by
    intro g hg
    obtain ⟨a, ha, r, hr, b, hb, hbK, hcap, _⟩ := spoke_ends hK hS hg
    have hab : a ≠ b := fun h => region_subset hr (h ▸ hb) (Γ.V_subset_U ha)
    exact ⟨a, b, isLine_closure hg hab hcap, hcap⟩
  have hmeet : ∀ e ∈ E, ∀ g ∈ E, e ≠ g → closure e ∩ closure g ⊆ {v} := by
    intro e he g hg heg x hx
    obtain ⟨r, hr, u, hu, hel, hline, _⟩ := radial_spoke_ends_at_vertex hS hK hv he.1 he.2
    have hvu : v ≠ u := lineWithEnds_ends_ne hline
    have hsub := closure_inter_subsingleton_of_unique_link hel hvu halllines
      (fun g hg hgl => (hunique e he.1 g hg u hel hgl).symm) g hg.1 heg.symm
    exact hsub ⟨hg.2, he.2⟩ ⟨hx.2, hx.1⟩ |>.symm
  exact ⟨hlines, hmeet⟩

/-- The reduced radial star contracts to the deleted vertex while
fixing the remaining drawing. This is the simultaneous topological
contraction used in XII (7.3), page 261. -/
theorem exists_radial_star_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} (hK : PreRad (PaintingOrDrawing.drawing Γ) K)
    {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g) :
    ∃ f : C(S, S), Function.Surjective f ∧
      (∀ x ∈ (deleteVertices Γ {v}).U, f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) := by
  let E : Set (Set S) := {e ∈ K.E | v ∈ closure e}
  obtain ⟨hlines, hmeet⟩ := radial_star_lines_and_intersections hS hK hv hunique
  have hdelete := deleteVertices_isSubdrawing Γ {v}
  have hvnot : v ∉ (deleteVertices Γ {v}).U := by
    intro hvU
    have hvV := (isSubdrawing_U_inter_V hdelete).subset ⟨hvU, hv⟩
    exact ((deleteVertices_V Γ {v}).subset hvV).2 rfl
  have havoid : Disjoint ({v} ∪ ⋃ e ∈ E, closure e) (deleteVertices Γ {v}).U := by
    apply disjoint_left.mpr
    intro x hx hxU
    rcases hx with rfl | hx
    · exact hvnot hxU
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨r, hr, u, hu, hel, hline, hsub⟩ := radial_spoke_ends_at_vertex hS hK hv he.1 he.2
      rcases hsub hxe with hxr | rfl
      · exact region_subset hr hxr (hdelete.U_subset hxU)
      · exact hvnot hxU
  have hfinite : {e ∈ K.E | v ∈ closure e}.Finite := K.finite_edges.subset fun _ he => he.1
  exact exists_star_collapse hS hfinite closure v hlines hmeet (deleteVertices Γ {v}).isClosed_U
    havoid

/-- The radial star lies in the region containing the deleted
vertex, as required for the contraction in XII (7.3), page 261. -/
theorem radial_star_subset_deleted_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e ⊆ r' := by
  have hdelete := deleteVertices_isSubdrawing Γ {v}
  intro x hx
  rcases hx with rfl | hx
  · exact hvr'
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    obtain ⟨r, hr, u, hu, hel, hline, hsub⟩ := radial_spoke_ends_at_vertex hS hK hv he.1 he.2
    have hdis : Disjoint (closure e) (deleteVertices Γ {v}).U := by
      apply disjoint_left.mpr
      intro y hy hyU
      rcases hsub hy with hyr | rfl
      · exact region_subset hr hyr (hdelete.U_subset hyU)
      · exact region_subset hr' hvr' hyU
    have hc : IsPreconnected (closure e) := by
      obtain ⟨p, _, _⟩ := hline
      have hrange : range (fun t : unitInterval => (p t).val) = closure e := by
        ext y
        constructor
        · rintro ⟨t, rfl⟩
          exact (p t).property
        · intro hy
          exact ⟨p.symm ⟨y, hy⟩, congrArg Subtype.val (p.apply_symm_apply ⟨y, hy⟩)⟩
      rw [← hrange]
      exact isPreconnected_range (continuous_subtype_val.comp p.continuous)
    exact subset_region hr' hc hdis he.2 hvr' hxe

/-- The radial-star contraction may fix every point outside the
region of the deleted vertex. This gives the unchanged part of the
radial drawing in XII (7.3), page 261. -/
theorem exists_radial_star_collapse_in_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    ∃ f : C(S, S), Function.Surjective f ∧ (∀ x ∉ r', f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hlines, hmeet⟩ := radial_star_lines_and_intersections hS hK hv hunique
  have hsub := radial_star_subset_deleted_region hS hK hv hr' hvr'
  have havoid : Disjoint ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) r'ᶜ :=
    disjoint_left.mpr fun _ hx hxn => hxn (hsub hx)
  have hfinite : {e ∈ K.E | v ∈ closure e}.Finite := K.finite_edges.subset fun _ he => he.1
  exact exists_star_collapse hS hfinite closure v hlines hmeet (region_isOpen hr').isClosed_compl
    havoid

end GraphMinor.GM12
