/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section74LeafRegion
import LeanPool.GraphMinor.GM12.Section74LeafAccess
import LeanPool.GraphMinor.GM12.Section74LeafSegment
import LeanPool.GraphMinor.GM12.Section74LeafLens
import LeanPool.GraphMinor.GM12.Section74SlitEnclosure
import LeanPool.GraphMinor.GM11.GlueFaces
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Deleting a leaf preserves disc regions

For the last gluing step needed in XII (7.4), pages 262--263,
consider a circle in the region enlarged by deleting a leaf.
Cut the leaf edge before the circle, continue its last segment
by an access line into the old region, and construct a slit lens.
The enclosure lemma bounds the circle in the enlarged region.
The open-disc criterion then proves that the region is a disc.
All other regions are old regions. The lens is transported from a small
copy, so the construction works in any surface universe.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem enclose_circle_in_deleted_leaf_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ Γ.V = {u, v})
    (hEdge : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f)
    {r Y : Set S} (hr : r ∈ Γ.R) (hdr : IsOpenDisc r) (hvr : v ∈ closure r)
    (hY : Y ∈ (deleteVertices Γ {v}).R) (hvY : v ∈ Y)
    {F : Set S} (hF : IsOArc F) (hFY : F ⊆ Y) :
    ∃ D : Set S, D ⊆ Y ∧ IsClosedDisc D ∧ discBd D = F := by
  let K := deleteVertices Γ {v}
  have huCap : u ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inl rfl : u ∈ ({u, v} : Set S))
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  have huK : u ∈ K.U := K.V_subset_U ((deleteVertices_V Γ {v}).symm ▸ ⟨huCap.2, huv⟩)
  have huF : u ∉ F := fun h => region_subset hY (hFY h) huK
  obtain ⟨P, L, w, hP, hL, hPL, hcapPL, hPF, hwu, hwv⟩ :=
    exists_line_split_with_prefix_avoiding_closed hEdge (isCompact_of_isOArc hF).isClosed huF
  have hPE : P ⊆ closure e := hPL ▸ subset_union_left
  have hLE : L ⊆ closure e := hPL ▸ subset_union_right
  have hLG : L ⊆ Γ.U := hLE.trans (Γ.closure_subset_U he)
  have hPG : P ⊆ Γ.U := hPE.trans (Γ.closure_subset_U he)
  have huL : u ∉ L := by
    intro huL
    have huw : u = w := by
      have hh : u ∈ P ∩ L := ⟨hP.left_mem, huL⟩
      rw [hcapPL] at hh
      exact hh
    exact hwu huw.symm
  have hvP : v ∉ P := by
    intro hvP
    have hvw : v = w := by
      have hh : v ∈ P ∩ L := ⟨hvP, hL.right_mem⟩
      rw [hcapPL] at hh
      exact hh
    exact hwv hvw.symm
  have hLY : L ⊆ Y := by
    intro x hxL
    by_cases hxV : x ∈ Γ.V
    · rcases hcap.subset ⟨hLE hxL, hxV⟩ with hxu | hxv
      · exact (huL (hxu ▸ hxL)).elim
      · exact hxv.symm ▸ hvY
    · have hxe : x ∈ e := (Γ.closure_diff_V he).subset ⟨hLE hxL, hxV⟩
      exact incident_edge_subset_deleted_vertex_region hvCap.2 hY hvY he hvCap.1 hxe
  obtain ⟨B, z, hB, hzr, hBr, hBG⟩ := exists_access_line_from_leaf hS he huv hcap hEdge hleaf hr hvr
  have hLB : L ∩ B = {v} := by
    apply Subset.antisymm
    · intro x hx
      have hxG : x ∈ B ∩ Γ.U := ⟨hx.2, hLG hx.1⟩
      rwa [hBG] at hxG
    · exact singleton_subset_iff.mpr ⟨hL.right_mem, hB.left_mem⟩
  let Z := K.U ∪ P
  have hZ : IsClosed Z := K.isClosed_U.union hP.isCompact.isClosed
  have hLZ : L ∩ Z = {w} := by
    apply Subset.antisymm
    · intro x hx
      rcases hx.2 with hxK | hxP
      · exact (region_subset hY (hLY hx.1) hxK).elim
      · have hh : x ∈ P ∩ L := ⟨hxP, hx.1⟩
        rwa [hcapPL] at hh
    · exact singleton_subset_iff.mpr ⟨hL.left_mem, Or.inr hP.right_mem⟩
  have hBZ : Disjoint B Z := by
    apply disjoint_left.mpr
    intro x hxB hxZ
    have hxG : x ∈ Γ.U := by
      rcases hxZ with hxK | hxP
      · exact (deleteVertices_isSubdrawing Γ {v}).U_subset hxK
      · exact hPG hxP
    have hxv : x = v := by
      have hh : x ∈ B ∩ Γ.U := ⟨hxB, hxG⟩
      rw [hBG] at hh
      exact hh
    rcases hxZ with hxK | hxP
    · exact region_subset hY hvY ((congrArg (fun y => y ∈ K.U) hxv).mp hxK)
    · exact hvP (hxv ▸ hxP)
  have hG : Γ.U ⊆ Z ∪ L := by
    intro x hxG
    by_cases hxK : x ∈ K.U
    · exact Or.inl (Or.inl hxK)
    · rcases mem_deleted_vertex_or_incident_edge hxG hxK with rfl | ⟨f, hf, hxf, hvf⟩
      · exact Or.inr hL.right_mem
      · have hfe : f = e := by
          by_contra hne
          exact hleaf f hf hne hvf
        have hxE : x ∈ closure e := subset_closure (hfe ▸ hxf)
        rw [← hPL] at hxE
        rcases hxE with hxP | hxL
        · exact Or.inl (Or.inr hxP)
        · exact Or.inr hxL
  have hwK : w ∉ K.U := region_subset hY (hLY hL.left_mem)
  obtain ⟨N, hN, hNY, hLN, hNG, hbdL⟩ := exists_leaf_slit_lens hS hL hB hLB hZ hLZ hBZ hG hLG
    subset_union_left hwK hY hvY
  have hYeq := deleted_leaf_region_eq hS he huv hcap hEdge hleaf hr hvr hY hvY
  have hShape : Y ⊆ r ∪ Γ.U := by
    intro x hx
    rw [hYeq] at hx
    rcases hx with (hxr | hxe) | rfl
    · exact Or.inl hxr
    · exact Or.inr (he.2.1 hxe).1
    · exact Or.inr (Γ.V_subset_U hvCap.2)
  have hrY : r ⊆ Y := by rw [hYeq]; exact subset_union_left.trans subset_union_left
  have hFZ : Disjoint F Z := by
    apply disjoint_left.mpr
    intro x hxF hxZ
    rcases hxZ with hxK | hxP
    · exact region_subset hY (hFY hxF) hxK
    · exact disjoint_left.mp hPF hxP hxF
  have hFA : F \ discInt N ⊆ r := by
    intro x hx
    apply (hShape (hFY hx.1)).resolve_right
    intro hxG
    have hxL : x ∈ L := (hG hxG).resolve_left (fun hxZ => disjoint_left.mp hFZ hx.1 hxZ)
    have hxN : x ∈ N := hLN hxL
    have hxBd : x ∉ discBd N := by
      intro hxBd
      have hxw : x = w := by
        have hh : x ∈ discBd N ∩ L := ⟨hxBd, hxL⟩
        rw [hbdL] at hh
        exact hh
      exact disjoint_left.mp hFZ hx.1 (Or.inr (hxw.symm ▸ hP.right_mem))
    exact hx.2 ⟨hxN, hxBd⟩
  exact exists_disc_bounding_circle_in_leaf_region_of_slit_disc hS hr hdr hrY hShape hN hNY
    hL hLN hNG hbdL hF hFA

/-- On a closed surface, the merged region formed by
deleting a leaf from a two-cell drawing is an open disc. -/
theorem isOpenDisc_deleted_leaf_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    (hΓ : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {e : Set S} (he : e ∈ Γ.E) {u v : S} (huv : u ≠ v)
    (hcap : closure e ∩ Γ.V = {u, v}) (hEdge : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f)
    {Y : Set S} (hY : Y ∈ (deleteVertices Γ {v}).R) (hvY : v ∈ Y) : IsOpenDisc Y := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  obtain ⟨x, hxY, hxG⟩ := exists_notMem_U (Γ := Γ) hS (region_isOpen hY) (region_nonempty hY)
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxG
  have hvr := deleted_vertex_mem_closure_of_region_meeting hS hvCap.2 hr hY hvY ⟨x, hxr, hxY⟩
  have huCap : u ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inl rfl : u ∈ ({u, v} : Set S))
  have huK : u ∈ (deleteVertices Γ {v}).U := (deleteVertices Γ {v}).V_subset_U
    ((deleteVertices_V Γ {v}).symm ▸ ⟨huCap.2, huv⟩)
  apply isOpenDisc_of_bound hS (region_isOpen hY) ⟨region_nonempty hY, region_isPreconnected hY⟩
    (fun h => region_subset hY (h.symm ▸ mem_univ u) huK)
  intro F hFY hF
  exact enclose_circle_in_deleted_leaf_region hS he huv hcap hEdge hleaf hr
    (hΓ.2 r hr) hvr hY hvY hF hFY

/-- Deleting a leaf from a two-cell drawing on a connected
closed surface preserves two-cellularity. The only enlarged
region is handled by the preceding slit-disc construction. -/
theorem isTwoCell_delete_leaf
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S}
    (hΓ : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {e : Set S} (he : e ∈ Γ.E) {u v : S} (huv : u ≠ v)
    (hcap : closure e ∩ Γ.V = {u, v}) (hEdge : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f) :
    (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell := by
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  refine ⟨inferInstance, ?_⟩
  intro Y hY
  by_cases hvY : v ∈ Y
  · exact isOpenDisc_deleted_leaf_region hS hΓ he huv hcap hEdge hleaf hY hvY
  · exact hΓ.2 Y (deleted_region_of_not_mem_vertex hS hvCap.2 hY hvY)

end GraphMinor.GM12
