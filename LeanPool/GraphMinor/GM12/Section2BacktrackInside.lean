/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2InsideHomotopy
public import LeanPool.GraphMinor.GM12.Section2NormalNoncover
public import LeanPool.GraphMinor.GM12.Section2Zero
import LeanPool.GraphMinor.GM11.LocalCone
import LeanPool.GraphMinor.GM11.Walks

/-!
# The inside in the one-visit backtracking case

In Case 1 of XII (2.1), page 244, a trace may go along one spoke
and return along the same spoke. A deformation to that line makes
the original circle null-homotopic in its region together with its
boundary vertex. A point of the drawing outside the selected disc
is also outside that set. The two-point contraction criterion then
puts the selected disc in that set. Its only possible atoms are
the region and the boundary vertex, both met by the trace.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A selected boundary disc lies in the region with its boundary
vertex restored whenever its embedded boundary contracts there.
This is the inside assertion in XII (2.1), Case 1's backtracking case. -/
theorem selected_disc_subset_region_vertex_of_null
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    {φ : C(Circle, S)} (hφ : IsEmbedding φ) (hn : Γ.IsNormal (range φ))
    {r D : Set S} {v : S} (hr : r ∈ Γ.R) (hvφ : v ∈ range φ)
    (hD : IsClosedDisc D) (hbd : subBd D = range φ)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hnull : ClosedCurveIsNullHomotopicIn (r ∪ {v}) φ) : D ⊆ r ∪ {v} := by
  have hnf : (PaintingOrDrawing.drawing Γ).IsNormal (frontier D) := by
    rw [← subBd_eq_frontier, hbd]
    exact hn
  obtain ⟨q, hqΓ, hqD, _⟩ := exists_support_point_outside_two_small_sides
    (Γ := .drawing Γ) hT hD.isCompact.isClosed hD.isCompact.isClosed hnf hnf hm hm
  have hvD : v ∈ D := by
    have hvb : v ∈ subBd D := hbd.symm ▸ hvφ
    exact hD.isCompact.isClosed.closure_subset_iff.mpr subset_rfl hvb.1
  have hqZ : q ∉ r ∪ {v} := by
    rintro (hqr | hqv)
    · exact region_subset hr hqr hqΓ
    · exact hqD (hqv.symm ▸ hvD)
  intro p hpD
  by_contra hpZ
  have hZpair : r ∪ {v} ⊆ ({p, q} : Set S)ᶜ := by
    intro x hx hpair
    simp only [mem_insert_iff, mem_singleton_iff] at hpair
    rcases hpair with hxp | hxq
    · exact hpZ (hxp ▸ hx)
    · exact hqZ (hxq ▸ hx)
  obtain ⟨c, hc, H⟩ := hnull
  have hnPair : ClosedCurveIsNullHomotopicIn ({p, q} : Set S)ᶜ φ :=
    ⟨c, hZpair hc, H.mono hZpair⟩
  exact ((curve_null_in_pair_compl_iff_not_mem_disc hS hφ hD hbd hqD).mp hnPair) hpD

/-- Deformation to a line in the region with its boundary vertex
restored supplies the contraction used in the backtracking case. -/
theorem selected_disc_subset_region_vertex_of_line_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    {φ ψ : C(Circle, S)} (hφ : IsEmbedding φ) (hn : Γ.IsNormal (range φ))
    {r D L : Set S} {v : S} (hr : r ∈ Γ.R) (hvφ : v ∈ range φ)
    (hD : IsClosedDisc D) (hbd : subBd D = range φ)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hL : IsLine L) (hLZ : L ⊆ r ∪ {v}) (hψL : range ψ ⊆ L)
    (hh : ClosedCurvesHomotopicIn (r ∪ {v}) φ ψ) : D ⊆ r ∪ {v} := by
  apply selected_disc_subset_region_vertex_of_null hS hT hφ hn hr hvφ hD hbd hm
  exact GM11.null_of_homotopic hLZ hh ((GM11.IsLine.isSimplyConnected hL).2 ψ hψL)

/-- Every atom meeting a disc contained in a region and one drawing
vertex meets any trace containing that vertex and the region's hub. -/
theorem meets_insWalk_of_subset_region_vertex
    {S : Type*} [TopologicalSpace S] [T1Space S] {Γ K : Drawing S}
    {r D c : Set S} {v w u : S} (hr : r ∈ Γ.R)
    (hD : D ⊆ r ∪ {v}) (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty)
    (W : GraphWalk K.toGraph u u) (hvW : v ∈ W.support) (hwW : w ∈ W.support) (hw : w ∈ r)
    (ins : Drawing S → Set S) : (c ∩ insWalk ins K W).Nonempty := by
  have recorded : ∀ x ∈ W.support, x ∈ insWalk ins K W := by
    intro x hx
    apply Or.inl
    apply (walkDrawing K W).V_subset_U
    rw [walkDrawing_V]
    exact hx
  obtain ⟨x, hxc, hxD⟩ := hcD
  rcases hD hxD with hxr | hxv
  · have hcr := atom_eq_region_of_meets hc hr ⟨x, hxc, hxr⟩
    exact ⟨w, hcr.symm ▸ hw, recorded w hwW⟩
  · have hvc : v ∈ c := hxv ▸ hxc
    exact ⟨v, hvc, recorded v hvW⟩

end GraphMinor.GM12
