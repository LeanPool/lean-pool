/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73Tangle
import LeanPool.GraphMinor.GM12.Section78
import LeanPool.GraphMinor.GM12.Section72RadialExists
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Removing a selected one-vertex disc before vertex contraction

The parallel-edge claim in the proof of XII (7.3), page 261, fails
when a loop is attached at the deleted vertex: the outer loop face
has two corners there even though deleting the vertex leaves a two-cell drawing.
The smallest correction first applies (7.2) to such selected insides.
Here we prove that this does not change the drawing after vertex
deletion. Its connected point set misses the one-vertex boundary.
The third tangle axiom provides a surviving vertex outside the disc,
so the whole deleted drawing lies outside it.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- If vertex deletion leaves a two-cell drawing, that drawing misses
every selected disc whose normal boundary meets just the deleted
vertex. This justifies the preprocessing needed in XII (7.3). -/
theorem deleted_drawing_disjoint_selected_vertex_disc [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) {v : S}
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    {D F : Set S} (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    Disjoint (deleteVertices Γ {v}).U D := by
  let Γ' := deleteVertices Γ {v}
  have hΓ : Γ'.IsSubdrawing Γ := deleteVertices_isSubdrawing Γ {v}
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hfront : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hvD : v ∈ D := hD.isClosed.closure_subset_iff.mpr subset_rfl
    ((hfront.symm ▸ hvFV.1).1)
  have hvnot : v ∉ Γ'.U := by
    intro hvU
    have hvV := (isSubdrawing_U_inter_V hΓ).subset ⟨hvU, hvFV.2⟩
    exact ((deleteVertices_V Γ {v}).subset hvV).2 rfl
  have hnotall : ¬ Γ.V ⊆ D := by
    intro hsub
    apply hT.axiom3 hm
    exact inter_eq_left.mpr hsub
  obtain ⟨w, hwΓ, hwD⟩ := not_subset.mp hnotall
  have hwNew : w ∈ Γ'.V := by
    rw [deleteVertices_V]
    exact ⟨hwΓ, fun hwv => hwD (mem_singleton_iff.mp hwv ▸ hvD)⟩
  have hdis : Disjoint Γ'.U (discBd D) := by
    apply disjoint_left.mpr
    intro x hxNew hxBd
    have hxF : x ∈ F := hfront ▸ (IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ hxBd
    have hxV : x ∈ Γ.V := hn ⟨hxF, hΓ.U_subset hxNew⟩
    have hxv : x = v := hFV.subset ⟨hxF, hxV⟩
    exact hvnot (hxv ▸ hxNew)
  rcases hD.side (fun x => (hS.2.2 x).isManifoldPoint)
      (isPreconnected_U_of_isTwoCell hS htwo) hdis with hin | hout
  · exact (hwD ((discInt_subset D) (hin (Γ'.V_subset_U hwNew)))).elim
  · exact hout

/-- Closed-set restriction commutes with vertex deletion, including
all ends of the surviving edges. -/
theorem deleteVertices_interSet {Γ : Drawing S} {X Z : Set S} (hX : IsClosed X) :
    deleteVertices (Γ.interSet X) Z = (deleteVertices Γ Z).interSet X := by
  have hsub : (Γ.interSet X).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  apply Drawing.ext_of_V_E
  · ext x
    simp only [deleteVertices_V, mem_interSet_V_iff hX, mem_sdiff]
    tauto
  · ext e
    rw [deleteVertices_E, mem_interSet_E_iff, deleteVertices_E]
    simp only [mem_ofPred_eq, mem_interSet_E_iff]
    constructor
    · rintro ⟨⟨he, heX⟩, hd⟩
      have he' := mem_interSet_E_iff.mpr ⟨he, heX⟩
      rw [hsub.closure_inter_V he'] at hd
      exact ⟨⟨he, hd⟩, heX⟩
    · rintro ⟨⟨he, hd⟩, heX⟩
      have he' := mem_interSet_E_iff.mpr ⟨he, heX⟩
      rw [← hsub.closure_inter_V he'] at hd
      exact ⟨⟨he, heX⟩, hd⟩

/-- Removing the selected disc before deleting its boundary vertex
does not change the resulting two-cell drawing. This corrects the
loop issue in the radial contraction used in XII (7.3), page 261. -/
theorem selected_disc_restriction_delete_vertex_eq [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) {v : S}
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    {D F : Set S} (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    deleteVertices (Γ.interSet (closure (univ \ D))) {v} = deleteVertices Γ {v} := by
  rw [deleteVertices_interSet isClosed_closure]
  apply interSet_eq_self_of_U_subset isClosed_closure
  intro x hx
  exact subset_closure ⟨mem_univ _, disjoint_left.mp
    (deleted_drawing_disjoint_selected_vertex_disc hS hT htwo hD hbd hn hFV hm) hx⟩

/-- The only old vertex in a selected one-vertex disc is its boundary
vertex when deleting that vertex leaves a two-cell drawing. -/
theorem vertices_in_selected_vertex_disc [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) {v : S}
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    {D F : Set S} (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) : Γ.V ∩ D = {v} := by
  have hdis := deleted_drawing_disjoint_selected_vertex_disc hS hT htwo hD hbd hn hFV hm
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hvD : v ∈ D := hD.isClosed.closure_subset_iff.mpr subset_rfl
    (((subBd_eq_frontier D).symm.trans hbd).symm ▸ hvFV.1).1
  apply Subset.antisymm
  · rintro x ⟨hxΓ, hxD⟩
    by_contra hxv
    have hxNew : x ∈ (deleteVertices Γ {v}).V := (deleteVertices_V Γ {v}).symm ▸ ⟨hxΓ, hxv⟩
    exact disjoint_left.mp hdis ((deleteVertices Γ {v}).V_subset_U hxNew) hxD
  · rintro x hx
    have hxv := mem_singleton_iff.mp hx
    subst x
    exact ⟨hvFV.2, hvD⟩

/-- Removing a selected inside containing an old edge strictly
reduces the number of edges. This supplies the finite induction
measure for preprocessing in XII (7.3). -/
theorem ncard_edges_outside_lt_of_edge_inside {Γ : Drawing S} {D : Set S}
    (hn : frontier D ∩ Γ.U ⊆ Γ.V) {e : Set S} (he : e ∈ Γ.E) (heD : e ⊆ D) :
    (Γ.interSet (closure (univ \ D))).E.ncard < Γ.E.ncard := by
  have hsub : (Γ.interSet (closure (univ \ D))).E ⊆ Γ.E := (Drawing.span_isSubdrawing Γ _ _).2
  have hen : e ∉ (Γ.interSet (closure (univ \ D))).E := by
    intro heNew
    have heOut := (mem_interSet_E_iff.mp heNew).2
    obtain ⟨x, hxe⟩ := he.1
    have hxFront : x ∈ frontier D := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure (heD hxe), by simpa only [compl_eq_univ_sdiff] using heOut hxe⟩
    exact (he.2.1 hxe).2 (hn ⟨hxFront, (he.2.1 hxe).1⟩)
  exact ncard_lt_ncard ⟨hsub, fun hback => hen (hback he)⟩ Γ.finite_edges

end GraphMinor.GM12
