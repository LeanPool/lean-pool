/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72Circuit
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM11.Forest
import LeanPool.GraphMinor.GM11.Section810

/-!
# Deleting the radial pieces inside the boundary circuit

XII (7.2), page 260, deletes the radial vertices and edges strictly
inside the two-spoke circuit and then deletes one boundary spoke.
Restriction to the closed outside performs the first deletion. Since
the boundary is a subdrawing, it cuts no edge. The lemmas here record
the exact vertices, edges, and point set of this construction.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- An edge meeting a subdrawing belongs to that subdrawing. Its
interior point cannot be a vertex, so it belongs to an edge of each
drawing, and distinct edges have disjoint interiors. -/
theorem edge_mem_of_meets_subdrawing {K C : Drawing S} (hC : C.IsSubdrawing K)
    {e : Set S} (he : e ∈ K.E) (hm : (e ∩ C.U).Nonempty) : e ∈ C.E := by
  obtain ⟨x, hxe, hxC⟩ := hm
  have hxV : x ∉ C.V := fun hv => (he.2.1 hxe).2 (hC.1 hv)
  obtain ⟨f, hf, hxf⟩ := C.exists_edge_of_mem hxC hxV
  have hef : e = f := K.edge_eq_of_mem he (hC.2 hf) hxe hxf
  exact hef.symm ▸ hf

/-- Restriction to the closed outside of a subdrawing boundary cuts
no edge. This justifies the first deletion in XII (7.2), page 260. -/
theorem interSet_outside_U_of_subdrawing_boundary {K C : Drawing S}
    (hC : C.IsSubdrawing K) {D : Set S} (hb : frontier D = C.U) :
    (K.interSet (closure (univ \ D))).U = K.U ∩ closure (univ \ D) := by
  let X := closure (univ \ D)
  have hfront : frontier X ⊆ frontier D := by
    dsimp [X]
    rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
    exact frontier_interior_subset
  have hbX : frontier D ⊆ X := by
    rw [frontier_eq_closure_inter_closure]
    simpa only [X, compl_eq_univ_sdiff] using
      (inter_subset_right : closure D ∩ closure Dᶜ ⊆ closure Dᶜ)
  apply Subset.antisymm
  · exact subset_inter (Drawing.span_isSubdrawing K _ _).U_subset
      (interSet_U_subset isClosed_closure)
  · rintro x ⟨hxK, hxX⟩
    by_cases hxV : x ∈ K.V
    · exact (K.interSet X).V_subset_U (mem_interSet_V hxV hxX)
    · obtain ⟨e, he, hxe⟩ := K.exists_edge_of_mem hxK hxV
      have heX : e ⊆ X := by
        by_cases hm : (e ∩ C.U).Nonempty
        · have heC := edge_mem_of_meets_subdrawing hC he hm
          exact fun y hy => hbX (hb.symm ▸ (heC.2.1 hy).1)
        · have hdis : Disjoint e (frontier X) := by
            apply disjoint_left.mpr
            intro y hy hyf
            exact hm ⟨y, hy, hb ▸ hfront hyf⟩
          exact subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected
            isClosed_closure hdis hxe hxX
      exact ((mem_interSet_E_iff.mpr ⟨he, heX⟩).2.1 hxe).1

/-- The radial deletion in XII (7.2), page 260: retain the closed
outside of the selected disc and remove the boundary spoke `f`. -/
def radialDiscDeletion (K : Drawing S) (D f : Set S) : Drawing S :=
  (K.interSet (closure (univ \ D))).deleteEdge f

/-- Every retained radial vertex and edge is an old one. -/
theorem radialDiscDeletion_isSubdrawing (K : Drawing S) (D f : Set S) :
    (radialDiscDeletion K D f).IsSubdrawing K :=
  (deleteEdge_isSubdrawing _ _).trans (Drawing.span_isSubdrawing K _ _)

/-- Exactly the vertices outside the open selected disc remain. -/
theorem radialDiscDeletion_V (K : Drawing S) (D f : Set S) :
    (radialDiscDeletion K D f).V = K.V ∩ closure (univ \ D) := by
  unfold radialDiscDeletion
  rw [deleteEdge_V]
  ext x
  exact mem_interSet_V_iff isClosed_closure

/-- Exactly the edges in the closed outside, apart from `f`, remain. -/
theorem radialDiscDeletion_E (K : Drawing S) (D f : Set S) :
    (radialDiscDeletion K D f).E =
      {e | e ∈ K.E ∧ e ⊆ closure (univ \ D) ∧ e ≠ f} := by
  unfold radialDiscDeletion
  rw [deleteEdge_E]
  ext e
  simp only [mem_sdiff, mem_singleton_iff, mem_ofPred_eq, mem_interSet_E_iff]
  tauto

/-- The point set of the deletion is the old closed outside with
only the interior of the chosen boundary spoke removed. -/
theorem radialDiscDeletion_U {K C : Drawing S} (hC : C.IsSubdrawing K)
    {D f : Set S} (hb : frontier D = C.U) (hf : f ∈ C.E) :
    (radialDiscDeletion K D f).U = (K.U ∩ closure (univ \ D)) \ f := by
  have hfX : f ⊆ closure (univ \ D) := by
    intro x hx
    have hxf : x ∈ frontier D := hb.symm ▸ (hf.2.1 hx).1
    rw [frontier_eq_closure_inter_closure] at hxf
    simpa only [compl_eq_univ_sdiff] using hxf.2
  have hf' : f ∈ (K.interSet (closure (univ \ D))).E :=
    mem_interSet_E_iff.mpr ⟨hC.2 hf, hfX⟩
  unfold radialDiscDeletion
  rw [deleteEdge_U _ hf', interSet_outside_U_of_subdrawing_boundary hC hb]

/-- Every retained old vertex is retained by the radial deletion. -/
theorem radialDiscDeletion_vertex_subset {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) (D f : Set S) :
    (Γ.interSet (closure (univ \ D))).V ⊆ (radialDiscDeletion K D f).V := by
  intro x hx
  rw [radialDiscDeletion_V]
  obtain ⟨hxΓ, hxD⟩ := (mem_interSet_V_iff isClosed_closure).mp hx
  exact ⟨hK.2.1 hxΓ, hxD⟩

/-- The first radial condition survives the deletion: the two retained
drawings meet precisely at the retained old vertices. -/
theorem radialDiscDeletion_inter {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) (D f : Set S) :
    (Γ.interSet (closure (univ \ D))).U ∩ (radialDiscDeletion K D f).U =
      (Γ.interSet (closure (univ \ D))).V := by
  let Γ' := Γ.interSet (closure (univ \ D))
  have hΓ : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hdel := radialDiscDeletion_isSubdrawing K D f
  apply Subset.antisymm
  · rintro x ⟨hxΓ, hxK⟩
    have hxV : x ∈ Γ.V := hK.1.subset ⟨hΓ.U_subset hxΓ, hdel.U_subset hxK⟩
    exact (isSubdrawing_U_inter_V hΓ).subset ⟨hxΓ, hxV⟩
  · intro x hx
    exact ⟨Γ'.V_subset_U hx,
      (radialDiscDeletion K D f).V_subset_U (radialDiscDeletion_vertex_subset hK D f hx)⟩

/-- Every retained radial vertex that is not an old vertex lies in
a region of the reduced drawing, as required in XII (7.2). -/
theorem radialDiscDeletion_vertex_region {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) (D f : Set S) :
    ∀ w ∈ (radialDiscDeletion K D f).V \ (Γ.interSet (closure (univ \ D))).V,
      ∃ r ∈ (Γ.interSet (closure (univ \ D))).R, w ∈ r := by
  intro w hw
  have hnot : w ∉ (Γ.interSet (closure (univ \ D))).U := by
    intro hwΓ
    have hwV := (radialDiscDeletion_inter hK D f).subset
      ⟨hwΓ, (radialDiscDeletion K D f).V_subset_U hw.1⟩
    exact hw.2 hwV
  exact exists_region_of_notMem hnot

/-- Each retained spoke still joins a retained old vertex to a
retained region vertex. Its ends are unchanged by the deletion in
XII (7.2), page 260. -/
theorem radialDiscDeletion_edge_ends {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) (D f : Set S) :
    ∀ e ∈ (radialDiscDeletion K D f).E,
      ∃ v ∈ (Γ.interSet (closure (univ \ D))).V,
        ∃ w ∈ (radialDiscDeletion K D f).V \ (Γ.interSet (closure (univ \ D))).V,
          closure e ∩ (radialDiscDeletion K D f).V = {v, w} := by
  intro e he
  have hedata := (radialDiscDeletion_E K D f).subset he
  obtain ⟨v, hv, w, hw, hcap⟩ := hK.2.2.2.2.1 e hedata.1
  have hcl : closure e ⊆ closure (univ \ D) := closure_minimal hedata.2.1 isClosed_closure
  have hvcl : v ∈ closure e := by
    have hv' : v ∈ closure e ∩ K.V := hcap.superset (Or.inl rfl)
    exact hv'.1
  have hvNew : v ∈ (Γ.interSet (closure (univ \ D))).V :=
    (mem_interSet_V_iff isClosed_closure).mpr ⟨hv, hcl hvcl⟩
  have hcapNew : closure e ∩ (radialDiscDeletion K D f).V = {v, w} :=
    ((radialDiscDeletion_isSubdrawing K D f).closure_inter_V he).trans hcap
  have hwNew : w ∈ (radialDiscDeletion K D f).V :=
    (hcapNew.superset (Or.inr rfl)).2
  have hwn : w ∉ (Γ.interSet (closure (univ \ D))).V := fun hwΓ =>
    hw.2 ((Drawing.span_isSubdrawing Γ _ _).1 hwΓ)
  exact ⟨v, hvNew, w, ⟨hwNew, hwn⟩, hcapNew⟩

end GraphMinor.GM12
