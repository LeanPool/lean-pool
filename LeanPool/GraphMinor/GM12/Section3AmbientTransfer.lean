/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section3AmbientDrawing
public import LeanPool.GraphMinor.GM12.Section3SubspaceDrawing
import LeanPool.GraphMinor.GM11.Walks

/-!
# Returning connected subdrawings from the punctured surface

XII (3.1), page 245, applies VII in Sigma-star and needs connected
subdrawings of the original drawing in Sigma. Inclusion of the closed
subspace maps edges and graph walks, preserves connectedness and vertex
disjointness, and preserves the prescribed intersections with the
boundary vertex set. This file proves that final ambient transfer.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A subdrawing of the restricted drawing becomes a subdrawing of
the original drawing when returned to the ambient space. -/
theorem drawingFromClosedSubspace_isSubdrawing {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (C : Set S) (hC : IsClosed C) (hUC : Γ.U ⊆ C)
    {H : Drawing C} (hH : H.IsSubdrawing (drawingInSubspace Γ C hUC)) :
    (drawingFromClosedSubspace C hC H).IsSubdrawing Γ := by
  constructor
  · rw [drawingFromClosedSubspace_V]
    rintro x ⟨y, hy, rfl⟩
    have hm := hH.1 hy
    rw [drawingInSubspace_V] at hm
    exact hm
  · rw [drawingFromClosedSubspace_E]
    rintro e ⟨e', he', rfl⟩
    have hm := hH.2 he'
    rw [drawingInSubspace_E] at hm
    obtain ⟨E, hE, hpreE⟩ := hm
    have hEC : E ⊆ C := fun x hx => hUC (hE.2.1 hx).1
    have himage : (Subtype.val : C → S) '' e' = E := by
      rw [← hpreE, Subtype.image_preimage_coe, inter_eq_right.mpr hEC]
    exact himage.symm ▸ hE

/-- A link maps through inclusion of the closed ambient subspace. -/
theorem isLink_drawingFromClosedSubspace {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsClosed C) (H : Drawing C)
    {e : Set C} {x y : C} (hl : H.toGraph.IsLink e x y) :
    (drawingFromClosedSubspace C hC H).toGraph.IsLink
      ((Subtype.val : C → S) '' e) x.val y.val := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [drawingFromClosedSubspace_E]
    exact ⟨e, hl.1, rfl⟩
  · rw [drawingFromClosedSubspace_V]
    exact ⟨x, hl.2.1, rfl⟩
  · rw [drawingFromClosedSubspace_V]
    exact ⟨y, hl.2.2.1, rfl⟩
  · rw [drawingFromClosedSubspace_V, hC.isClosedEmbedding_subtypeVal.closure_image_eq,
      ← image_inter Subtype.val_injective, hl.2.2.2, image_pair]

/-- A graph walk in the closed subspace gives an ambient graph walk
between the same points. -/
theorem exists_walk_drawingFromClosedSubspace {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsClosed C) (H : Drawing C) {x y : C} (W : GraphWalk H.toGraph x y) :
    Nonempty (GraphWalk (drawingFromClosedSubspace C hC H).toGraph x.val y.val) := by
  induction W with
  | nil hx =>
    refine ⟨.nil ?_⟩
    change _ ∈ (drawingFromClosedSubspace C hC H).V
    rw [drawingFromClosedSubspace_V]
    exact ⟨_, hx, rfl⟩
  | cons hl rest ih =>
    obtain ⟨R⟩ := ih
    exact ⟨.cons (isLink_drawingFromClosedSubspace C hC H hl) R⟩

/-- Connectedness is preserved when a drawing in a closed subspace
is read in the ambient space. -/
theorem isConnectedDrawing_drawingFromClosedSubspace {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsClosed C) {H : Drawing C} (hH : IsConnectedDrawing H) :
    IsConnectedDrawing (drawingFromClosedSubspace C hC H) := by
  intro x hx y hy
  rw [drawingFromClosedSubspace_V] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨W⟩ := hH x' hx' y' hy'
  exact exists_walk_drawingFromClosedSubspace C hC H W

/-- The connected subdrawings obtained in Sigma-star give the exact
connected-subdrawing conclusion in Sigma of XII (3.1), page 245. -/
theorem hasConnectingSubdrawings_from_closed_subspace {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (C : Set S) (hC : IsClosed C) (hUC : Γ.U ⊆ C)
    {p : ℕ} {Z : Set S} {Zs : Fin p → Set S} (hZs : ∀ j, Zs j ⊆ C)
    (hconnect : HasConnectingSubdrawings (drawingInSubspace Γ C hUC)
      ((Subtype.val : C → S) ⁻¹' Z) (fun j => (Subtype.val : C → S) ⁻¹' Zs j)) :
    HasConnectingSubdrawings Γ Z Zs := by
  obtain ⟨H, hsub, hconn, hdisj, hboundary⟩ := hconnect
  let K : Fin p → Drawing S := fun j => drawingFromClosedSubspace C hC (H j)
  refine ⟨K, fun j => drawingFromClosedSubspace_isSubdrawing Γ C hC hUC (hsub j),
    fun j => isConnectedDrawing_drawingFromClosedSubspace C hC (hconn j), ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rw [drawingFromClosedSubspace_V] at hxi hxj
    obtain ⟨y, hy, hyx⟩ := hxi
    obtain ⟨z, hz, hzx⟩ := hxj
    have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
    exact Set.disjoint_left.mp (hdisj i j hij) hy (hyz.symm ▸ hz)
  · intro j
    ext x
    constructor
    · rintro ⟨hxK, hxZ⟩
      rw [drawingFromClosedSubspace_V] at hxK
      obtain ⟨y, hy, rfl⟩ := hxK
      have hm : y ∈ (H j).V ∩ (Subtype.val : C → S) ⁻¹' Z := ⟨hy, hxZ⟩
      rw [hboundary j] at hm
      exact hm
    · intro hx
      let y : C := ⟨x, hZs j hx⟩
      have hm : y ∈ (H j).V ∩ (Subtype.val : C → S) ⁻¹' Z := by
        rw [hboundary j]
        exact hx
      refine ⟨?_, hm.2⟩
      rw [drawingFromClosedSubspace_V]
      exact ⟨y, hm.1, rfl⟩

end GraphMinor.GM12
