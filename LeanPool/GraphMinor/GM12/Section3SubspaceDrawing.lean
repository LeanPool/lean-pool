/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section3SubtypeComponents
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM11.Defs

/-!
# Reading a drawing in a subspace containing its support

For XII (3.1), page 245, the original drawing is also a graph in the
punctured surface. Pull its support and vertex set back along inclusion.
Its edges are the same arc-components, and their closures remain lines
or circles with the same endpoints. This constructs that drawing without
adding any geometric assumption beyond containment of its support.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

private theorem subtype_preimage_pair {S : Type*} {C : Set S} (v w : C) :
    (Subtype.val : C → S) ⁻¹' {v.val, w.val} = {v, w} := by
  ext x
  simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, Subtype.ext_iff]

private theorem subtype_preimage_singleton {S : Type*} {C : Set S} (v : C) :
    (Subtype.val : C → S) ⁻¹' {v.val} = {v} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]

/-- A drawing whose support is in a subspace can be read as a drawing
of that subspace. XII (3.1), page 245, uses this for Sigma-star. -/
def drawingInSubspace {S : Type*} [TopologicalSpace S] (Γ : Drawing S)
    (C : Set S) (hUC : Γ.U ⊆ C) : Drawing C where
  U := (Subtype.val : C → S) ⁻¹' Γ.U
  V := (Subtype.val : C → S) ⁻¹' Γ.V
  V_subset_U := preimage_mono Γ.V_subset_U
  isClosed_U := Γ.isClosed_U.preimage continuous_subtype_val
  finite_V := Set.Finite.preimage Subtype.val_injective.injOn Γ.finite_V
  finite_edges := by
    rw [← preimage_sdiff, arcComponentsIn_subtype_preimage (sdiff_subset.trans hUC)]
    exact Γ.finite_edges.image _
  edge_cond := by
    intro e' he'
    rw [← preimage_sdiff, arcComponentsIn_subtype_preimage (sdiff_subset.trans hUC)] at he'
    obtain ⟨e, he, rfl⟩ := he'
    have heC : e ⊆ C := fun x hx => hUC (he.2.1 hx).1
    have hclC : closure e ⊆ C := (Γ.closure_subset_U he).trans hUC
    have hcl := closure_subtype_preimage heC
    rcases Γ.edge_cond e he with ⟨v, w, hvw, hcap, hL⟩ | ⟨v, hcap, hO⟩
    · have hv : v ∈ Γ.V := by
        have hm : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inl rfl)
        exact hm.2
      have hw : w ∈ Γ.V := by
        have hm : w ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl)
        exact hm.2
      let v' : C := ⟨v, hUC (Γ.V_subset_U hv)⟩
      let w' : C := ⟨w, hUC (Γ.V_subset_U hw)⟩
      left
      refine ⟨v', w', fun h => hvw (congrArg Subtype.val h), ?_, ?_⟩
      · rw [hcl, ← preimage_inter, hcap]
        exact subtype_preimage_pair v' w'
      · rw [hcl]
        exact isLineWithEnds_subtype_preimage hclC hL
    · have hv : v ∈ Γ.V := by
        have hm : v ∈ closure e ∩ Γ.V := hcap.symm ▸ mem_singleton v
        exact hm.2
      let v' : C := ⟨v, hUC (Γ.V_subset_U hv)⟩
      right
      refine ⟨v', ?_, ?_⟩
      · rw [hcl, ← preimage_inter, hcap]
        exact subtype_preimage_singleton v'
      · rw [hcl]
        exact isOArc_subtype_preimage hclC hO

/-- Support of the drawing read in the smaller ambient space. -/
theorem drawingInSubspace_U {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (C : Set S) (hUC : Γ.U ⊆ C) :
    (drawingInSubspace Γ C hUC).U = (Subtype.val : C → S) ⁻¹' Γ.U := by rfl

/-- Vertex set of the drawing read in the smaller ambient space. -/
theorem drawingInSubspace_V {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (C : Set S) (hUC : Γ.U ⊆ C) :
    (drawingInSubspace Γ C hUC).V = (Subtype.val : C → S) ⁻¹' Γ.V := by rfl

/-- Edges of the drawing read in the smaller ambient space. -/
theorem drawingInSubspace_E {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (C : Set S) (hUC : Γ.U ⊆ C) :
    (drawingInSubspace Γ C hUC).E =
      (fun E : Set S => (Subtype.val : C → S) ⁻¹' E) '' Γ.E := by
  change arcComponentsIn ((Subtype.val : C → S) ⁻¹' Γ.U \ (Subtype.val : C → S) ⁻¹' Γ.V) = _
  rw [← preimage_sdiff, arcComponentsIn_subtype_preimage (sdiff_subset.trans hUC)]
  rfl

/-- Vertex intersections are unchanged on inclusion into the original
surface. This also identifies their finite cardinalities. -/
theorem drawingInSubspace_image_vertices_inter
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S)
    (C : Set S) (hUC : Γ.U ⊆ C) (F : Set C) :
    (Subtype.val : C → S) '' ((drawingInSubspace Γ C hUC).V ∩ F) =
      Γ.V ∩ (Subtype.val : C → S) '' F := by
  rw [drawingInSubspace_V]
  ext x
  constructor
  · rintro ⟨y, ⟨hyV, hyF⟩, rfl⟩
    exact ⟨hyV, y, hyF, rfl⟩
  · rintro ⟨hxV, y, hyF, rfl⟩
    exact ⟨y, ⟨hxV, hyF⟩, rfl⟩

/-- A normal set in the smaller ambient space remains normal after
inclusion in the original drawing. -/
theorem drawingInSubspace_isNormal_image
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S)
    (C : Set S) (hUC : Γ.U ⊆ C) {F : Set C}
    (hn : (drawingInSubspace Γ C hUC).IsNormal F) :
    Γ.IsNormal ((Subtype.val : C → S) '' F) := by
  rintro x ⟨⟨y, hy, rfl⟩, hyU⟩
  have hyG : y ∈ (drawingInSubspace Γ C hUC).U := by
    rw [drawingInSubspace_U]
    exact hyU
  have hyV := hn ⟨hy, hyG⟩
  rw [drawingInSubspace_V] at hyV
  exact hyV

end GraphMinor.GM12
