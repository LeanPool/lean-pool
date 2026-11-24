/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section3SubtypeComponents

/-!
# Returning a drawing from a closed subspace to the surface

After VII is applied in the punctured surface of XII (3.1), page 245,
its subdrawings must be read in the original surface. The punctured
surface is closed, so inclusion preserves closed supports and edge
closures. Arc-components and their line or circle parametrizations
then give the ambient drawing with the same vertices and edges.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Read a drawing of a closed subspace in the ambient space. This is
the return from Sigma-star to Sigma in XII (3.1), page 245. -/
def drawingFromClosedSubspace {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsClosed C) (H : Drawing C) : Drawing S where
  U := (Subtype.val : C → S) '' H.U
  V := (Subtype.val : C → S) '' H.V
  V_subset_U := image_mono H.V_subset_U
  isClosed_U := hC.isClosedEmbedding_subtypeVal.isClosedMap _ H.isClosed_U
  finite_V := H.finite_V.image Subtype.val
  finite_edges := by
    rw [← image_sdiff Subtype.val_injective, arcComponentsIn_subtype_image]
    exact H.finite_edges.image _
  edge_cond := by
    intro e' he'
    rw [← image_sdiff Subtype.val_injective, arcComponentsIn_subtype_image] at he'
    obtain ⟨e, he, rfl⟩ := he'
    have hcl := hC.isClosedEmbedding_subtypeVal.closure_image_eq e
    have hcap : closure ((Subtype.val : C → S) '' e) ∩ (Subtype.val : C → S) '' H.V =
        (Subtype.val : C → S) '' (closure e ∩ H.V) := by
      rw [hcl, ← image_inter Subtype.val_injective]
    rcases H.edge_cond e he with ⟨v, w, hvw, hends, hL⟩ | ⟨v, hends, hO⟩
    · left
      refine ⟨v.val, w.val, fun h => hvw (Subtype.ext h), ?_, ?_⟩
      · rw [hcap, hends, image_pair]
      · rw [hcl]
        obtain ⟨f, hf0, hf1⟩ := hL
        refine ⟨f.trans (IsEmbedding.subtypeVal.homeomorphImage (closure e)), ?_, ?_⟩
        · exact congrArg Subtype.val hf0
        · exact congrArg Subtype.val hf1
    · right
      refine ⟨v.val, ?_, ?_⟩
      · rw [hcap, hends, image_singleton]
      · rw [hcl]
        obtain ⟨f⟩ := hO
        exact ⟨f.trans (IsEmbedding.subtypeVal.homeomorphImage (closure e))⟩

/-- Support of a drawing returned from a closed subspace. -/
theorem drawingFromClosedSubspace_U {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsClosed C) (H : Drawing C) :
    (drawingFromClosedSubspace C hC H).U = (Subtype.val : C → S) '' H.U := by rfl

/-- Vertices of a drawing returned from a closed subspace. -/
theorem drawingFromClosedSubspace_V {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsClosed C) (H : Drawing C) :
    (drawingFromClosedSubspace C hC H).V = (Subtype.val : C → S) '' H.V := by rfl

/-- Edges of a drawing returned from a closed subspace. -/
theorem drawingFromClosedSubspace_E {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsClosed C) (H : Drawing C) :
    (drawingFromClosedSubspace C hC H).E =
      (image (Subtype.val : C → S)) '' H.E := by
  change arcComponentsIn ((Subtype.val : C → S) '' H.U \ (Subtype.val : C → S) '' H.V) = _
  rw [← image_sdiff Subtype.val_injective, arcComponentsIn_subtype_image]
  rfl

end GraphMinor.GM12
