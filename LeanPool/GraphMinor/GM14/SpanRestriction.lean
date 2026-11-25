/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs

/-!
# Restricting a span embedding

A span embedding restricts to a spanned subdrawing with the same vertex and edge maps.
The image of a cleared subdrawing lies in the original image.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Graph Surface GM11

universe u v w

variable {S : Type w} [TopologicalSpace S] [T1Space S]

/-- Restriction of a `SpanEmbedding H G` to a spanned subdrawing `H.span V' E'`. -/
def restrictSpan {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (V' : Set S) (E' : Set (Set S)) :
    SpanEmbedding (H.span V' E') G where
  imageGraph :=
    (η.imageGraph.induce (η.vMap '' (H.span V' E').V)).restrict (η.eMap '' (H.span V' E').E)
  vMap := η.vMap
  eMap := η.eMap
  imageGraph_le := by
    have hV_sub : η.vMap '' (H.span V' E').V ⊆ V(η.imageGraph) := by
      rw [← η.bijOn_v.image_eq]
      exact image_mono (H.spanV_subset V' E')
    exact (Graph.restrict_le.trans (Graph.induce_le hV_sub)).trans η.imageGraph_le
  bijOn_v := by
    have hV_eq :
        V((η.imageGraph.induce (η.vMap '' (H.span V' E').V)).restrict
          (η.eMap '' (H.span V' E').E)) = η.vMap '' (H.span V' E').V := by
      simp
    rw [hV_eq]
    exact (η.bijOn_v.injOn.mono (H.spanV_subset V' E')).bijOn_image
  bijOn_e := by
    have hE_eq :
        E((η.imageGraph.induce (η.vMap '' (H.span V' E').V)).restrict
          (η.eMap '' (H.span V' E').E)) = η.eMap '' (H.span V' E').E := by
      apply Subset.antisymm
      · intro b hb
        rw [edge_mem_iff_exists_isLink] at hb
        obtain ⟨x, y, hb, _⟩ := hb
        exact hb
      · rintro b ⟨e, he, rfl⟩
        have he_span : e ∈ E' ∩ H.E := by rwa [← H.span_E V' E']
        have he_img : η.eMap e ∈ E(η.imageGraph) := η.bijOn_e.mapsTo he_span.2
        rw [edge_mem_iff_exists_isLink] at he_img ⊢
        obtain ⟨x, y, hlink⟩ := he_img
        have hx_V : x ∈ V(η.imageGraph) := η.imageGraph.left_mem_of_isLink hlink
        have hy_V : y ∈ V(η.imageGraph) := η.imageGraph.left_mem_of_isLink hlink.symm
        rw [← η.bijOn_v.image_eq] at hx_V hy_V
        obtain ⟨u, huH, rfl⟩ := hx_V
        obtain ⟨v, hvH, rfl⟩ := hy_V
        have hu_cl : u ∈ closure e := (η.inc_iff e he_span.2 u huH).mp ⟨η.vMap v, hlink⟩
        have hv_cl : v ∈ closure e := (η.inc_iff e he_span.2 v hvH).mp ⟨η.vMap u, hlink.symm⟩
        have hu_span : u ∈ (H.span V' E').V :=
          Or.inr (mem_iUnion₂.mpr ⟨e, he_span, hu_cl, huH⟩)
        have hv_span : v ∈ (H.span V' E').V :=
          Or.inr (mem_iUnion₂.mpr ⟨e, he_span, hv_cl, hvH⟩)
        exact ⟨η.vMap u, η.vMap v, ⟨e, he, rfl⟩, hlink,
          ⟨u, hu_span, rfl⟩, ⟨v, hv_span, rfl⟩⟩
    rw [hE_eq]
    have hE_sub : (H.span V' E').E ⊆ H.E := by
      rw [H.span_E V' E']
      exact inter_subset_right
    exact (η.bijOn_e.injOn.mono hE_sub).bijOn_image
  inc_iff e he v hv := by
    have he_span : e ∈ E' ∩ H.E := by rwa [← H.span_E V' E']
    have hv_H : v ∈ H.V := H.spanV_subset V' E' hv
    rw [← η.inc_iff e he_span.2 v hv_H]
    constructor
    · rintro ⟨w, _, hlink, _, _⟩
      exact ⟨w, hlink⟩
    · rintro ⟨w, hlink⟩
      have hw_V : w ∈ V(η.imageGraph) := η.imageGraph.left_mem_of_isLink hlink.symm
      rw [← η.bijOn_v.image_eq] at hw_V
      obtain ⟨u, huH, rfl⟩ := hw_V
      have hu_cl : u ∈ closure e := (η.inc_iff e he_span.2 u huH).mp ⟨η.vMap v, hlink.symm⟩
      have hu_span : u ∈ (H.span V' E').V :=
        Or.inr (mem_iUnion₂.mpr ⟨e, he_span, hu_cl, huH⟩)
      exact ⟨η.vMap u, ⟨e, he, rfl⟩, hlink, ⟨v, hv, rfl⟩, ⟨u, hu_span, rfl⟩⟩

/-- Restriction of a `SpanEmbedding H G` to `clearedSubdrawing H Λ = H.interSet (univ \ Λ)`. -/
def restrictCleared {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    SpanEmbedding (clearedSubdrawing H Λ) G :=
  restrictSpan η (H.V ∩ (univ \ Λ)) {e | e ∈ H.E ∧ e ⊆ univ \ Λ}

@[simp]
theorem restrictCleared_vMap {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).vMap = η.vMap := rfl

@[simp]
theorem restrictCleared_eMap {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).eMap = η.eMap := rfl

theorem restrictCleared_imageGraph_le {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).imageGraph ≤ η.imageGraph := by
  have hV_sub : η.vMap '' (clearedSubdrawing H Λ).V ⊆ V(η.imageGraph) := by
    rw [← η.bijOn_v.image_eq]
    exact image_mono (H.spanV_subset _ _)
  exact Graph.restrict_le.trans (Graph.induce_le hV_sub)

end GraphMinor.GM14
