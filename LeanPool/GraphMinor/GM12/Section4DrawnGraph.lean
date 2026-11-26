/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM09.DiscDrawing

/-!
# Turning a drawing by edge curves into a graph drawing

The target of XII (4.3), page 249, is an abstract graph that
can be drawn in the surface. Convert its vertex points and edge
curves into a drawing with a graph isomorphism. Start with the
vertex points and add the edges one at a time, using a line for
a nonloop edge and an `O`-arc for a loop. The given intersection
conditions ensure that gluing preserves exactly the original graph.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph GM09

/-- A finite graph drawn by vertex points and disjoint edge curves
has a geometric drawing isomorphic to it, as used at the start
of XII (4.3), page 249. -/
theorem exists_graphDrawing_of_edge_curves
    {α β S : Type*} [TopologicalSpace S] [T2Space S]
    (G : Graph α β) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (ν : α → S) (edgeOf : β → Set S) (hν : InjOn ν G.vertexSet)
    (hline : ∀ e ∈ G.edgeSet, ∀ u v, G.IsLink e u v → u ≠ v →
      IsLineWithEnds (edgeOf e) (ν u) (ν v))
    (hloop : ∀ e ∈ G.edgeSet, ∀ v, G.IsLoopAt e v → IsOArc (edgeOf e) ∧ ν v ∈ edgeOf e)
    (hmeet : ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f →
      edgeOf e ∩ edgeOf f ⊆ ν '' G.vertexSet)
    (hon : ∀ e ∈ G.edgeSet, ∀ v ∈ G.vertexSet, ν v ∈ edgeOf e → G.Inc e v) :
    ∃ D : GraphDrawing G S, D.drawing.U = ν '' G.vertexSet ∪ ⋃ e ∈ G.edgeSet, edgeOf e ∧
      ∀ v : G.vertexSet, (D.iso.vertexEquiv v).val = ν v.val := by
  classical
  have hconstruct : ∀ (F : Set β), F.Finite → F ⊆ G.edgeSet →
      ∃ D : GraphDrawing (G.restrict F) S,
        D.drawing.U = ν '' G.vertexSet ∪ ⋃ e ∈ F, edgeOf e ∧
        ∀ v : (G.restrict F).vertexSet, (D.iso.vertexEquiv v).val = ν v.val := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty =>
      intro _
      obtain ⟨D, hDU, hmap⟩ := GraphDrawing.of_edgeless (G := G.restrict ∅) hV
        (show (G.restrict ∅).edgeSet = ∅ by simp) hν
      refine ⟨D, ?_, hmap⟩
      simpa only [vertexSet_restrict, biUnion_empty, union_empty] using hDU
    | @insert e F he hF ih =>
      intro hFG
      have heG : e ∈ G.edgeSet := hFG (Or.inl rfl)
      have hFsub : F ⊆ G.edgeSet := fun f hf => hFG (Or.inr hf)
      obtain ⟨D₁, hD₁U, hmap₁⟩ := ih hFsub
      obtain ⟨u, v, hlink⟩ := G.exists_isLink_of_mem_edgeSet heG
      let K : Graph α β := (G.induce {u, v}).restrict {e}
      have hKV : K.vertexSet = {u, v} := rfl
      have hKE : K.edgeSet = {e} := by
        ext f
        simp only [K, edgeSet_restrict, mem_inter_iff, mem_singleton_iff, edgeSet_induce,
          mem_ofPred_eq]
        constructor
        · exact fun h => h.2
        · intro hfe
          subst f
          exact ⟨⟨u, v, hlink, Or.inl rfl, Or.inr rfl⟩, rfl⟩
      have hlinkK : K.IsLink e u v := ⟨rfl, hlink, Or.inl rfl, Or.inr rfl⟩
      have hKL : K ≤ G.restrict (insert e F) :=
        ⟨by
          rw [hKV, vertexSet_restrict]
          exact pair_subset hlink.left_mem hlink.right_mem,
          fun {_ _ _} hl => ⟨hl.1 ▸ (Or.inl rfl), hl.2.1⟩⟩
      have hsingle : ∃ D₂ : GraphDrawing K S, D₂.drawing.U = edgeOf e ∧
          ∀ z : K.vertexSet, (D₂.iso.vertexEquiv z).val = ν z.val := by
        by_cases huv : u = v
        · subst v
          have hKV' : K.vertexSet = {u} := by simp [hKV]
          have hshape := hloop e heG u hlink
          exact GraphDrawing.of_single_loop hKV' hKE hlinkK hshape.1 hshape.2
        · exact GraphDrawing.of_single_edge hKV hKE hlinkK
            (fun h => huv (hν hlink.left_mem hlink.right_mem h)) (hline e heG u v hlink huv)
      obtain ⟨D₂, hD₂U, hmap₂⟩ := hsingle
      have hG₁ : G.restrict F ≤ G.restrict (insert e F) :=
        ⟨subset_rfl, fun {_ _ _} hl => ⟨Or.inr hl.1, hl.2⟩⟩
      have hVunion : (G.restrict F).vertexSet ∪ K.vertexSet = (G.restrict (insert e F)).vertexSet
        := by
        rw [hKV, vertexSet_restrict, vertexSet_restrict]
        exact union_eq_left.mpr (pair_subset hlink.left_mem hlink.right_mem)
      have hEunion : (G.restrict F).edgeSet ∪ K.edgeSet = (G.restrict (insert e F)).edgeSet := by
        rw [hKE, edgeSet_restrict, edgeSet_restrict]
        ext f
        simp only [mem_union, mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro (⟨hfG, hfF⟩ | hfe)
          · exact ⟨hfG, Or.inr hfF⟩
          · subst f
            exact ⟨heG, Or.inl rfl⟩
        · rintro ⟨hfG, hfe | hfF⟩
          · exact Or.inr hfe
          · exact Or.inl ⟨hfG, hfF⟩
      have hEdisj : Disjoint (G.restrict F).edgeSet K.edgeSet := by
        rw [hKE, disjoint_singleton_right, edgeSet_restrict]
        exact fun h => he h.2
      have hcontact : D₁.drawing.U ∩ D₂.drawing.U ⊆ ν '' ((G.restrict F).vertexSet ∩ K.vertexSet)
        := by
        rw [hD₁U, hD₂U, vertexSet_restrict, hKV]
        rintro z ⟨hz₁, hz₂⟩
        have hzV : z ∈ ν '' G.vertexSet := by
          rcases hz₁ with hzV | hz₁
          · exact hzV
          · obtain ⟨f, hfF, hzf⟩ := mem_iUnion₂.mp hz₁
            exact hmeet f (hFsub hfF) e heG (fun hfe => he (hfe ▸ hfF)) ⟨hzf, hz₂⟩
        obtain ⟨w, hw, rfl⟩ := hzV
        have hwInc := hon e heG w hw hz₂
        have hwEnds : w ∈ ({u, v} : Set α) := hwInc.eq_or_eq_of_isLink hlink
        exact ⟨w, ⟨hw, hwEnds⟩, rfl⟩
      obtain ⟨D, hDU, hmap⟩ := GraphDrawing.glue hG₁ hKL hVunion hEunion hEdisj hν
        D₁ D₂ hmap₁ hmap₂ hcontact
      refine ⟨D, ?_, hmap⟩
      rw [hDU, hD₁U, hD₂U, biUnion_insert]
      ac_rfl
  obtain ⟨D, hDU, hmap⟩ := hconstruct G.edgeSet hE subset_rfl
  obtain ⟨D', hD', hmap'⟩ := GraphDrawing.of_eq (Graph.restrict_self G) D hmap
  exact ⟨D', hD' ▸ hDU, hmap'⟩

end GraphMinor.GM12
