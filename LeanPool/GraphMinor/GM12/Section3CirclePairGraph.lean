/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.SurfaceGraph
public import LeanPool.GraphMinor.GM12.Section3MeetingDiscs
import LeanPool.GraphMinor.Surface.ArcErase
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# A finite graph presentation of two disjoint circles

The first two-loop shape in VII Section 8, used by XII (3.1), page 245,
is a finite graph. Start with its two attachment vertices. Adding each
disjoint circle meets the existing carrier once, so its remaining part
is path-connected. The proved curve-addition construction supplies the
finite graph while retaining both attachment vertices.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem finConn_oArc_diff_of_inter_singleton
    {S : Type*} [TopologicalSpace S] {F Q : Set S} {a : S}
    (hF : IsOArc F) (hinter : F ∩ Q = {a}) : FinConn (F \ Q) := by
  have ha : a ∈ F ∩ Q := hinter.symm ▸ mem_singleton a
  have heq : F \ Q = F \ {a} := by
    ext x
    constructor
    · rintro ⟨hxF, hxQ⟩
      refine ⟨hxF, ?_⟩
      intro hxa
      exact hxQ (hxa.symm ▸ ha.2)
    · rintro ⟨hxF, hxa⟩
      refine ⟨hxF, fun hxQ => ?_⟩
      exact hxa (hinter ▸ (show x ∈ F ∩ Q from ⟨hxF, hxQ⟩))
  rw [heq]
  exact finConn_of_isPreconnected (isPathConnected_oArc_diff hF ha.1).isConnected.isPreconnected

/-- Two disjoint circles have a finite graph presentation containing
chosen attachment vertices in its vertex set. -/
theorem exists_graph_of_disjoint_circle_pair
    {S : Type*} [TopologicalSpace S] [T2Space S] {F A : Set S} {a b : S}
    (hF : IsOArc F) (hA : IsOArc A) (hdis : Disjoint F A) (ha : a ∈ F) (hb : b ∈ A) :
    ∃ V E, {a, b} ⊆ V ∧ IsGraph V E ∧ gr V E = F ∪ A := by
  have h0 : IsGraph ({a, b} : Set S) ∅ := by
    refine ⟨(finite_singleton b).insert a, finite_empty, ?_, ?_⟩
    · intro e he
      exact False.elim he
    · intro e he
      exact False.elim he
  have hgr0 : gr ({a, b} : Set S) ∅ = {a, b} := by simp [gr]
  have hinterF : F ∩ gr ({a, b} : Set S) ∅ = {a} := by
    rw [hgr0]
    apply Subset.antisymm
    · rintro x ⟨hxF, hxa | hxb⟩
      · exact hxa
      · exact False.elim (Set.disjoint_left.mp hdis hxF (hxb.symm ▸ hb))
    · intro x hx
      have hxa : x = a := hx
      rw [hxa]
      exact ⟨ha, Or.inl rfl⟩
  obtain ⟨V₁, E₁, hV₁, hG₁, hgr₁, _⟩ :=
    h0.add_curve hF (finConn_oArc_diff_of_inter_singleton hF hinterF)
  have hinterA : A ∩ gr V₁ E₁ = {b} := by
    rw [hgr₁, hgr0]
    apply Subset.antisymm
    · rintro x ⟨hxA, (hxa | hxb) | hxF⟩
      · exact False.elim (Set.disjoint_left.mp hdis (hxa.symm ▸ ha) hxA)
      · exact hxb
      · exact False.elim (Set.disjoint_left.mp hdis hxF hxA)
    · intro x hx
      have hxb : x = b := hx
      rw [hxb]
      exact ⟨hb, Or.inl (Or.inr rfl)⟩
  obtain ⟨V₂, E₂, hV₂, hG₂, hgr₂, _⟩ :=
    hG₁.add_curve hA (finConn_oArc_diff_of_inter_singleton hA hinterA)
  refine ⟨V₂, E₂, hV₁.trans hV₂, hG₂, ?_⟩
  rw [hgr₂, hgr₁, hgr0]
  apply Subset.antisymm
  · rintro x (((hxa | hxb) | hxF) | hxA)
    · exact Or.inl (hxa.symm ▸ ha)
    · exact Or.inr (hxb.symm ▸ hb)
    · exact Or.inl hxF
    · exact Or.inr hxA
  · rintro x (hxF | hxA)
    · exact Or.inl (Or.inr hxF)
    · exact Or.inr hxA

/-- The first two-loop shape is a finite graph in which the joining
line is one edge and meets the vertex set only at its two ends. -/
theorem exists_graph_of_disjoint_circles_with_joining_line
    {S : Type*} [TopologicalSpace S] [T2Space S] {F A P : Set S} {a b : S}
    (hF : IsOArc F) (hA : IsOArc A) (hdis : Disjoint F A)
    (hP : IsLineWithEnds P a b) (ha : a ∈ F) (hb : b ∈ A)
    (hPF : P ∩ F = {a}) (hPA : P ∩ A = {b}) :
    ∃ V E, IsGraph V E ∧ gr V E = F ∪ A ∪ P ∧ P ∈ E ∧ P ∩ V = {a, b} := by
  obtain ⟨V, E, hverts, hG, hgr⟩ := exists_graph_of_disjoint_circle_pair hF hA hdis ha hb
  have hab : a ≠ b := fun he => Set.disjoint_left.mp hdis ha (he.symm ▸ hb)
  have haV : a ∈ V := hverts (Or.inl rfl)
  have hbV : b ∈ V := hverts (Or.inr rfl)
  have hinter : P ∩ gr V E = {a, b} := by
    rw [hgr, inter_union_distrib_left, hPF, hPA, singleton_union]
  obtain ⟨hG', hgr'⟩ := hG.add_arc hab hP haV hbV hinter
  refine ⟨V, insert P E, hG', ?_, Or.inl rfl, ?_⟩
  · rw [hgr', hgr]
  · apply Subset.antisymm
    · rintro x ⟨hxP, hxV⟩
      exact hinter ▸ (show x ∈ P ∩ gr V E from ⟨hxP, Or.inl hxV⟩)
    · rintro x (hxa | hxb)
      · rw [hxa]
        exact ⟨hP.left_mem, haV⟩
      · rw [hxb]
        exact ⟨hP.right_mem, hbV⟩

end GraphMinor.GM12
