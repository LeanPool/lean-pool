/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM16.LineInFace
import LeanPool.GraphMinor.GM16.LineDial
import LeanPool.GraphMinor.GM16.TwoFaceDial
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.Surface.CutLift

/-!
# Rigidity from disc faces and their common boundary lines

Split a normal circle at two points containing all its drawing
vertices. Each open half lies in one face. If the faces coincide,
the circle bounds an empty dial in that face. Otherwise their two
common points lie on the drawing. A common boundary line joins
them, and the two-face construction gives a dial. This reduces the
wall rigidity check in XVI (4.2) to its face geometry.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11 GM14

/-- A drawing with disc faces and boundary lines joining common face
points is rigid. The hypotheses describe the face closures and their
intersections, rather than assume dials for normal circles. -/
theorem isRigid_of_disc_faces {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S}
    (hFaces : ∀ r ∈ H.R, IsClosedDisc (closure r) ∧
      closure r ∩ H.U ⊆ discBd (closure r))
    (hJoin : ∀ r ∈ H.R, ∀ s ∈ H.R, r ≠ s → ∀ a b : S, a ≠ b →
      a ∈ closure r ∩ closure s → b ∈ closure r ∩ closure s →
      ∃ K, IsLineWithEnds K a b ∧ K ⊆ closure r ∩ closure s) : IsRigid H := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  intro F hF hNormal hCard
  obtain ⟨X, _, hVX, hXF, hXCard⟩ := (infinite_of_isOArc hF).exists_superset_ncard_eq
    (inter_subset_left : F ∩ H.V ⊆ F) (H.finite_V.subset inter_subset_right) hCard
  obtain ⟨a,b,hab,hX⟩ := Set.ncard_eq_two.mp hXCard
  have haF : a ∈ F := hXF (hX.symm ▸ mem_insert a {b})
  have hbF : b ∈ F := hXF (hX.symm ▸ mem_insert_of_mem a rfl)
  have hFPair : F ∩ H.V ⊆ {a,b} := hX ▸ hVX
  obtain ⟨P₁,P₂,hP₁,hP₂,hUnion,_⟩ := hF.lines haF hbF hab
  have hP₁F : P₁ ⊆ F := hUnion ▸ subset_union_left
  have hP₂F : P₂ ⊆ F := hUnion ▸ subset_union_right
  have hAvoid (P : Set S) (hPF : P ⊆ F) : Disjoint (P \ {a,b}) H.U := by
    apply disjoint_left.mpr
    rintro x ⟨hxP,hxEnds⟩ hxU
    exact hxEnds (hFPair ⟨hPF hxP,hNormal ⟨hPF hxP,hxU⟩⟩)
  obtain ⟨r,hr,hOpen₁,hClosed₁⟩ := exists_face_containing_line hP₁ (hAvoid P₁ hP₁F)
  obtain ⟨s,hs,hOpen₂,hClosed₂⟩ := exists_face_containing_line hP₂ (hAvoid P₂ hP₂F)
  have hEmpty (r : Set S) (hr : r ∈ H.R) : Disjoint (interior (closure r)) H.U := by
    apply disjoint_left.mpr
    intro x hx hxU
    have hxBd := (hFaces r hr).2 ⟨interior_subset hx,hxU⟩
    have hxFr : x ∈ frontier (closure r) :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS (hFaces r hr).1).symm ▸ hxBd
    exact hxFr.2 hx
  by_cases hrs : r = s
  · subst s
    apply exists_isDial_of_circle_in_empty_disc hS (hFaces r hr).1 hF
      (hUnion ▸ union_subset hClosed₁ hClosed₂) (hEmpty r hr)
  have hMeetU : closure r ∩ closure s ⊆ H.U := by
    rintro x ⟨hxr,hxs⟩
    by_contra hn
    have hxr' := (closure_region_subset hr hxr).resolve_right hn
    have hxs' := (closure_region_subset hs hxs).resolve_right hn
    exact hrs (region_eq_of_mem hr hs hxr' hxs')
  have haBoth : a ∈ closure r ∩ closure s := ⟨hClosed₁ hP₁.left_mem,hClosed₂ hP₂.left_mem⟩
  have hbBoth : b ∈ closure r ∩ closure s := ⟨hClosed₁ hP₁.right_mem,hClosed₂ hP₂.right_mem⟩
  obtain ⟨K,hK,hKBoth⟩ := hJoin r hr s hs hrs a b hab haBoth hbBoth
  have hEnds : F ∩ H.V = {a,b} := by
    apply subset_antisymm hFPair
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨haF,hNormal ⟨haF,hMeetU haBoth⟩⟩
    · rw [mem_singleton_iff] at hx
      subst x
      exact ⟨hbF,hNormal ⟨hbF,hMeetU hbBoth⟩⟩
  rw [← hUnion] at hNormal hEnds ⊢
  apply exists_isDial_of_two_faces hS (hFaces r hr).1 (hFaces s hs).1 hP₁ hP₂ hK hab
    hClosed₁ hClosed₂ _ _ (hKBoth.trans hMeetU)
    (line_inter_face_boundary_subset hS hr (hFaces r hr).1 hOpen₁)
    (line_inter_face_boundary_subset hS hs (hFaces s hs).1 hOpen₂)
    (hFaces r hr).2 (hFaces s hs).2 _ hNormal hEnds
  · exact fun x hx => (hFaces r hr).2 ⟨(hKBoth hx).1,hMeetU (hKBoth hx)⟩
  · exact fun x hx => (hFaces s hs).2 ⟨(hKBoth hx).2,hMeetU (hKBoth hx)⟩
  · exact fun x hx => (hFaces r hr).2 ⟨hx.1,hMeetU hx⟩

end GraphMinor.GM16
