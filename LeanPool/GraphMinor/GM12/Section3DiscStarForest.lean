/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section3DiscStarLines
import LeanPool.GraphMinor.GM12.Section3StarDrawingForest
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# A connected forest inside a feasibility disc

For XII (3.1), page 245, draw a star from an interior centre to the
finite prescribed boundary set of a feasibility disc. The line and
drawing constructions give a forest. Every leaf is joined to the
centre by one edge, proving connectedness. Only the prescribed leaves
lie on the disc boundary.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A finite boundary set of a closed disc can be connected by a
forest drawing inside it, meeting the disc boundary exactly in that
set. This is the local forest used for XII (3.1), page 245. -/
theorem exists_connected_forest_in_disc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {D Z : Set S} (hD : IsClosedDisc D) (hZ : Z.Finite) (hZD : Z ⊆ discBd D) :
    ∃ (H : Drawing S) (c : S), c ∈ discInt D ∧ H.U ⊆ D ∧ H.V = insert c Z ∧
      H.U ∩ discBd D = Z ∧ IsGraphForest H.toGraph ∧ IsConnectedDrawing H := by
  obtain ⟨c, hc, L, hlines, hmeet⟩ := exists_star_lines_in_disc hD hZD
  have hcZ : c ∉ Z := fun h => hc.2 (hZD h)
  obtain ⟨H, hU, hV, hE, hforest⟩ := exists_forest_drawing_of_finite_star hZ c L
    (fun a ha => (hlines a ha).1) hmeet hcZ
  have hUD : H.U ⊆ D := by
    rw [hU]
    apply union_subset
    · exact singleton_subset_iff.mpr hc.1
    · exact iUnion₂_subset fun a ha => (hlines a ha).2.1
  have hboundary : H.U ∩ discBd D = Z := by
    apply Subset.antisymm
    · rintro x ⟨hxH, hxB⟩
      rw [hU] at hxH
      rcases hxH with hxC | hxL
      · have hxc : x = c := hxC
        exact False.elim (hc.2 (hxc ▸ hxB))
      · obtain ⟨a, ha⟩ := mem_iUnion.mp hxL
        obtain ⟨haZ, hxa⟩ := mem_iUnion.mp ha
        have hx : x ∈ L a ∩ discBd D := ⟨hxa, hxB⟩
        rw [(hlines a haZ).2.2] at hx
        exact (show x = a from hx) ▸ haZ
    · intro x hxZ
      refine ⟨?_, hZD hxZ⟩
      rw [hU]
      exact Or.inr (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxZ, (hlines x hxZ).1.right_mem⟩⟩)
  have hlinks : ∀ a ∈ Z, H.toGraph.IsLink (L a \ {c, a}) c a := by
    intro a ha
    have hinter : L a ∩ insert c Z = {c, a} := by
      apply Subset.antisymm
      · rintro x ⟨hxL, hxV⟩
        rcases hxV with hxc | hxZ
        · exact Or.inl hxc
        · have hx : x ∈ L a ∩ discBd D := ⟨hxL, hZD hxZ⟩
          rw [(hlines a ha).2.2] at hx
          exact Or.inr hx
      · rintro x (hxc | hxa)
        · subst x
          exact ⟨(hlines a ha).1.left_mem, Or.inl rfl⟩
        · subst x
          exact ⟨(hlines a ha).1.right_mem, Or.inr ha⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hE]
      exact mem_image_of_mem (fun a => L a \ {c, a}) ha
    · rw [hV]
      exact Or.inl rfl
    · rw [hV]
      exact Or.inr ha
    · rw [closure_sdiff_pair (hlines a ha).1, hV, hinter]
  have hcentre : c ∈ H.V := hV.symm ▸ (show c ∈ insert c Z from Or.inl rfl)
  have hwalk : ∀ x ∈ H.V, Nonempty (GraphWalk H.toGraph c x) := by
    intro x hx
    have hxV : x ∈ H.V := hx
    rw [hV] at hx
    rcases hx with hxc | hxZ
    · rw [hxc]
      exact ⟨.nil hcentre⟩
    · exact ⟨.cons (hlinks x hxZ) (.nil hxV)⟩
  refine ⟨H, c, hc, hUD, hV, hboundary, hforest, ?_⟩
  intro a ha b hb
  obtain ⟨W₁⟩ := hwalk a ha
  obtain ⟨W₂⟩ := hwalk b hb
  exact ⟨W₁.reverse.append W₂⟩

end GraphMinor.GM12
