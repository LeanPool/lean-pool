/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM16.LineDrawingPath
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# Dials whose intersection with a drawing is a line

In the sphere-wall proof of XVI (4.2), a disc bounded by a normal
circle either misses the drawing in its interior, or meets it in
a line between the two boundary vertices. In the latter case the
restricted drawing is a path, by the line-to-path lemma. This file
supplies that last conversion without a graph connectivity assumption.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11 GM14

/-- A disc meeting the drawing in a line joining its two boundary
vertices satisfies the second alternative in the definition of a dial. -/
theorem isDial_of_line_intersection {S : Type*} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {F Δ : Set S} {a b : S}
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hNormal : F ∩ H.U ⊆ H.V) (hab : a ≠ b)
    (hEnds : F ∩ H.V = {a,b}) (hLine : IsLineWithEnds (H.U ∩ Δ) a b) :
    IsDial H F Δ := by
  obtain ⟨hV,hU⟩ := interSet_V_and_U hΔ.isClosed (hbd.symm ▸ hNormal)
  have ha : a ∈ (H.interSet Δ).V := by
    rw [hV]
    exact ⟨(hEnds.symm ▸ (show a ∈ ({a,b} : Set S) from mem_insert _ _)).2,
      hLine.left_mem.2⟩
  have hb : b ∈ (H.interSet Δ).V := by
    rw [hV]
    exact ⟨(hEnds.symm ▸ (show b ∈ ({a,b} : Set S) from mem_insert_of_mem _ rfl)).2,
      hLine.right_mem.2⟩
  refine ⟨hΔ,hbd,Or.inr ⟨a,b,hab,hEnds,?_⟩⟩
  exact drawing_isPathBetween_of_isLine_U (hU.symm ▸ hLine) hab ha hb

/-- A circle contained in a closed disc whose interior misses the drawing
bounds a dial with no drawing in its interior. This is the one-face case
of the rigidity check in XVI (4.2). -/
theorem exists_isDial_of_circle_in_empty_disc {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {F C : Set S}
    (hC : IsClosedDisc C) (hF : IsOArc F) (hFC : F ⊆ C)
    (hEmpty : Disjoint (interior C) H.U) : ∃ Δ, IsDial H F Δ := by
  obtain ⟨Δ, ⟨hΔC, hΔ, hbd, _⟩, _⟩ := disc_oArc C F hC hFC hF
  have hfront : frontier Δ = F := (GM11.IsClosedDisc.frontier_eq_discBd hS hΔ).trans hbd
  refine ⟨Δ, hΔ, (subBd_eq_frontier Δ).trans hfront, Or.inl ?_⟩
  rintro x ⟨hxΔ, hxH⟩
  by_contra hxF
  have hxInt : x ∈ interior Δ := by
    by_contra hn
    have hxFr : x ∈ frontier Δ := ⟨subset_closure hxΔ, hn⟩
    exact hxF (hfront ▸ hxFr)
  exact (disjoint_left.mp hEmpty) (interior_mono hΔC hxInt) hxH

end GraphMinor.GM16
