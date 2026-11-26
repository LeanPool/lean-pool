/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Cutting off a subdisc in an empty face

A line in a face and a boundary subline with the same ends form a
circle. The disc it bounds inside the face meets the drawing exactly
in the boundary subline. This supplies each half of the two-face
dial in the rigidity check of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11

/-- If a closed subset lies in another closed set, points of the first
on the frontier of the second are on its own frontier. -/
theorem inter_frontier_subset_frontier_of_subset {S : Type*} [TopologicalSpace S]
    {A B : Set S} (hAB : A ⊆ B) : A ∩ frontier B ⊆ frontier A := by
  rintro x ⟨hx,hxB⟩
  exact ⟨subset_closure hx, fun hxInt => hxB.2 (interior_mono hAB hxInt)⟩

/-- The part cut off inside an empty face by a line meets the drawing
exactly in the corresponding boundary line. -/
theorem exists_face_subdisc {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {C P K U : Set S} {a b : S}
    (hC : IsClosedDisc C) (hP : IsLineWithEnds P a b) (hK : IsLineWithEnds K a b)
    (hPC : P ⊆ C) (hKC : K ⊆ discBd C) (hKU : K ⊆ U)
    (hPU : P ∩ discBd C ⊆ {a,b}) (hEmpty : C ∩ U ⊆ discBd C) :
    ∃ Δ, Δ ⊆ C ∧ IsClosedDisc Δ ∧ discBd Δ = P ∪ K ∧
      Δ ∩ discBd C = K ∧ Δ ∩ U = K := by
  have hPK : P ∩ K ⊆ {a,b} := fun _ hx => hPU ⟨hx.1,hKC hx.2⟩
  have hCircle := isOArc_union hP hK hPK
  obtain ⟨Δ,⟨hΔC,hΔ,hbd,_⟩,_⟩ := disc_oArc C (P ∪ K) hC
    (union_subset hPC (hKC.trans (Surface.discBd_subset C))) hCircle
  have hKΔ : K ⊆ Δ := fun _ hx => Surface.discBd_subset Δ (hbd.symm ▸ Or.inr hx)
  have hEnds : ({a,b} : Set S) ⊆ K := by
    intro x hx
    rcases hx with rfl | hx
    · exact hK.left_mem
    · rw [mem_singleton_iff] at hx
      exact hx.symm ▸ hK.right_mem
  have hBoundary : Δ ∩ discBd C = K := by
    apply subset_antisymm
    · rintro x ⟨hxΔ,hxC⟩
      have hxFr : x ∈ frontier Δ := inter_frontier_subset_frontier_of_subset hΔC
        ⟨hxΔ,(GM11.IsClosedDisc.frontier_eq_discBd hS hC).symm ▸ hxC⟩
      have hx : x ∈ P ∪ K := hbd ▸ (GM11.IsClosedDisc.frontier_eq_discBd hS hΔ ▸ hxFr)
      exact hx.elim (fun hxP => hEnds (hPU ⟨hxP,hxC⟩)) id
    · intro x hx
      exact ⟨hKΔ hx,hKC hx⟩
  refine ⟨Δ,hΔC,hΔ,hbd,hBoundary,subset_antisymm ?_ ?_⟩
  · rintro x ⟨hxΔ,hxU⟩
    exact hBoundary ▸ (show x ∈ Δ ∩ discBd C from ⟨hxΔ,hEmpty ⟨hΔC hxΔ,hxU⟩⟩)
  · intro x hx
    exact ⟨hKΔ hx,hKU hx⟩

end GraphMinor.GM16
