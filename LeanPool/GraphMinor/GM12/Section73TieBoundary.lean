/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.CutLift
import Mathlib.Topology.Separation.Basic

/-!
# Boundaries of the pieces of a tie

The walk selection in XII (7.3), page 262, uses the ties of XI
(9.2). Their disc and line pieces meet only at finitely many
attachment points. Away from these points, a boundary of a piece
is on the boundary of the union. A line or circle is the closure
of itself with finitely many points removed. Thus a closed set
containing the boundary of the union contains these boundaries
at the attachment points too.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Removing finitely many points from a line leaves a dense
subset of that line, including at its ends. -/
theorem line_subset_closure_sdiff_finite
    {S : Type*} [TopologicalSpace S] {L T : Set S} {p q : S}
    (hL : IsLineWithEnds L p q) (hT : T.Finite) : L ⊆ closure (L \ T) := by
  obtain ⟨a, ha, hr, _, _⟩ := hL.exists_arc
  have hpre : (a ⁻¹' T).Finite := hT.preimage ha.2.injOn
  have hd : Dense ((univ : Set unitInterval) \ a ⁻¹' T) := dense_univ.sdiff_finite hpre
  rintro x hx
  obtain ⟨t, rfl⟩ := hr.symm ▸ hx
  have ht : t ∈ closure ((univ : Set unitInterval) \ a ⁻¹' T) := by
    rw [hd.closure_eq]
    exact mem_univ t
  apply closure_mono (s := a '' ((univ : Set unitInterval) \ a ⁻¹' T))
    (fun z hz => ?_) (image_closure_subset_closure_image ha.1 ⟨t, ht, rfl⟩)
  obtain ⟨s, hs, rfl⟩ := hz
  exact ⟨hr ▸ mem_range_self s, hs.2⟩

/-- Removing finitely many points from a circle leaves a dense
subset of the circle. Split it into two lines and apply the
line result to each. -/
theorem oArc_subset_closure_sdiff_finite
    {S : Type*} [TopologicalSpace S] [T2Space S] {F T : Set S}
    (hF : IsOArc F) (hT : T.Finite) : F ⊆ closure (F \ T) := by
  obtain ⟨e⟩ := hF
  let p : S := (e 1).1
  have hp : p ∈ F := (e 1).2
  have hF : IsOArc F := ⟨e⟩
  obtain ⟨q, hq, hpq⟩ := hF.exists_ne p
  obtain ⟨A, B, hA, hB, hAB, _⟩ := hF.lines hp hq hpq.symm
  have hAF : A ⊆ F := hAB ▸ subset_union_left
  have hBF : B ⊆ F := hAB ▸ subset_union_right
  intro x hx
  rcases (hAB.symm ▸ hx) with hx | hx
  · exact closure_mono (sdiff_subset_sdiff_left hAF)
      (line_subset_closure_sdiff_finite hA hT hx)
  · exact closure_mono (sdiff_subset_sdiff_left hBF)
      (line_subset_closure_sdiff_finite hB hT hx)

/-- Outside a closed second piece, boundary points of a first
piece remain boundary points of their union. -/
theorem frontier_sdiff_subset_frontier_union
    {S : Type*} [TopologicalSpace S] {A B : Set S} (hB : IsClosed B) :
    frontier A \ B ⊆ frontier (A ∪ B) := by
  intro x hx
  refine ⟨closure_mono subset_union_left hx.1.1, ?_⟩
  intro hi
  have hopen : IsOpen (interior (A ∪ B) ∩ Bᶜ) := isOpen_interior.inter hB.isOpen_compl
  have hsub : interior (A ∪ B) ∩ Bᶜ ⊆ A := by
    intro y hy
    exact (interior_subset hy.1).resolve_right hy.2
  exact hx.1.2 (interior_maximal hsub hopen ⟨hi, hx.2⟩)

/-- A boundary contained in a closed set on a dense subset is
contained in it everywhere. -/
theorem subset_of_frontier_union_of_dense_complement
    {S : Type*} [TopologicalSpace S] {A B F U : Set S}
    (hB : IsClosed B) (hU : IsClosed U) (hFA : F ⊆ frontier A)
    (hdense : F ⊆ closure (F \ (F ∩ B)))
    (hfront : frontier (A ∪ B) ⊆ U) : F ⊆ U := by
  apply hdense.trans
  apply closure_minimal _ hU
  intro x hx
  exact hfront (frontier_sdiff_subset_frontier_union hB
    ⟨hFA hx.1, fun hxB => hx.2 ⟨hx.1, hxB⟩⟩)

/-- A circle on the boundary of one piece is in every closed set
containing the boundary of the union, when the second piece meets
it only finitely often. -/
theorem oArc_subset_of_frontier_union_of_finite_attachment
    {S : Type*} [TopologicalSpace S] [T2Space S] {A B F U : Set S}
    (hB : IsClosed B) (hU : IsClosed U) (hFA : F ⊆ frontier A)
    (hF : IsOArc F) (hfinite : (F ∩ B).Finite)
    (hfront : frontier (A ∪ B) ⊆ U) : F ⊆ U :=
  subset_of_frontier_union_of_dense_complement hB hU hFA
    (oArc_subset_closure_sdiff_finite hF hfinite) hfront

/-- The corresponding boundary extension for a line. The finite
attachment points are recovered by continuity along the line. -/
theorem line_subset_of_frontier_union_of_finite_attachment
    {S : Type*} [TopologicalSpace S] {A B F U : Set S} {p q : S}
    (hB : IsClosed B) (hU : IsClosed U) (hFA : F ⊆ frontier A)
    (hF : IsLineWithEnds F p q) (hfinite : (F ∩ B).Finite)
    (hfront : frontier (A ∪ B) ⊆ U) : F ⊆ U :=
  subset_of_frontier_union_of_dense_complement hB hU hFA
    (line_subset_closure_sdiff_finite hF hfinite) hfront

end GraphMinor.GM12
