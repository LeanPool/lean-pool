/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.EdgeLens
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Parallel copies of target edges

The loopless minimum-degree-two replacement at the start of XII
(4.3), page 249, may add a parallel copy of an edge inside a
thin lens. The lens avoids the rest of the drawing. One of its
boundary arcs is the new copy, with the same ends and with no
other point on the original line or the forbidden closed set.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

private theorem line_image {S U : Type*} [TopologicalSpace S] [TopologicalSpace U] [T2Space U]
    {j : S → U} (hc : Continuous j) (hi : Function.Injective j)
    {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) :
    IsLineWithEnds (j '' L) (j u) (j v) := by
  obtain ⟨a, ha, hr, ha0, ha1⟩ := hL.exists_arc
  have ha' : IsArcMap (j ∘ a) := ⟨hc.comp ha.1, hi.comp ha.2⟩
  simpa only [range_comp, hr, Function.comp_apply, ha0, ha1] using ha'.isLineWithEnds

private theorem parallel_line_small
    {S : Type} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {L Z : Set S} {u v : S} (hL : IsLineWithEnds L u v) (huv : u ≠ v)
    (hZ : IsClosed Z) (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ P : Set S, IsLineWithEnds P u v ∧ P ∩ Z ⊆ {u, v} ∧ P ∩ L = {u, v} := by
  obtain ⟨D, _, _, hD, hLD, hDZ, huD, hvD, hbdL, _⟩ := exists_edge_lens hS hL huv hZ hLZ
  obtain ⟨a, b, hab, ha0, ha1, hr⟩ := hD.isOArc_discBd.exists_arcs huD hvD huv
  have ha : IsLineWithEnds (range a) u v := by
    simpa only [ha0, ha1] using hab.1.isLineWithEnds
  have haBd : range a ⊆ discBd D := fun x hx => hr ▸ Or.inl hx
  have haD : range a ⊆ D := haBd.trans (discBd_subset D)
  refine ⟨range a, ha, ?_, ?_⟩
  · exact fun x hx => hDZ ⟨haD hx.1, hx.2⟩
  · apply Set.Subset.antisymm
    · exact fun x hx => hbdL ⟨haBd hx.1, hx.2⟩
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨ha.left_mem, hL.left_mem⟩
      · have hxv := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨ha.right_mem, hL.right_mem⟩

/-- A parallel copy of a line avoiding a forbidden closed set away
from its two ends, used in the target replacement of XII (4.3). -/
theorem exists_parallel_line
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {L Z : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) (huv : u ≠ v) (hZ : IsClosed Z)
    (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ P : Set S, IsLineWithEnds P u v ∧ P ∩ Z ⊆ {u, v} ∧ P ∩ L = {u, v} := by
  let : CompactSpace S := hS.1
  have hsurf : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨n, m, c, ⟨e⟩⟩ := classification S hsurf inferInstance
  let : T2Space (SurfaceModel n m c) := e.t2Space
  have hM : IsClosedSurface (SurfaceModel n m c) := by
    refine ⟨e.compactSpace, e.t2Space, ?_⟩
    intro x
    have hx := (isInteriorPoint_homeomorph_iff e (e.symm x)).mpr (hS.2.2 (e.symm x))
    simpa only [e.apply_symm_apply] using hx
  have hL' := line_image e.continuous e.injective hL
  have hZ' : IsClosed (e.symm ⁻¹' Z) := hZ.preimage e.symm.continuous
  have hLZ' : (e '' L) ∩ (e.symm ⁻¹' Z) ⊆ {e u, e v} := by
    rintro _ ⟨⟨x, hxL, rfl⟩, hxZ⟩
    have hx : x ∈ Z := by simpa only [mem_preimage, e.symm_apply_apply] using hxZ
    rcases hLZ ⟨hxL, hx⟩ with h | h
    · exact Or.inl (congrArg e h)
    · exact Or.inr (Set.mem_singleton_iff.mpr (congrArg e (Set.mem_singleton_iff.mp h)))
  obtain ⟨P, hP, hPZ, hPL⟩ := parallel_line_small hM hL' (fun h => huv (e.injective h)) hZ' hLZ'
  refine ⟨e.symm '' P, ?_, ?_, ?_⟩
  · have hline := line_image e.symm.continuous e.symm.injective hP
    simpa only [e.symm_apply_apply] using hline
  · rintro _ ⟨⟨x, hxP, rfl⟩, hxZ⟩
    have hxends := hPZ ⟨hxP, hxZ⟩
    rcases hxends with h | h
    · exact Or.inl ((congrArg e.symm h).trans (e.symm_apply_apply u))
    · exact Or.inr (Set.mem_singleton_iff.mpr
        ((congrArg e.symm (Set.mem_singleton_iff.mp h)).trans (e.symm_apply_apply v)))
  · apply Set.Subset.antisymm
    · rintro _ ⟨⟨x, hxP, rfl⟩, hxL⟩
      have hxL' : x ∈ e '' L := ⟨e.symm x, hxL, e.apply_symm_apply x⟩
      have hxends := hPL.subset ⟨hxP, hxL'⟩
      rcases hxends with h | h
      · exact Or.inl ((congrArg e.symm h).trans (e.symm_apply_apply u))
      · exact Or.inr (Set.mem_singleton_iff.mpr
          ((congrArg e.symm (Set.mem_singleton_iff.mp h)).trans (e.symm_apply_apply v)))
    · intro x hx
      rcases hx with hxu | hx
      · exact hxu ▸ ⟨⟨e u, hP.left_mem, e.symm_apply_apply u⟩, hL.left_mem⟩
      · have hxv := Set.mem_singleton_iff.mp hx
        exact hxv ▸ ⟨⟨e v, hP.right_mem, e.symm_apply_apply v⟩, hL.right_mem⟩

end GraphMinor.GM12
