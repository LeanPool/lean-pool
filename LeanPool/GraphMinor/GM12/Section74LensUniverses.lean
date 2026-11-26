/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4SmallSurfaceCopy
import LeanPool.GraphMinor.Surface.EdgeLens
import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Slit lenses in arbitrary surface universes

The lens used in the leaf gluing for XII (7.4), pages 262--263,
is first constructed on a small copy of the closed surface.
A homeomorphism carries the line and the closed set to that
copy, and carries the resulting closed disc back. It preserves
the intersection and boundary conditions needed by the proof.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The disc and boundary parts of the edge-lens construction,
transported from a small copy to any closed surface. -/
theorem exists_edge_lens_disc_universes
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {L Z : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) (huv : u ≠ v) (hZ : IsClosed Z)
    (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ D : Set S, IsClosedDisc D ∧ L ⊆ D ∧ D ∩ Z ⊆ {u, v} ∧
      u ∈ discBd D ∧ v ∈ discBd D ∧ discBd D ∩ L ⊆ {u, v} := by
  obtain ⟨T, t, ⟨e⟩, hT⟩ := exists_small_closed_surface_copy hS
  let : TopologicalSpace T := t
  let : T2Space T := hT.2.1
  have hLine : IsLineWithEnds (e '' L) (e u) (e v) := by
    obtain ⟨a, ha, har, ha0, ha1⟩ := hL.exists_arc
    have hArc : IsArcMap (e ∘ a) := ⟨e.continuous.comp ha.1, e.injective.comp ha.2⟩
    have hh := hArc.isLineWithEnds
    rwa [range_comp, har, Function.comp_apply, Function.comp_apply, ha0, ha1] at hh
  have hClosed : IsClosed (e '' Z) := e.isClosedMap Z hZ
  have hInter : (e '' L) ∩ (e '' Z) ⊆ {e u, e v} := by
    rw [← Set.image_inter e.injective]
    rintro y ⟨x, hx, rfl⟩
    rcases hLZ hx with h | h
    · exact Or.inl (congrArg e h)
    · exact Or.inr (congrArg e h)
  obtain ⟨D, _, _, hD, hLD, hDZ, huBd, hvBd, hBdL, _⟩ :=
    exists_edge_lens hT hLine (e.injective.ne huv) hClosed hInter
  have hDisc := hD.image e.symm.continuous.continuousOn e.continuous.continuousOn
    (fun x _ => e.apply_symm_apply x)
  have hmem : ∀ x : S, x ∈ e.symm '' D ↔ e x ∈ D := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hh : y = e x := by simpa only [e.apply_symm_apply] using congrArg e hxy
      exact hh ▸ hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  have hbdmem : ∀ x : S, x ∈ discBd (e.symm '' D) ↔ e x ∈ discBd D := by
    intro x
    rw [hDisc.2]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hh : y = e x := by simpa only [e.apply_symm_apply] using congrArg e hxy
      exact hh ▸ hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  refine ⟨e.symm '' D, hDisc.1, ?_, ?_, hbdmem u |>.mpr huBd, hbdmem v |>.mpr hvBd, ?_⟩
  · intro x hx
    exact (hmem x).mpr (hLD ⟨x, hx, rfl⟩)
  · intro x hx
    rcases hDZ ⟨(hmem x).mp hx.1, ⟨x, hx.2, rfl⟩⟩ with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective h)
  · intro x hx
    rcases hBdL ⟨(hbdmem x).mp hx.1, ⟨x, hx.2, rfl⟩⟩ with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective h)

end GraphMinor.GM12
