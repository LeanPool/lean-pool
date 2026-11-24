/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section4ArcComplement
import LeanPool.GraphMinor.GM12.Section4CircleSubsetArc
import LeanPool.GraphMinor.GM11.CircuitRegions
import LeanPool.GraphMinor.Surface.HoleDisc
import LeanPool.GraphMinor.GM11.PlaneFacts
import Mathlib.Topology.Connected.Clopen

/-!
# The frontier of a region closure

In XII (4.5), page 253, the eye regions have simple closed
boundaries. A non-dense such region has the same boundary as
its closure. Otherwise a proper compact part of the boundary
would separate the surface, whereas it lies in an arc.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A proper closed set with a circle as a possible boundary
has the whole circle as its frontier, provided both sides
have points outside that circle. -/
theorem frontier_eq_circle_of_two_sides
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {X C : Set S}
    (hX : IsClosed X)
    (hC : IsOArc C) (hsub : frontier X ⊆ C)
    (hCX : C ⊆ X) (hin : (X \ C).Nonempty) (hout : X ≠ univ) :
    frontier X = C := by
  let : CompactSpace S := hS.1
  have hXC : IsCompact (frontier X) := isClosed_frontier.isCompact
  apply Subset.antisymm hsub
  intro p hp
  by_contra hpF
  have hne : (frontier X).Nonempty := nonempty_frontier_iff.mpr
    ⟨hin.mono sdiff_subset, hout⟩
  obtain ⟨L, a, b, hL, hFL, hLC⟩ :=
    exists_arc_containing_nonempty_compact_circle_subset hC hXC hsub hne hp hpF
  have hdis : Disjoint Lᶜ (frontier X) := disjoint_left.mpr
    (fun z hz hzf => hz (hFL hzf))
  rcases GM11.subset_or_disjoint_of_frontier hX
      (isPreconnected_compl_of_arc hS hL) hdis with h | h
  · have he : Xᶜ.Nonempty := nonempty_compl.mpr hout
    obtain ⟨z, hz⟩ := he
    exact hz (h (fun hzL => hz (hCX (hLC hzL))))
  · obtain ⟨z, hzX, hzC⟩ := hin
    exact disjoint_left.mp h (fun hzL => hzC (hLC hzL)) hzX

/-- A non-dense open disc with a simple closed frontier has
closed-disc closure. This supplies the region discs used in
XII (4.5), page 253. -/
theorem closedDisc_closure_of_nondense_openDisc
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {r : Set S} (hr : IsOpenDisc r)
    (hC : IsOArc (frontier r))
    (hproper : closure r ≠ univ) :
    IsClosedDisc (closure r) ∧ discBd (closure r) = frontier r := by
  have hrne : r.Nonempty := by
    obtain ⟨f⟩ := hr.2
    exact ⟨(f ⟨0, by simp [OpenUnitDisc]⟩).val,
      (f ⟨0, by simp [OpenUnitDisc]⟩).property⟩
  have hfr : frontier (closure r) = frontier r := by
    apply frontier_eq_circle_of_two_sides hS isClosed_closure hC
      frontier_closure_subset frontier_subset_closure
    · obtain ⟨x, hx⟩ := hrne
      refine ⟨x, subset_closure hx, ?_⟩
      intro hxf
      exact hxf.2 (hr.1.interior_eq.symm ▸ hx)
    · exact hproper
  have hdiff : closure r \ r = frontier r := by
    rw [frontier, hr.1.interior_eq]
  have hbd : Disjoint (closure r) (bd S) := by
    apply disjoint_left.mpr
    intro x hx hxb
    exact hxb (hS.2.2 x)
  have hout : ∀ x ∈ closure r \ r, x ∈ closure (closure r)ᶜ := by
    intro x hx
    have hxf : x ∈ frontier (closure r) := hfr.symm ▸ (hdiff ▸ hx)
    rw [frontier_eq_closure_inter_closure] at hxf
    exact hxf.2
  simpa only [hdiff] using closure_disc (Surface.IsClosedSurface.isSurface hS) hr hbd
    (hdiff ▸ hC) hout

end GraphMinor.GM12
