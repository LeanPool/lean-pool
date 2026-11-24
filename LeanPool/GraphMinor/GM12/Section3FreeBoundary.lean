/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Theorem61
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Free boundary vertices give the enclosing-circle bound

To verify (3.1)(v) in the proof of XII (3.2), page 247, the enclosed
boundary vertices are free and lie on the small side selected by the
tangle. Their number is at most the separation order. The common
vertices of that separation lie on the enclosing circle, which gives
the required bound. The disc on the small side is the enclosing disc.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 Hypergraph

/-- The free-set step in the verification of XII (3.1)(v) in the proof
of (3.2), page 247. The tangle separation for the enclosing disc has
all common vertices on its frontier. -/
theorem free_set_card_le_frontier_of_selected_disc
    {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {X D : Set S} (hfree : IsFreeSet Γ.toHypergraph T θ X)
    (hXD : X ⊆ D)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    X.ncard ≤ (Γ.V ∩ frontier D).ncard := by
  have hXA : X ⊆ ((PaintingOrDrawing.drawing Γ).inter D).vertexSet :=
    fun x hx => ⟨hfree.1 hx, hXD hx⟩
  apply (hfree.2.2 hm hXA).trans
  apply Set.ncard_le_ncard ?_ (Γ.finite_V.subset inter_subset_left)
  intro x hx
  have hh := inter_outside_subset hx
  exact ⟨hh.2, hh.1⟩

/-- The prescribed free boundary has at most as many vertices as a
circle enclosing its disc and selected by the tangle. This is precisely
the counting implication used for XII (3.1)(v), page 247. -/
theorem boundary_vertex_count_le_of_free_of_selected_disc
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {δ D : Set S} (hD : IsClosedDisc D) (hδD : δ ⊆ D)
    (hfree : IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd δ))
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    (Γ.V ∩ discBd δ).ncard ≤ (Γ.V ∩ discBd D).ncard := by
  rw [← IsClosedDisc.frontier_eq_discBd hS hD]
  exact free_set_card_le_frontier_of_selected_disc hfree
    (fun _ hx => hδD (Surface.discBd_subset δ hx.2)) hm

end GraphMinor.GM12
