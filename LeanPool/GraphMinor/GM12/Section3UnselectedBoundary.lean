/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Theorem61

/-!
# A free set outside an unselected disc bounds its boundary

For the one-disc sphere case of XII (3.2), pages 247--248, take a
disc which is not a small side of the tangle. If its boundary has
at least the tangle order, the free-set size bound suffices. Otherwise
the first tangle axiom selects the reverse separation. Freeness of
the prescribed vertices on that reverse side bounds them by the
separation order, which is at most the boundary vertex count.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 Hypergraph

/-- The unselected-side counting step in the one-disc case of
Graph Minors XII (3.2), pages 247--248. -/
theorem free_set_card_le_frontier_of_not_selected
    {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T) {Z D : Set S}
    (hfree : IsFreeSet Γ.toHypergraph T θ Z) (hD : IsClosed D)
    (hn : Γ.IsNormal (frontier D))
    (hZ : Z ⊆ closure (univ \ D))
    (hnot : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∉ T) :
    Z.ncard ≤ (Γ.V ∩ frontier D).ncard := by
  let G : PaintingOrDrawing S := .drawing Γ
  have hord : separationOrder (G.inter D) (G.interOutside D) ≤ (Γ.V ∩ frontier D).ncard := by
    apply Set.ncard_le_ncard ?_ (Γ.finite_V.subset inter_subset_left)
    intro x hx
    have h := inter_outside_subset hx
    exact ⟨h.2, h.1⟩
  by_cases hlong : θ ≤ (Γ.V ∩ frontier D).ncard
  · exact hfree.2.1.trans hlong
  · have hshort : separationOrder (G.inter D) (G.interOutside D) < θ :=
      hord.trans_lt (Nat.lt_of_not_ge hlong)
    have hsep := isSeparation_inter (Γ := G) hD hn
    have hm := (hT.axiom1 hsep hshort).resolve_left hnot
    have hZB : Z ⊆ (G.interOutside D).vertexSet := fun x hx => ⟨hfree.1 hx, hZ hx⟩
    have hbound := hfree.2.2 hm hZB
    rw [separationOrder_comm] at hbound
    exact hbound.trans hord

end GraphMinor.GM12
