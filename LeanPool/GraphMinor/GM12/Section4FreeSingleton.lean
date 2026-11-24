/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section4PathExists
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# A single drawing vertex is free

XII (4.4), page 251, uses that each singleton boundary vertex set
is free because the drawing is connected. If a separation of order
zero has a vertex on its small side, every incident edge stays on
that side. Propagate along walks in the connected drawing. All
vertices would lie on the small side, contrary to the third tangle
axiom.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM14 Hypergraph

/-- The singleton freeness assertion in XII (4.4), page 251. -/
theorem isFreeSet_singleton_of_respectful_drawing
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle Γ θ T) {v : S} (hv : v ∈ Γ.V) :
    IsFreeSet Γ.toHypergraph T θ {v} := by
  refine ⟨singleton_subset_iff.mpr hv, ?_, ?_⟩
  · simpa only [ncard_singleton] using hT.2.1.one_le
  · intro A B hmem hsub
    rw [ncard_singleton]
    by_contra hbound
    have hzero : separationOrder A B = 0 := Nat.eq_zero_of_not_pos hbound
    have hsep := hT.2.1.isSeparation hmem
    have hempty : (A ∩ B).vertexSet = ∅ :=
      (Set.ncard_eq_zero (A ∩ B).vertexSet_finite).mp hzero
    have hnotboth : ∀ x, x ∈ A.vertexSet → x ∈ B.vertexSet → False := by
      intro x hxA hxB
      have hx : x ∈ (A ∩ B).vertexSet := ⟨hxA, hxB⟩
      rw [hempty] at hx
      exact hx.elim
    have hwalk : ∀ {x y : S}, GraphWalk Γ.toGraph x y → x ∈ A.vertexSet → y ∈ A.vertexSet := by
      intro x y W
      induction W with
      | nil => exact id
      | @cons x y z e hl W ih =>
        intro hxA
        have hxInc : Γ.toHypergraph.Inc e x :=
          ⟨hl.1, hl.2.1, ((hl.2.2.2).symm.subset (Or.inl rfl)).1⟩
        have hyInc : Γ.toHypergraph.Inc e y :=
          ⟨hl.1, hl.2.2.1, ((hl.2.2.2).symm.subset (Or.inr rfl)).1⟩
        have heAB : e ∈ A.edgeSet ∪ B.edgeSet := by rw [hsep.edgeSet_union]; exact hl.1
        apply ih
        rcases heAB with heA | heB
        · exact A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).mpr hyInc)
        · exact False.elim (hnotboth x hxA
            (B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).mpr hxInc)))
    have hVA : Γ.V ⊆ A.vertexSet := by
      intro x hx
      obtain ⟨W⟩ := exists_walk_of_open_disc_regions hS hT.1.2 hv hx
      exact hwalk W (hsub (mem_singleton v))
    exact hT.2.1.axiom3 hmem (hsep.left_le.vertexSet_subset.antisymm hVA)

end GraphMinor.GM12
