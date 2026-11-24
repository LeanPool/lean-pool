/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import Mathlib.Topology.Connected.Basic

/-!
# Components after removing the common ends of two arcs

In Case 2 of XII (2.1), page 244, a chord cuts a circle into two arcs.
The two open arcs are precisely the components of the circle minus the
chord ends. The general lemma here treats two closed sets whose
intersection is removed: each remaining connected piece is a whole
component of their union.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

private theorem component_eq_closed_piece {S : Type*} [TopologicalSpace S]
    {A B F : Set S} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∩ B ⊆ F)
    (hconn : IsPreconnected (A \ F)) {x : S} (hx : x ∈ A \ F) :
    connectedComponentIn ((A ∪ B) \ F) x = A \ F := by
  let T := (A ∪ B) \ F
  have hxT : x ∈ T := ⟨Or.inl hx.1, hx.2⟩
  have hsub : A \ F ⊆ T := fun _ h => ⟨Or.inl h.1, h.2⟩
  apply Subset.antisymm
  · intro y hy
    have hyT := connectedComponentIn_subset T x hy
    refine ⟨?_, hyT.2⟩
    by_contra hyA
    have hyB := hyT.1.resolve_left hyA
    obtain ⟨z, hzC, hzA, hzB⟩ := isPreconnected_closed_iff.mp
      isPreconnected_connectedComponentIn A B hA hB
      (fun z hz => (connectedComponentIn_subset T x hz).1)
      ⟨x, mem_connectedComponentIn hxT, hx.1⟩ ⟨y, hy, hyB⟩
    exact (connectedComponentIn_subset T x hzC).2 (hAB ⟨hzA, hzB⟩)
  · exact hconn.subset_connectedComponentIn hx hsub

/-- If two closed sets meet only in the removed set, their nonempty
preconnected remainders are exactly the components of the punctured
union. Applied to two arcs and their ends, this identifies the two
boundary pieces in the disc-cutting step of XII (2.1), Case 2. -/
theorem componentsIn_union_sdiff {S : Type*} [TopologicalSpace S]
    {A B F : Set S} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∩ B ⊆ F)
    (hAc : IsPreconnected (A \ F)) (hBc : IsPreconnected (B \ F))
    (hAne : (A \ F).Nonempty) (hBne : (B \ F).Nonempty) :
    componentsIn ((A ∪ B) \ F) = {A \ F, B \ F} := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx.1 with hxA | hxB
    · exact Or.inl (component_eq_closed_piece hA hB hAB hAc ⟨hxA, hx.2⟩)
    · right
      have heq : connectedComponentIn ((A ∪ B) \ F) x = B \ F := by
        rw [union_comm]
        exact component_eq_closed_piece hB hA (fun _ hz => hAB ⟨hz.2, hz.1⟩) hBc ⟨hxB, hx.2⟩
      exact mem_singleton_iff.mpr heq
  · rintro (rfl | hC)
    · obtain ⟨x, hx⟩ := hAne
      exact ⟨x, ⟨Or.inl hx.1, hx.2⟩,
        component_eq_closed_piece hA hB hAB hAc hx⟩
    · obtain rfl := mem_singleton_iff.mp hC
      obtain ⟨x, hx⟩ := hBne
      refine ⟨x, ⟨Or.inr hx.1, hx.2⟩, ?_⟩
      rw [union_comm]
      exact component_eq_closed_piece hB hA (fun _ hz => hAB ⟨hz.2, hz.1⟩) hBc hx

end GraphMinor.GM12
