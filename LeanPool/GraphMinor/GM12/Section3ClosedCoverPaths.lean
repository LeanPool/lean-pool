/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Separation.Regular

/-!
# Joining representatives through a finite closed cover

The normal-connection construction in the existence argument for the
minimum used by XII (3.1), page 245, uses closures of drawing regions.
A finite closed cover of a connected space has connected intersection
data: splitting its members into reachable and unreachable classes
would give two disjoint closed sets covering the space. If meeting
cover members have their representatives joined in a prescribed set,
all representatives are joined in that set.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Paths between representatives of intersecting members of a finite
closed cover extend to paths between every pair of representatives. -/
theorem joinedIn_of_finite_closed_cover
    {S ι : Type*} [TopologicalSpace S] [ConnectedSpace S] [Finite ι]
    {N : Set S} (C : ι → Set S) (z : ι → S)
    (hC : ∀ i, IsClosed (C i)) (hne : ∀ i, (C i).Nonempty)
    (hcover : (⋃ i, C i) = univ) (hz : ∀ i, z i ∈ N)
    (hjoin : ∀ i j, (C i ∩ C j).Nonempty → JoinedIn N (z i) (z j)) :
    ∀ i j, JoinedIn N (z i) (z j) := by
  classical
  intro i j
  by_contra hn
  let A := {k | JoinedIn N (z i) (z k)}
  let X := ⋃ k ∈ A, C k
  let Y := ⋃ k ∈ Aᶜ, C k
  have hX : IsClosed X := (Set.toFinite A).isClosed_biUnion (fun k _ => hC k)
  have hY : IsClosed Y := (Set.toFinite Aᶜ).isClosed_biUnion (fun k _ => hC k)
  have hcov : (univ : Set S) ⊆ X ∪ Y := by
    intro x _
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    by_cases hkA : k ∈ A
    · exact Or.inl (mem_iUnion₂.mpr ⟨k, hkA, hk⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨k, hkA, hk⟩)
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨y, hy⟩ := hne j
  have hxX : x ∈ X := mem_iUnion₂.mpr ⟨i, JoinedIn.refl (hz i), hx⟩
  have hyY : y ∈ Y := mem_iUnion₂.mpr ⟨j, hn, hy⟩
  obtain ⟨w, _, hwX, hwY⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_univ : IsPreconnected (univ : Set S)) X Y hX hY hcov
    ⟨x, mem_univ x, hxX⟩ ⟨y, mem_univ y, hyY⟩
  obtain ⟨k, hkA, hwk⟩ := mem_iUnion₂.mp hwX
  obtain ⟨l, hlA, hwl⟩ := mem_iUnion₂.mp hwY
  exact hlA (hkA.trans (hjoin k l ⟨w, hwk, hwl⟩))

end GraphMinor.GM12
