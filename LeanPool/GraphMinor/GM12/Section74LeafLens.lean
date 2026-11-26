/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section73ImageArc
import LeanPool.GraphMinor.GM12.Section74LensUniverses
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM11.Regions

/-!
# A slit disc around the end of a leaf edge

The leaf step in XII (7.4), pages 262--263, extends the last
part of the leaf edge by an access arc into its incident region.
A lens around the combined line puts the leaf endpoint inside
and the other end on its boundary. The closed set `Z` consists
of the drawing that remains and the earlier part of the leaf
edge. The lens misses `Z` except at its boundary end. Hence it
lies in the new region and meets the old drawing in exactly the
last part of the leaf edge, a slit with only one boundary point.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A lens around a leaf segment continued by an access arc is
a closed slit disc in the new region. The sets `L`, `B`, and `Z`
are the leaf segment, its access continuation, and the closed
remainder of the old drawing. -/
theorem exists_leaf_slit_lens
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {K : Drawing S} {G L B Z r : Set S} {w v z : S}
    (hL : IsLineWithEnds L w v) (hB : IsLineWithEnds B v z)
    (hLB : L ∩ B = {v}) (hZ : IsClosed Z) (hLZ : L ∩ Z = {w})
    (hBZ : Disjoint B Z) (hG : G ⊆ Z ∪ L) (hLG : L ⊆ G)
    (hKZ : K.U ⊆ Z) (hwK : w ∉ K.U) (hr : r ∈ K.R) (hvr : v ∈ r) :
    ∃ N : Set S, IsClosedDisc N ∧ N ⊆ r ∧ L ⊆ N ∧
      N ∩ G = L ∧ discBd N ∩ L = {w} := by
  have hExt : IsLineWithEnds (L ∪ B) w z := Surface.IsLineWithEnds.union hL hB hLB
  have hwz : w ≠ z := lineWithEnds_ends_ne hExt
  have hExtZ : (L ∪ B) ∩ Z ⊆ {w, z} := by
    intro x hx
    rcases hx.1 with hxL | hxB
    · exact Or.inl (by have hh : x ∈ L ∩ Z := ⟨hxL, hx.2⟩; rwa [hLZ] at hh)
    · exact (disjoint_left.mp hBZ hxB hx.2).elim
  obtain ⟨N, hN, hExtN, hNZ, hwbd, _, hbdExt⟩ :=
    exists_edge_lens_disc_universes hS hExt hwz hZ hExtZ
  have hzZ : z ∉ Z := disjoint_left.mp hBZ hB.right_mem
  have hNZw : N ∩ Z ⊆ {w} := by
    intro x hx
    exact (hNZ hx).resolve_right (fun hxz => hzZ (hxz ▸ hx.2))
  have hLN : L ⊆ N := subset_union_left.trans hExtN
  have hNdis : Disjoint N K.U := by
    apply disjoint_left.mpr
    intro x hxN hxK
    have hxw : x = w := hNZw ⟨hxN, hKZ hxK⟩
    exact hwK (hxw ▸ hxK)
  have hNr : N ⊆ r := subset_region hr hN.isPathConnected.isConnected.isPreconnected
    hNdis (hLN hL.right_mem) hvr
  have hNG : N ∩ G = L := by
    apply Subset.antisymm
    · intro x hx
      rcases hG hx.2 with hxZ | hxL
      · have hxw : x = w := hNZw ⟨hx.1, hxZ⟩
        exact hxw.symm ▸ hL.left_mem
      · exact hxL
    · intro x hx
      exact ⟨hLN hx, hLG hx⟩
  have hzL : z ∉ L := by
    intro hz
    have hzv : z = v := by
      have hh : z ∈ L ∩ B := ⟨hz, hB.right_mem⟩
      rw [hLB] at hh
      exact hh
    exact lineWithEnds_ends_ne hB hzv.symm
  have hbdL : discBd N ∩ L = {w} := by
    apply Subset.antisymm
    · intro x hx
      exact (hbdExt ⟨hx.1, Or.inl hx.2⟩).resolve_right (fun hxz => hzL (hxz ▸ hx.2))
    · exact singleton_subset_iff.mpr ⟨hwbd, hL.left_mem⟩
  exact ⟨N, hN, hNr, hLN, hNG, hbdL⟩

end GraphMinor.GM12
