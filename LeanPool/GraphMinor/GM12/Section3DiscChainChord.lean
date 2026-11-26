/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DiscChainCarrier
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM06.RegionLocal

/-!
# A proper normal chord from a disc chain

For the VI (3.6) application in XII (3.2), pages 247--248,
extract an arc from a path in the chain carrier. The carrier meets
the disc boundary only at the two endpoints, so the arc is proper.
Its drawing vertices are among the vertex terms of the chain.
Repeated terms only increase chain length, giving the required
vertex-count bound.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM06

universe u

/-- A VI chain between distinct boundary points supplies the proper
normal line used in the one-disc case of XII (3.2), with no more
drawing vertices than the length of the chain. -/
theorem exists_normal_chord_of_disc_chain
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    {A : List (ChainTerm S)} (hDisc : IsClosedDiscSpace S) (hProper : G.IsProper)
    (hA : IsXYChain G x y A) (hxy : x ≠ y) (hxB : x ∈ bd S) (hyB : y ∈ bd S) :
    ∃ L : Set S, IsLineWithEnds L x y ∧ G.IsNormal L ∧ L ∩ bd S = {x, y} ∧
      (G.V ∩ L).ncard ≤ chainLength A := by
  let : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  obtain ⟨F, _, hF, hxF, hyF, hFU, hFB⟩ :=
    exists_path_connected_carrier_of_disc_chain hDisc hProper hA
  obtain ⟨p, hp⟩ := hF.joinedIn x hxF y hyF
  obtain ⟨g, hg, hgi, hg0, hg1, hgr⟩ := exists_arc_of_path p.continuous (by
    rw [p.source, p.target]
    exact hxy)
  have hgF : range g ⊆ F := by
    intro z hz
    obtain ⟨t, rfl⟩ := hgr hz
    exact hp t
  have hg0' : g 0 = x := hg0.trans p.source
  have hg1' : g 1 = y := hg1.trans p.target
  have hL : IsLineWithEnds (range g) x y := by
    simpa only [hg0', hg1'] using (IsArcMap.isLineWithEnds ⟨hg, hgi⟩)
  have hn : G.IsNormal (range g) := fun z hz => (hFU ⟨hgF hz.1, hz.2⟩).1
  have hcap : range g ∩ bd S = {x, y} := by
    apply Subset.antisymm
    · exact fun z hz => hFB ⟨hgF hz.1, hz.2⟩
    · intro z hz
      rcases hz with rfl | rfl
      · exact ⟨⟨0, hg0'⟩, hxB⟩
      · exact ⟨⟨1, hg1'⟩, hyB⟩
  have hcount : (G.V ∩ range g).ncard ≤ chainLength A := by
    apply (Set.ncard_le_ncard (t := {v : S | Sum.inl v ∈ A}) ?_ (finite_inl_mem A)).trans
      (ncard_inl_mem_le_chainLength A)
    intro z hz
    exact (hFU ⟨hgF hz.2, G.V_subset_U hz.1⟩).2
  exact ⟨range g, hL, hn, hcap, hcount⟩

end GraphMinor.GM12
