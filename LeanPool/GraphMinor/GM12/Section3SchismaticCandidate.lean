/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM12.Section3SolidUnion
import LeanPool.GraphMinor.GM12.Section3FiniteGraphSolid
import LeanPool.GraphMinor.Surface.SurfaceGraph
import Mathlib.Analysis.Convex.Contractible

/-!
# Schismatic sets are alpha candidates

The alternative minimum in VII Section 8, page 241, used by XII
(3.1), page 245, goes in both directions. Extraction gives the lower
bound. For the other direction, every schismatic shape is solid and
connected. Its constituent lines and circles are solid, finite unions
preserve solidity, and the specified attachments give connectedness.
Thus a normal schismatic set is itself an alpha candidate.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem connected_line
    {S : Type*} [TopologicalSpace S] {L : Set S} (hL : IsLine L) : IsConnected L := by
  obtain ⟨e⟩ := hL
  let : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : PathConnectedSpace L := e.pathConnectedSpace
  exact (isPathConnected_iff_pathConnectedSpace.mpr inferInstance).isConnected

private theorem connected_circle
    {S : Type*} [TopologicalSpace S] {F : Set S} (hF : IsOArc F) : IsConnected F := by
  obtain ⟨e⟩ := hF
  let : PathConnectedSpace F := e.pathConnectedSpace
  exact (isPathConnected_iff_pathConnectedSpace.mpr inferInstance).isConnected

/-- Every schismatic shape is solid and connected, as required for the
alternative definition of alpha in VII Section 8, page 241. -/
theorem solid_connected_of_schismatic
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    {X : Set S} (hX : GM07.IsSchismatic X) : IsSolid X ∧ IsConnected X := by
  rcases hX.1 with hF | h1 | h2 | h3
  · exact ⟨isSolid_oArc hF, connected_circle hF⟩
  · obtain ⟨A, B, P, u, v, hA, hB, _, hP, hu, hv, _, _, rfl⟩ := h1
    have hL : IsLine P := ⟨hP.choose⟩
    have hAP := (connected_circle hA).union ⟨u, hu, hP.left_mem⟩ (connected_line hL)
    have hAPB := hAP.union ⟨v, Or.inr hP.right_mem, hv⟩ (connected_circle hB)
    rw [union_right_comm] at hAPB
    exact ⟨isSolid_union (isSolid_union (isSolid_oArc hA) (isSolid_oArc hB)) (isSolid_line hL),
      hAPB⟩
  · obtain ⟨A, B, u, hA, hB, hcap, rfl⟩ := h2
    have hu : u ∈ A ∩ B := hcap.symm ▸ mem_singleton u
    exact ⟨isSolid_union (isSolid_oArc hA) (isSolid_oArc hB),
      (connected_circle hA).union ⟨u, hu⟩ (connected_circle hB)⟩
  · obtain ⟨P, Q, R, u, v, _, hP, hQ, hR, _, _, _, rfl⟩ := h3
    have hPL : IsLine P := ⟨hP.choose⟩
    have hQL : IsLine Q := ⟨hQ.choose⟩
    have hRL : IsLine R := ⟨hR.choose⟩
    have hPQ := (connected_line hPL).union ⟨u, hP.left_mem, hQ.left_mem⟩ (connected_line hQL)
    exact ⟨isSolid_union (isSolid_union (isSolid_line hPL) (isSolid_line hQL)) (isSolid_line hRL),
      hPQ.union ⟨u, Or.inl hP.left_mem, hR.left_mem⟩ (connected_line hRL)⟩

/-- A normal schismatic set is an alpha candidate, not merely a subset
of one. This is one direction of VII Section 8's alternative minimum. -/
theorem alphaCandidate_of_normal_schismatic
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    {G : Drawing S} {X : Set S} (hX : GM07.IsSchismatic X) (hn : G.IsNormal X) :
    GM07.IsAlphaCandidate G X := by
  obtain ⟨hs, hc⟩ := solid_connected_of_schismatic hX
  exact ⟨hs, hc, hn, hX.2.1⟩

/-- Each normal schismatic vertex count bounds alpha above, as used
in the alternative minimum of VII Section 8, page 241. -/
theorem alpha_le_normal_schismatic_count
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    {G : Drawing S} {X : Set S} (hX : GM07.IsSchismatic X) (hn : G.IsNormal X) :
    GM07.alpha G ≤ (X ∩ G.V).ncard := by
  exact Nat.sInf_le ⟨X, alphaCandidate_of_normal_schismatic hX hn, rfl⟩

end GraphMinor.GM12
