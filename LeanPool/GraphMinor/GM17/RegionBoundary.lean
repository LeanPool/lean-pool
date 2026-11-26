/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.BorderNode
public import LeanPool.GraphMinor.GM17.Section8

/-!
# The boundary of regions of a tame painting

This file proves `RegionBoundaryOArcCriterionStatement`, the surface work of (8.2), (8.4), (8.6),
(8.7) and (8.8) of Graph Minors XVII (pages 181 to 183). The parts are proved in
`GraphMinor.GM17.RegionCycle`, `GraphMinor.GM17.CellNodes`, `GraphMinor.GM17.BorderArc`,
`GraphMinor.GM17.BorderCells`, `GraphMinor.GM17.NodeRing` and
`GraphMinor.GM17.BorderNode`.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

/-- **Graph Minors XVII, (8.2), and the pushing off of cells in (8.4), (8.6), (8.7) and (8.8)**
(pages 181 to 183). -/
theorem regionBoundaryOArcCriterion : RegionBoundaryOArcCriterionStatement := by
  unfold RegionBoundaryOArcCriterionStatement
  intro S _ _ hS Γ h6 hreg hO
  have ht2 : T2Space S := hS.2.1
  have hΓ : Γ.Tame := ⟨h6, hreg, hO⟩
  refine ⟨fun r hr => Painting.frontier_isOArc hS hΓ hr, fun c hc => ?_,
    fun n hn => Painting.node_on_cell hS hΓ hn, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, hne⟩ := Painting.two_nodes hS hΓ hc
    exact (Set.one_lt_ncard_iff (Γ.finite_tilde_cell hc)).mpr ⟨a, b, ha, hb, hne⟩
  · exact fun n hn hall => Painting.border_node hS hΓ hn.1 hall
  · exact fun c hc hint => ⟨fun n₁ h₁ n₂ h₂ hne => Painting.internal_arc hS hΓ hc hint h₁ h₂ hne,
      fun ht => Painting.internal_bd_arc hS hΓ hc hint ht⟩
  · exact fun c₁ h₁ c₂ h₂ hne hb₁ hb₂ he => Painting.two_border hS hΓ h₁ h₂ hne hb₁ hb₂ he
  · rintro n ⟨hn, hnb⟩ (h | ⟨h, c₀, h₀, hnc, h2⟩)
    · exact Painting.node_one hS hΓ hn hnb h
    · exact Painting.node_two hS hΓ hn hnb h h₀ hnc h2

end GraphMinor.GM17
