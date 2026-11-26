/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section11
public import LeanPool.GraphMinor.GM07.AlphaExists
public import LeanPool.GraphMinor.GM07.Section5a
public import LeanPool.GraphMinor.GM07.Section5b
public import LeanPool.GraphMinor.GM11.Cited
public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM19.Conditional
import LeanPool.GraphMinor.Surface.OpenDisc
import LeanPool.GraphMinor.Surface.CutIArc
import LeanPool.GraphMinor.Surface.CutLoop
import LeanPool.GraphMinor.Surface.NormalWord
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.GM07.Section11b
import LeanPool.GraphMinor.GM07.Section11f

/-!
# Bridge Theorems for Graph Minors VII

This file connects the results of `GraphMinor/GM07/` to the cited statement definitions in
`GraphMinor/GM11/Cited.lean`, `GraphMinor/GM12/Cited.lean`, `GraphMinor/GM14/Cited.lean`, and
`GraphMinor/GM19/Conditional.lean`:
- `gm07_theorem_4_2`: proves `GM14.GM07Theorem42Statement` from `Surface.open_disc` with
  no hypotheses (using `isClosedSurface_of_bd_eq_empty` and
  `subBd_eq_discBd_of_bd_eq_empty` from `Section11.lean`).
- `gm07_theorem_5_1`: proves `GM12.GM07Theorem51Statement` from `theorem_5_1`.
- `gm07_theorem_5_2`: proves `GM12.GM07Theorem52Statement` from `theorem_5_2`.
- `gm07_theorem_5_5`: proves `GM12.GM07Theorem55Statement` from `theorem_5_5`.
- `gm07_theorem_11_2`: proves `GM11.GM07Theorem112Statement` from `theorem_11_2`.
- `gm07_theorem_11_9`: proves `GM14.GM07Theorem119Statement` from `gm07_theorem_11_9_closed`.
- `gm07_theorem_11_10`: proves `GM11.GM07Theorem1110Statement` from `theorem_11_10`.
- `gm07_planar_iff`: proves `GM19.GM07PlanarIffStatement` from `theorem_5_1`.
- `gm07_alpha_exists`: proves `GM19.GM07AlphaExistsStatement` from `gm07_alpha_exists_core`.
- `gm07_theorem_11_9_closed` and `gm07_theorem_11_9_subset`: prove the closed-surface (`bd S = ∅`,
  for `GM14.IsArcSimplyConnected`) and general-surface (`IsSimplyConnectedSubset`) forms of
  Graph Minors VII, (11.9).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe u

/-- Unconditional proof of `GM14.GM07Theorem42Statement` (Graph Minors VII, (4.2), page 222) from
`Surface.open_disc`. Because `bd S = ∅`, `S` is a closed surface
(`isClosedSurface_of_bd_eq_empty`) and `subBd Δ = discBd Δ` for every closed disc `Δ ⊆ S`
(`subBd_eq_discBd_of_bd_eq_empty`). -/
theorem gm07_theorem_4_2 :
    GM07Theorem42Statement.{u} := by
  intro S _ _ hS hconn hbd Y hY_conn hY_open hY_oarc
  have hS_closed : IsClosedSurface S := isClosedSurface_of_bd_eq_empty hS hbd
  refine Surface.open_disc S Y hS_closed hconn hY_conn hY_open fun F hFY hF => ?_
  obtain ⟨Δ, hΔ, hsub, hΔY⟩ := hY_oarc F hF hFY
  rw [subBd_eq_discBd_of_bd_eq_empty hS hbd hΔ] at hsub
  exact ⟨Δ, hΔY, hΔ, hsub⟩

/-- Unconditional proof of `GM12.GM07Theorem51Statement` (Graph Minors VII, (5.1), page 230). -/
theorem gm07_theorem_5_1 :
    GM07Theorem51Statement.{u} := by
  intro S _ hS hconn X hX_solid hX_ne
  exact @theorem_5_1_proof S _ hS hconn X hX_solid hX_ne

/-- Unconditional proof of `GM12.GM07Theorem52Statement` (Graph Minors VII, (5.2), page 230). -/
theorem gm07_theorem_5_2 :
    GM07Theorem52Statement.{u} := by
  intro S _ hS C X _ hX_solid hXC
  exact @theorem_5_2_proof S _ hS X C hX_solid hXC

/-- Unconditional proof of `GM12.GM07Theorem55Statement` (Graph Minors VII, (5.5), page 231). -/
theorem gm07_theorem_5_5 :
    GM07Theorem55Statement.{u} := by
  intro S _ hS hconn G hG R hR hZ_ne
  rw [@theorem_5_5_proof S _ hS hconn G hG R hR (closure (⋃₀ R)) rfl hZ_ne]
  constructor
  · intro h F hF_norm hF_oarc hF_sub
    exact h F hF_sub hF_norm hF_oarc
  · intro h F hF_sub hF_norm hF_oarc
    exact h F hF_norm hF_oarc hF_sub

/-- Unconditional proof of `GM11.GM07Theorem112Statement` (Graph Minors VII, (11.2), page 249). -/
theorem gm07_theorem_11_2 :
    GM07Theorem112Statement.{u} := by
  intro S _ hS φ hφ
  exact theorem_11_2_proof hS φ hφ

/-- Proof of `GM11.GM07Theorem1110Statement` (Graph Minors VII, (11.10), page 253). -/
theorem gm07_theorem_11_10 :
    GM07Theorem1110Statement.{u} := by
  intro S _ _ hS hconn Z hZ_solid hZ_flat
  exact @theorem_11_10_proof S _ hS hconn Z hZ_solid hZ_flat

/-- Unconditional proof of `GM19.GM07PlanarIffStatement` (Graph Minors VII, (5.1), page 230). -/
theorem gm07_planar_iff :
    GM19.GM07PlanarIffStatement.{u} := by
  intro S _ _ hS hconn X hX_solid hX_ne
  exact @theorem_5_1_proof S _ hS hconn X hX_solid hX_ne

/-- Unconditional proof of `GM19.GM07AlphaExistsStatement` (Graph Minors VII, Section 5, page 230).
-/
theorem gm07_alpha_exists :
    GM19.GM07AlphaExistsStatement.{u} :=
  gm07_alpha_exists_core

/-- Proof of Graph Minors VII, (11.9) (page 253) for closed surfaces (`bd S = ∅`, the setting of
Graph Minors XIV), yielding `GM14.IsArcSimplyConnected Y`. -/
theorem gm07_theorem_11_9_closed :
    ∀ (S : Type u) [TopologicalSpace S],
      IsSurface S → ConnectedSpace S → bd S = ∅ →
      ∀ Z : Set S, IsFlat Z → IsLocallyArcConnected Z →
        (IsClosed Z ∨ IsArcConnected Z) →
        ∃ Y : Set S, IsOpen Y ∧ IsArcSimplyConnected Y ∧ Z ⊆ Y := by
  intro S _ hS hconn hbd Z hZ_flat hZ_lac hZ_cl_or_arc
  obtain ⟨Y, hZY, hY_open, hY_asc, _⟩ :=
    @theorem_11_9_closed S _ hS hbd hconn Z
      hZ_flat hZ_lac hZ_cl_or_arc
  exact ⟨Y, hY_open, hY_asc, hZY⟩

/-- Closed-surface case of VII (11.9), with the general form in `gm07_theorem_11_9_subset`. -/
theorem gm07_theorem_11_9 :
    GM07Theorem119Statement.{u} := by
  intro S _ _ hS hconn hbd Z hZ_flat hZ_lac hZ_cl_or_arc
  exact gm07_theorem_11_9_closed S hS hconn hbd Z hZ_flat hZ_lac hZ_cl_or_arc

/-- Proof of Graph Minors VII, (11.9) (page 253) for all surfaces (with possibly nonempty boundary),
using `IsSimplyConnectedSubset Y` (`discBd Δ = F`). -/
theorem gm07_theorem_11_9_subset :
    ∀ (S : Type u) [TopologicalSpace S],
      IsSurface S → ConnectedSpace S →
      ∀ Z : Set S, IsFlat Z → IsLocallyArcConnected Z →
        (IsClosed Z ∨ IsArcConnected Z) →
        ∃ Y : Set S, IsOpen Y ∧ IsSimplyConnectedSubset Y ∧ Z ⊆ Y := by
  intro S _ hS hconn Z hZ_flat hZ_lac hZ_cl_or_arc
  obtain ⟨Y, hZY, hY_open, hY_sc, _⟩ :=
    @theorem_11_9_proof S _ hS hconn Z hZ_flat hZ_lac hZ_cl_or_arc
  exact ⟨Y, hY_open, hY_sc, hZY⟩

end GraphMinor.GM07
