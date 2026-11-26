/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM16.ConnectedTwoBoundaries
import LeanPool.GraphMinor.GM16.AnnulusCrossing
import LeanPool.GraphMinor.GM16.AnnulusIncidentEdges
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

/-!
# Connectivity of the annular subdrawing

The two zone boundaries are circuits in the annular subdrawing.
A crossing path joins them. Every edge at a vertex on neither
boundary is retained, so connectedness of the original drawing
implies connectedness of the annular subdrawing. This supplies the
connectivity assertion in XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- An annulus between nested drawn zone boundaries is connected
when a path inside it joins the two boundary circles. -/
theorem annular_subdrawing_isGraphConnected {H J : Drawing S}
    {d : Set S → Set S → ℕ} {γ δ : ℕ} {z w I O : Set S} {a b : S}
    (hI : IsLambdaZoneAround H d γ z I) (hO : IsLambdaZoneAround H d δ w O)
    (hNest : closure I ⊆ O) (hH : IsGraphConnected H.toGraph)
    (hJ : J.IsSubdrawing (H.interSet (closure O \ I)))
    (hPath : J.IsPathBetween a b) (ha : a ∈ H.V ∩ subBd I) (hb : b ∈ H.V ∩ subBd O) :
    IsGraphConnected (H.interSet (closure O \ I)).toGraph := by
  let Q := H.interSet (closure O \ I)
  let C := H.interSet (subBd I)
  let D := H.interSet (subBd O)
  have hCU : C.U = subBd I := by
    apply subset_antisymm
    · exact interSet_U_subset (by rw [subBd_eq_frontier]; exact isClosed_frontier)
    · exact oArc_subset_interSet_U hI.isOArc_bd hI.bd_subset_U Subset.rfl
  have hDU : D.U = subBd O := by
    apply subset_antisymm
    · exact interSet_U_subset (by rw [subBd_eq_frontier]; exact isClosed_frontier)
    · exact oArc_subset_interSet_U hO.isOArc_bd hO.bd_subset_U Subset.rfl
  have hCV : C.V = H.V ∩ subBd I := by
    ext x
    exact mem_interSet_V_iff (by rw [subBd_eq_frontier]; exact isClosed_frontier)
  have hDV : D.V = H.V ∩ subBd O := by
    ext x
    exact mem_interSet_V_iff (by rw [subBd_eq_frontier]; exact isClosed_frontier)
  have hDisI := (isOpen_disjoint_subBd_and_closure_eq hI.isOpenDisc.1).1
  have hDisO := (isOpen_disjoint_subBd_and_closure_eq hO.isOpenDisc.1).1
  have hCQ : C.IsSubdrawing Q := by
    apply subdrawing_interSet_of_U_subset interSet_isSub
    rw [hCU]
    intro x hx
    exact ⟨subset_closure (hNest hx.1), fun hxi => hDisI.notMem_of_mem_left hxi hx⟩
  have hDQ : D.IsSubdrawing Q := by
    apply subdrawing_interSet_of_U_subset interSet_isSub
    rw [hDU]
    intro x hx
    exact ⟨hx.1, fun hxi => hDisO.notMem_of_mem_left (hNest (subset_closure hxi)) hx⟩
  obtain ⟨W, _, _, _⟩ := hPath
  obtain ⟨W', _, _⟩ := hJ.exists_walk_up W
  apply isGraphConnected_of_two_boundaries
    (toGraph_le_of_isSubdrawing (interSet_isSub (Γ := H))) hH
    (toGraph_le_of_isSubdrawing hCQ) (toGraph_le_of_isSubdrawing hDQ)
    (circuit_drawing_isGraphConnected (interSet_isCircuit_of_oArc hI.isOArc_bd hI.bd_subset_U))
    (circuit_drawing_isGraphConnected (interSet_isCircuit_of_oArc hO.isOArc_bd hO.bd_subset_U))
    (show a ∈ C.V from hCV.symm ▸ ha) (show b ∈ D.V from hDV.symm ▸ hb) W'
  intro e x y hl hx hnot
  apply annular_subdrawing_keeps_edges hI hO hl hx
  simpa only [show V(C.toGraph) = H.V ∩ subBd I from hCV,
    show V(D.toGraph) = H.V ∩ subBd O from hDV] using hnot

/-- The full connectivity assertion used in XVI (8.1), Claim (14),
page 74: a connected drawing restricted between two nested zone
boundaries is connected. The crossing path is derived from ambient
connectedness rather than assumed. -/
theorem annular_subdrawing_connected (hS : IsClosedSurface S) {H : Drawing S}
    {d : Set S → Set S → ℕ} {γ δ : ℕ} {z w I O : Set S}
    (hI : IsLambdaZoneAround H d γ z I) (hO : IsLambdaZoneAround H d δ w O)
    (hNest : closure I ⊆ O) (hH : IsGraphConnected H.toGraph) :
    IsGraphConnected (H.interSet (closure O \ I)).toGraph := by
  obtain ⟨a, ha, b, hb, J, hPath, hJ⟩ := exists_annular_crossing_path hS hI hO hNest hH
  exact annular_subdrawing_isGraphConnected hI hO hNest hH hJ hPath ha hb

end GraphMinor.GM16
