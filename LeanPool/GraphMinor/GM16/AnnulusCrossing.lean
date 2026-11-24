/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM16.AnnularPathTrim
import LeanPool.GraphMinor.GM16.ZoneBoundaryLinkage
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

/-!
# A crossing path between two nested zone boundaries

Connectedness gives a path between the two boundary circuits.
First trim it into the outer closed zone, then at its last visit to
the inner circuit. The remaining path lies in the annulus and joins
its boundary circles. This completes the setup for the connectivity
argument of XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
  GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- A connected drawing has a crossing path in the annulus between
two nested drawn zone boundaries. -/
theorem exists_annular_crossing_path (hS : IsClosedSurface S) {H : Drawing S}
    {d : Set S → Set S → ℕ} {γ δ : ℕ} {z w I O : Set S}
    (hI : IsLambdaZoneAround H d γ z I) (hO : IsLambdaZoneAround H d δ w O)
    (hNest : closure I ⊆ O) (hH : IsGraphConnected H.toGraph) :
    ∃ a ∈ H.V ∩ subBd I, ∃ b ∈ H.V ∩ subBd O, ∃ J : Drawing S,
      J.IsPathBetween a b ∧ J.IsSubdrawing (H.interSet (closure O \ I)) := by
  classical
  let C := H.interSet (subBd I)
  let D := H.interSet (subBd O)
  have hC := interSet_isCircuit_of_oArc hI.isOArc_bd hI.bd_subset_U
  have hD := interSet_isCircuit_of_oArc hO.isOArc_bd hO.bd_subset_U
  have hCV : C.V = H.V ∩ subBd I := by
    ext x
    exact mem_interSet_V_iff (by rw [subBd_eq_frontier]; exact isClosed_frontier)
  have hDV : D.V = H.V ∩ subBd O := by
    ext x
    exact mem_interSet_V_iff (by rw [subBd_eq_frontier]; exact isClosed_frontier)
  obtain ⟨a, W₁, _, _, haV, _⟩ := hC
  obtain ⟨b, W₂, _, _, hbV, _⟩ := hD
  have ha : a ∈ H.V ∩ subBd I := hCV ▸ (haV.symm ▸ W₁.start_mem_support)
  have hb : b ∈ H.V ∩ subBd O := hDV ▸ (hbV.symm ▸ W₂.start_mem_support)
  obtain ⟨W⟩ := hH.2 a ha.1 b hb.1
  obtain ⟨P, hP, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
  obtain ⟨L, hLPath, hLH, _⟩ := exists_drawing_of_graphPath hP
  have hA : H.V ∩ subBd I ⊆ O := fun _ hx => hNest hx.2.1
  obtain ⟨Q, hQ, _⟩ := linkage_inside_closed_zone hO hA (fun _ : Fin 1 => L)
    (fun _ => ⟨a, ha, b, hb, hLPath, hLH⟩)
    (fun i j hij => False.elim (hij (Subsingleton.elim i j)))
  obtain ⟨b', a', hR⟩ := hQ 0
  have hb' : b' ∈ H.V ∩ subBd O := by
    have hmem := hR.1.left_mem
    exact (hR.2.1 ▸ (show b' ∈ ({b'} : Set S) from rfl)).2
  have ha' : a' ∈ H.V ∩ subBd I :=
    (hR.2.2 ▸ (show a' ∈ ({a'} : Set S) from rfl)).2
  obtain ⟨R, hRPath, hRSub, _⟩ := exists_drawing_of_graphPath hR.1.symm
  have hCU : C.U = subBd I := by
    apply subset_antisymm
    · exact interSet_U_subset (by rw [subBd_eq_frontier]; exact isClosed_frontier)
    · exact oArc_subset_interSet_U hI.isOArc_bd hI.bd_subset_U Subset.rfl
  have hfr : frontier (closure I) = subBd I := by
    rw [← subBd_eq_frontier]
    exact subBd_closure_eq_subBd_of_isOpenDisc hS hI.isOpenDisc hI.isOArc_bd hI.isClosedDisc_closure
  have hInt : interior (closure I) = I := by
    rw [← self_sdiff_frontier, hfr, subBd_eq_frontier, closure_sdiff_frontier,
      hI.isOpenDisc.1.interior_eq]
  have hbOut : b' ∉ closure I := fun h =>
    ((isOpen_disjoint_subBd_and_closure_eq hO.isOpenDisc.1).1).notMem_of_mem_left (hNest h) hb'.2
  have hRInside : R.U ⊆ closure O := fun _ hx => interSet_U_subset isClosed_closure
    (hRSub.U_subset hx)
  obtain ⟨c, hc, J, hJPath, hJR, hJU, _, _⟩ := exists_annular_terminal_path
    (interSet_isSub (Γ := H)) (hRSub.trans interSet_isSub) hRPath (hCV.symm ▸ ha')
    isClosed_closure (hfr.trans hCU.symm) hbOut hRInside
  refine ⟨c, hCV ▸ hc, b', hb', J, drawingPath_symm hJPath, ?_⟩
  apply subdrawing_interSet_of_U_subset (hJR.trans (hRSub.trans interSet_isSub))
  rwa [hInt] at hJU

end GraphMinor.GM16
