/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary
public import LeanPool.ApollonianSuperharmonic.P3963T1ExteriorMixedCycleObstruction
public import LeanPool.ApollonianSuperharmonic.P3963T1MixedBoundaryCycle

-- [TABLET NODE: P3963T1EdgeFreeDiskCorners]

/-!
# P3963T1EdgeFreeDiskCorners

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3963T1EdgeFreeDiskCorners (U V : ProtoTile)
    (hU : LatticeTile U) (hV : LatticeTile V)
    (hdisjoint : Disjoint U.cells V.cells)
    (hedge : ¬ (FootprintEdges U ∩ FootprintEdges V).Nonempty)
    (houtside : FourNeighborConnected
      ((↑(U.cells ∪ V.cells) : Set LatticeCell)ᶜ)) :
    (FootprintVertices U ∩ FootprintVertices V).Subsingleton := by
-- BODY
  classical
  have hgU := LatticeTileGridStructure U hU
  have hgV := LatticeTileGridStructure V hV
  have rawIncident (T : ProtoTile) (hne : T.cells.Nonempty)
      (x : GaussianInt) (hx : x ∈ FootprintVertices T) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells := by
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hx
    obtain ⟨c, hc, h | h | h | h⟩ := hx
    · exact ⟨0, by simpa [LatticeVertexIncidentCell, h] using hc⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell, h] using hc⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell, h] using hc⟩
    · exact ⟨2, by simpa [LatticeVertexIncidentCell, h, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hc⟩
  have hrawBoundary : FootprintVertices U ∩ FootprintVertices V ⊆
      BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V := by
    rintro x ⟨hxU, hxV⟩
    obtain ⟨jU, hjU⟩ := rawIncident U hgU.1.1 x hxU
    obtain ⟨jV, hjV⟩ := rawIncident V hgV.1.1 x hxV
    exact ⟨P3161T2IncidentBoundary U x ⟨jU, hjU⟩
        ⟨jV, fun h => Finset.disjoint_left.mp hdisjoint h hjV⟩,
      P3161T2IncidentBoundary V x ⟨jV, hjV⟩
        ⟨jU, fun h => Finset.disjoint_left.mp hdisjoint hjU h⟩⟩
  have boundaryFootprint (T : ProtoTile) :
      BoundaryFootprintEdges T ⊆ FootprintEdges T := by
    rintro e ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩
    · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        congr 1 <;> simp [Zsqrtd.ext_iff]
    · rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        congr 1 <;> simp []
  have hboundaryDisjoint :
      Disjoint (BoundaryFootprintEdges U) (BoundaryFootprintEdges V) := by
    apply Set.disjoint_left.mpr
    intro e heU heV
    exact hedge ⟨e, boundaryFootprint U heU, boundaryFootprint V heV⟩
  by_contra hmultiple
  have hboundaryMultiple :
      ¬ (BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V).Subsingleton := by
    intro h
    apply hmultiple
    intro x hx y hy
    exact h (hrawBoundary hx) (hrawBoundary hy)
  obtain ⟨W, F, x, e, f, hcycle, hsubset, hxe, hxf, he, hf⟩ :=
    P3963T1MixedBoundaryCycle _ _ _ _ hgU.2.2 hgV.2.2
      hboundaryDisjoint hboundaryMultiple
  apply P3963T1ExteriorMixedCycleObstruction U V hdisjoint hedge houtside
    W F hcycle _ x e f hxe hxf
    ⟨he.1, boundaryFootprint U he.2⟩ ⟨hf.1, boundaryFootprint V hf.2⟩
  intro g hg
  rcases hsubset hg with hgU | hgV
  · exact Or.inl (boundaryFootprint U hgU)
  · exact Or.inr (boundaryFootprint V hgV)

end ApollonianSuperharmonic

end
