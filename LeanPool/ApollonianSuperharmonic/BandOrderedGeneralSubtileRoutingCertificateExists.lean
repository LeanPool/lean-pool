/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileRoutingCertificate
public import LeanPool.ApollonianSuperharmonic.CoveredInterfaceOppositeIncidentCells
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathVertexIncidentEdge
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: BandOrderedGeneralSubtileRoutingCertificateExists]

/-!
# BandOrderedGeneralSubtileRoutingCertificateExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralSubtileRoutingCertificateExists
    {C₀ Cᵢ : BandCircle} {q : Fin 4 → CircleCoordinates}
    {i : Fin 3} {T₀ Tᵢ : ProtoTile}
    {h₀ hᵢ : PartialOdometer} {x : GaussianInt}
    {normalization : BandOrderedGeneralSubtileNormalizationCertificate
      C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x}
    (interface : BandOrderedGeneralSubtileInterfaceCertificate normalization) :
    Nonempty (BandOrderedGeneralSubtileRoutingCertificate interface) := by
-- BODY
  classical
  have hedge : ∃ edge : Finset GaussianInt,
      normalization.normalizedPoint ∈ edge ∧
        edge ∈ FootprintEdges normalization.normalizedRoot ∩
          FootprintEdges normalization.normalizedFixed := by
    rcases interface.startData.pathAB with
      ⟨p, hp, hlen, _, _, hvertices, hsteps, hedges⟩
    exact SimpleGridPathVertexIncidentEdge _ _
      ⟨p, hp, hlen, hvertices, hsteps, hedges⟩
      normalization.normalizedPoint interface.normalized_point_on_start_path
  have hrootBand : BandPrototile normalization.normalizedCircle.1.1
      normalization.normalizedRoot := by
    rw [← normalization.normalized_circle_eq]
    exact normalization.root_band
  have hfixedBand : BandPrototile normalization.normalizedFixedCircle.1.1
      normalization.normalizedFixed :=
    TileOdometerBandPrototile _ _ _ normalization.normalized_fixed_odometer
  have hrootRegular := LatticeEdgeRegularity normalization.normalizedCircle
    normalization.normalizedRoot hrootBand interface.root_lattice
  have hfixedRegular := LatticeEdgeRegularity normalization.normalizedFixedCircle
    normalization.normalizedFixed hfixedBand interface.fixed_lattice
  have hstart : interface.startData.point ∈
      FootprintVertices normalization.normalizedRoot ∩
        FootprintVertices normalization.normalizedFixed ∩
          FootprintVertices interface.startCompanion :=
    (interface.startData.unique_common interface.startData.point).2 rfl
  have hend : interface.startData.otherAB ∈
      FootprintVertices normalization.normalizedRoot ∩
        FootprintVertices normalization.normalizedFixed ∩
          FootprintVertices interface.endCompanion := by
    rw [← interface.interface_endpoints.1]
    exact (interface.endData.unique_common interface.endData.point).2 rfl
  obtain ⟨direction, hrootCell, hfixedCell⟩ := CoveredInterfaceOppositeIncidentCells
    normalization.normalizedRoot normalization.normalizedFixed
    interface.startCompanion interface.endCompanion
    interface.startData.point interface.startData.otherAB
    normalization.normalizedPoint interface.root_lattice interface.fixed_lattice
    interface.start_lattice interface.end_lattice interface.root_fixed_disjoint
    interface.root_start_disjoint interface.fixed_start_disjoint
    interface.root_end_disjoint interface.fixed_end_disjoint
    interface.startData.pathAB hedge interface.start_touching
    interface.end_touching hstart hend hrootRegular.2.1 hfixedRegular.2.1
    normalization.normalized_star
  obtain ⟨selectedSlot, selectedSign, hselected⟩ :=
    (normalization.piece_cell_cover _).mp hrootCell
  let centralIndex := normalization.pieceIndex selectedSlot selectedSign
  have hcentralIndex := normalization.piece_index_central selectedSlot selectedSign
  have hpieceCells := normalization.piece_layout_cells selectedSlot selectedSign
  have hexteriorCells := normalization.fixed_exterior_cells
  have hcentralCell : LatticeVertexIncidentCell normalization.normalizedPoint
      direction ∈ (SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v centralIndex).cells := by
    dsimp [centralIndex]
    rw [← hpieceCells]
    exact hselected
  have hexteriorCell : LatticeVertexIncidentCell normalization.normalizedPoint
      (direction + 2) ∈
      (SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v normalization.exteriorIndex).cells := by
    rw [hexteriorCells]
    exact hfixedCell
  have hstar : ∀ y, y = normalization.normalizedPoint ∨
      y = normalization.normalizedPoint + 1 ∨
      y = normalization.normalizedPoint - 1 ∨
      y = normalization.normalizedPoint + ⟨0, 1⟩ ∨
      y = normalization.normalizedPoint - ⟨0, 1⟩ →
    y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v normalization.exteriorIndex) ∨
      y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v centralIndex) := by
    have cell_corner (T : ProtoTile) (c : GaussianInt) (hc : c ∈ T.cells) :
        ∀ y, y = c ∨ y = c + 1 ∨ y = c + ⟨0, 1⟩ ∨
          y = c + 1 + ⟨0, 1⟩ → y ∈ FootprintVertices T := by
      intro y hy
      have hn : T.cells.Nonempty := ⟨c, hc⟩
      simp only [FootprintVertices, ite_eq_left hn, Set.mem_ofPred_eq]
      rcases hy with h | h | h | h
      · exact ⟨c, hc, Or.inl h⟩
      · exact ⟨c, hc, Or.inr (Or.inl h)⟩
      · exact ⟨c, hc, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨c, hc, Or.inr (Or.inr (Or.inr h))⟩
    let centralTile := SubtileOccurrenceInterpretation normalization.layout.P
      normalization.layout.u normalization.layout.v centralIndex
    let exteriorTile := SubtileOccurrenceInterpretation normalization.layout.P
      normalization.layout.u normalization.layout.v normalization.exteriorIndex
    have centralCorners := cell_corner centralTile
      (LatticeVertexIncidentCell normalization.normalizedPoint direction) hcentralCell
    have exteriorCorners := cell_corner exteriorTile
      (LatticeVertexIncidentCell normalization.normalizedPoint (direction + 2)) hexteriorCell
    intro y hy
    fin_cases direction <;>
    simp? [LatticeVertexIncidentCell] at hcentralCell hexteriorCell ⊢ <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    solve
    | apply Or.inr
      apply centralCorners
      simp [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
        Zsqrtd.ext_iff]
    | apply Or.inl
      apply exteriorCorners
      simp [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
        Zsqrtd.ext_iff]
  exact ⟨
    { edgeAtPoint := hedge
      root_induced := hrootRegular.2.1
      fixed_induced := hfixedRegular.2.1
      routedDirection := direction
      routed_root_cell := hrootCell
      routed_fixed_cell := hfixedCell
      selectedSlot := selectedSlot
      selectedSign := selectedSign
      selected_piece_cell := hselected
      centralIndex := centralIndex
      central_index := hcentralIndex
      selected_central_index := rfl
      exterior_routed_cell := hexteriorCell
      central_routed_cell := hcentralCell
      selected_star := hstar }
    ⟩

end ApollonianSuperharmonic

end
