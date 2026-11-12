/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightInterfaceCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell

-- [TABLET NODE: BandOrderedGeneralRightRoutingCertificate]

/-!
# BandOrderedGeneralRightRoutingCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Given a `BandOrderedGeneralRightInterfaceCertificate`, a right routing
certificate records an actual common outer footprint edge through the
normalized point, the two induced-edge properties, and opposite incident
cells of the transformed root and fixed tiles.  It selects a signed piece of
the fixed decomposition containing the root-side cell and the corresponding
central layout occurrence containing the fixed-side cell.  It records their
literal occurrence indices, observable alignment, routed memberships, and
five-point cover, together with the common occurrence edge and selected
contact row returned by shifted routed-boundary localization.
-/
structure BandOrderedGeneralRightRoutingCertificate
    {C : BandCircle} {T N : ProtoTile} {h k : PartialOdometer}
    {x : GaussianInt}
    {normalization :
      BandOrderedGeneralRightNormalizationCertificate C T N h k x}
    (interface : BandOrderedGeneralRightInterfaceCertificate normalization) where
-- BODY
  edgeAtPoint : exists edge : Finset GaussianInt,
    normalization.normalizedPoint ∈ edge ∧
      edge ∈ FootprintEdges normalization.normalizedRoot ∩
        FootprintEdges normalization.normalizedFixed
  root_induced : forall y,
    y ∈ FootprintVertices normalization.normalizedRoot -> forall z,
    z ∈ FootprintVertices normalization.normalizedRoot ->
      FourNeighborAdjacent y z ->
      ({y, z} : Finset GaussianInt) ∈
        FootprintEdges normalization.normalizedRoot
  fixed_induced : forall y,
    y ∈ FootprintVertices normalization.normalizedFixed -> forall z,
    z ∈ FootprintVertices normalization.normalizedFixed ->
      FourNeighborAdjacent y z ->
      ({y, z} : Finset GaussianInt) ∈
        FootprintEdges normalization.normalizedFixed
  /-- The incident-square direction with root and fixed cells in opposite sectors. -/
  routedDirection : Fin 4
  routed_root_cell : LatticeVertexIncidentCell normalization.normalizedPoint
    routedDirection ∈ normalization.normalizedRoot.cells
  routed_fixed_cell : LatticeVertexIncidentCell normalization.normalizedPoint
    (routedDirection + 2) ∈ normalization.normalizedFixed.cells
  /-- The selected parent slot of the fixed six-piece decomposition. -/
  selectedSlot : Fin 3
  /-- The sign of that selected occurrence in the same decomposition family. -/
  selectedSign : Bool
  selected_piece_cell : LatticeVertexIncidentCell normalization.normalizedPoint
    routedDirection ∈ (normalization.pieces selectedSlot selectedSign).cells
  selected_boundary_piece :
    (selectedSlot = normalization.rightFirstSlot ∧
      selectedSign = normalization.firstBoundarySign) ∨
    (selectedSlot = normalization.rightSecondSlot ∧
      selectedSign = normalization.secondBoundarySign)
  /-- The literal exterior occurrence selected by the routed contact. -/
  exteriorIndex : PeriodicSubtileIndex
  /-- The literal central child occurrence selected by the opposite routed square. -/
  centralIndex : PeriodicSubtileIndex
  exterior_index :
    exteriorIndex = ⟨.A, -1, -1⟩ ∨ exteriorIndex = ⟨.A, 0, -1⟩ ∨
    exteriorIndex = ⟨.C, 1, 0⟩ ∨ exteriorIndex = ⟨.C, 1, 1⟩ ∨
    exteriorIndex = ⟨.E, 0, 1⟩ ∨ exteriorIndex = ⟨.E, -1, 0⟩ ∨
    exteriorIndex = ⟨.B, 1, 1⟩ ∨ exteriorIndex = ⟨.B, 0, 1⟩ ∨
    exteriorIndex = ⟨.D, -1, 0⟩ ∨ exteriorIndex = ⟨.D, -1, -1⟩ ∨
    exteriorIndex = ⟨.F, 0, -1⟩ ∨ exteriorIndex = ⟨.F, 1, 0⟩
  central_index :
    centralIndex = ⟨.A, 0, 0⟩ ∨ centralIndex = ⟨.B, 0, 0⟩ ∨
    centralIndex = ⟨.C, 0, 0⟩ ∨ centralIndex = ⟨.D, 0, 0⟩ ∨
    centralIndex = ⟨.E, 0, 0⟩ ∨ centralIndex = ⟨.F, 0, 0⟩
  selected_exterior_cells :
    (normalization.pieces selectedSlot selectedSign).cells =
      (SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v exteriorIndex).cells
  selected_exterior_empty_anchor :
    (normalization.pieces selectedSlot selectedSign).cells = ∅ ->
      (normalization.pieces selectedSlot selectedSign).anchor =
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v exteriorIndex).anchor
  selected_exterior_footprint :
    FootprintVertices (normalization.pieces selectedSlot selectedSign) =
      FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v exteriorIndex)
  selected_exterior_domain :
    ((normalization.functions selectedSlot selectedSign).domain :
      Set GaussianInt) =
      FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v exteriorIndex)
  exterior_routed_cell :
    LatticeVertexIncidentCell normalization.normalizedPoint routedDirection ∈
      (SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v exteriorIndex).cells
  central_routed_cell :
    LatticeVertexIncidentCell normalization.normalizedPoint
      (routedDirection + 2) ∈
      (SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v centralIndex).cells
  selected_star : forall y,
    y = normalization.normalizedPoint ∨
      y = normalization.normalizedPoint + 1 ∨
      y = normalization.normalizedPoint - 1 ∨
      y = normalization.normalizedPoint + ⟨0, 1⟩ ∨
      y = normalization.normalizedPoint - ⟨0, 1⟩ ->
    y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v exteriorIndex) ∨
      y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v centralIndex)
  /-- The common occurrence footprint edge returned by shifted boundary localization. -/
  localizedEdge : Finset GaussianInt
  localized_edge_at_point : normalization.normalizedPoint ∈ localizedEdge
  localized_edge_common : localizedEdge ∈
    FootprintEdges
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v exteriorIndex) ∩
      FootprintEdges
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v centralIndex)
  localized_contact : Nonempty
    (BandOrderedGeneralSelectedContactRow normalization.normalizedPresentation
      normalization.configuration normalization.normalizedCircle
      normalization.normalizedFixed normalization.layout exteriorIndex centralIndex)

end ApollonianSuperharmonic

end
