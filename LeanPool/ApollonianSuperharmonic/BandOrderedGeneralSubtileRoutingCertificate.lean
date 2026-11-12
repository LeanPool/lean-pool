/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileInterfaceCertificate
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell

-- [TABLET NODE: BandOrderedGeneralSubtileRoutingCertificate]

/-!
# BandOrderedGeneralSubtileRoutingCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Given a `BandOrderedGeneralSubtileInterfaceCertificate`, a subtile
routing certificate records an actual common footprint edge through the
normalized point, the induced-edge properties of both outer lattice tiles,
and a direction whose opposite incident cells lie in the normalized root and
fixed supports.  It then chooses exactly one signed piece of the already
fixed decomposition containing the root-side incident cell.

The certificate retains that same slot and sign by naming its central
periodic occurrence, recording equality with the normalization certificate's
central index for that piece, and transferring the routed root-side cell to
that occurrence.  It transfers the opposite cell to the already fixed
exterior occurrence and records that these same two occurrences cover the
normalized point and its four axial neighbors.  No second decomposition or
second piece selection is permitted by the data.
-/
structure BandOrderedGeneralSubtileRoutingCertificate
    {C₀ Cᵢ : BandCircle} {q : Fin 4 → CircleCoordinates}
    {i : Fin 3} {T₀ Tᵢ : ProtoTile}
    {h₀ hᵢ : PartialOdometer} {x : GaussianInt}
    {normalization : BandOrderedGeneralSubtileNormalizationCertificate
      C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x}
    (interface : BandOrderedGeneralSubtileInterfaceCertificate normalization) where
-- BODY
  edgeAtPoint : ∃ edge : Finset GaussianInt,
    normalization.normalizedPoint ∈ edge ∧
      edge ∈ FootprintEdges normalization.normalizedRoot ∩
        FootprintEdges normalization.normalizedFixed
  root_induced : ∀ y,
    y ∈ FootprintVertices normalization.normalizedRoot → ∀ z,
    z ∈ FootprintVertices normalization.normalizedRoot →
      FourNeighborAdjacent y z →
      ({y, z} : Finset GaussianInt) ∈
        FootprintEdges normalization.normalizedRoot
  fixed_induced : ∀ y,
    y ∈ FootprintVertices normalization.normalizedFixed → ∀ z,
    z ∈ FootprintVertices normalization.normalizedFixed →
      FourNeighborAdjacent y z →
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
  /-- The central occurrence containing the selected root-side incident square. -/
  centralIndex : PeriodicSubtileIndex
  central_index :
    centralIndex = ⟨.A, 0, 0⟩ ∨ centralIndex = ⟨.B, 0, 0⟩ ∨
    centralIndex = ⟨.C, 0, 0⟩ ∨ centralIndex = ⟨.D, 0, 0⟩ ∨
    centralIndex = ⟨.E, 0, 0⟩ ∨ centralIndex = ⟨.F, 0, 0⟩
  selected_central_index :
    centralIndex = normalization.pieceIndex selectedSlot selectedSign
  exterior_routed_cell : LatticeVertexIncidentCell normalization.normalizedPoint
    (routedDirection + 2) ∈
      (SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v
        normalization.exteriorIndex).cells
  central_routed_cell : LatticeVertexIncidentCell normalization.normalizedPoint
    routedDirection ∈
      (SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v centralIndex).cells
  selected_star : ∀ y,
    y = normalization.normalizedPoint ∨
      y = normalization.normalizedPoint + 1 ∨
      y = normalization.normalizedPoint - 1 ∨
      y = normalization.normalizedPoint + ⟨0, 1⟩ ∨
      y = normalization.normalizedPoint - ⟨0, 1⟩ →
    y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v
          normalization.exteriorIndex) ∨
      y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v centralIndex)

end ApollonianSuperharmonic

end
