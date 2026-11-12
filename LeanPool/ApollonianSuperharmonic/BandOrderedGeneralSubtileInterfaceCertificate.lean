/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileNormalizationCertificate
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: BandOrderedGeneralSubtileInterfaceCertificate]

/-!
# BandOrderedGeneralSubtileInterfaceCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Given a `BandOrderedGeneralSubtileNormalizationCertificate`, a
subtile interface certificate consists of two companion prototiles and two
literal `ExactTileInterfaceTriple` records on the same normalized
root--fixed pair.  The normalized point lies on their complete common outer
interface.  The two records have crossed distinguished endpoints.

The certificate separately retains lattice-tile witnesses for the two outer
supports and both companions, all six pairwise cell-disjointness facts, and
literal `TouchingTriple` witnesses for the two endpoint triples.
Thus every geometric and topological fact about the original normalized
outer interface is fixed before any decomposition piece is selected.
-/
structure BandOrderedGeneralSubtileInterfaceCertificate
    {C₀ Cᵢ : BandCircle} {q : Fin 4 → CircleCoordinates}
    {i : Fin 3} {T₀ Tᵢ : ProtoTile}
    {h₀ hᵢ : PartialOdometer} {x : GaussianInt}
    (normalization : BandOrderedGeneralSubtileNormalizationCertificate
      C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x) where
-- BODY
  /-- The literal third tile at the initial endpoint of the root-fixed interface. -/
  startCompanion : ProtoTile
  /-- The literal third tile at the terminal endpoint of that same interface. -/
  endCompanion : ProtoTile
  /-- The complete interface triple with its distinguished initial endpoint. -/
  startData : ExactTileInterfaceTriple normalization.normalizedRoot
    normalization.normalizedFixed startCompanion
  /-- The complete interface triple with the two root-fixed endpoints exchanged. -/
  endData : ExactTileInterfaceTriple normalization.normalizedRoot
    normalization.normalizedFixed endCompanion
  normalized_point_on_start_path : normalization.normalizedPoint ∈
    FootprintVertices normalization.normalizedRoot ∩
      FootprintVertices normalization.normalizedFixed
  interface_endpoints :
    endData.point = startData.otherAB ∧ endData.otherAB = startData.point
  root_lattice : LatticeTile normalization.normalizedRoot
  fixed_lattice : LatticeTile normalization.normalizedFixed
  start_lattice : LatticeTile startCompanion
  end_lattice : LatticeTile endCompanion
  root_fixed_disjoint :
    Disjoint normalization.normalizedRoot.cells normalization.normalizedFixed.cells
  root_start_disjoint :
    Disjoint normalization.normalizedRoot.cells startCompanion.cells
  fixed_start_disjoint :
    Disjoint normalization.normalizedFixed.cells startCompanion.cells
  root_end_disjoint :
    Disjoint normalization.normalizedRoot.cells endCompanion.cells
  fixed_end_disjoint :
    Disjoint normalization.normalizedFixed.cells endCompanion.cells
  start_end_disjoint : Disjoint startCompanion.cells endCompanion.cells
  start_touching : TouchingTriple normalization.normalizedRoot
    normalization.normalizedFixed startCompanion
  end_touching : TouchingTriple normalization.normalizedRoot
    normalization.normalizedFixed endCompanion

end ApollonianSuperharmonic

end
