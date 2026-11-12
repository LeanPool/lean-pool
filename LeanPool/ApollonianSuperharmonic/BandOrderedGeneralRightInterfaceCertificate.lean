/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightNormalizationCertificate
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: BandOrderedGeneralRightInterfaceCertificate]

/-!
# BandOrderedGeneralRightInterfaceCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Given a `BandOrderedGeneralRightNormalizationCertificate`, a right
interface certificate consists of two companion prototiles and two
literal `ExactTileInterfaceTriple` records on the same transformed
root--fixed pair.  Both outer supports and both companions are lattice tiles;
the four tile cell sets have all disjointness relations needed by the endpoint
theorem; and each endpoint record is accompanied by its literal touching
triple.  The two records have crossed distinguished endpoints, so the first
record's $AB$ path is the single oriented complete interface path used later;
the normalized point is retained as a vertex of its common root--fixed
footprint.
-/
structure BandOrderedGeneralRightInterfaceCertificate
    {C : BandCircle} {T N : ProtoTile} {h k : PartialOdometer}
    {x : GaussianInt}
    (normalization :
      BandOrderedGeneralRightNormalizationCertificate C T N h k x) where
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
