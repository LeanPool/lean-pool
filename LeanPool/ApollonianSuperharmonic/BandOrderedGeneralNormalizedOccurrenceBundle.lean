/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightPlacement
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtilePlacement
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: BandOrderedGeneralNormalizedOccurrenceBundle]

/-!
# BandOrderedGeneralNormalizedOccurrenceBundle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $C,D$ be positive band circles, let $(T,h)$ and $(N,k)$ be tile
odometers, and let $x$ be a lattice vertex.  A
*normalized routed occurrence bundle* for these data consists of the
following single, mutually aligned package.

It contains one proper presentation of $C$, one cyclic parent rotation, and
one packing symmetry.  Applying that symmetry after that rotation produces
one ordered-general presentation $\bar q$, positive circles $\bar C,\bar D$,
literal transformed supports $\bar T,\bar N$, literal transformed functions
$\bar h,\bar k$, the transformed point $\bar x$, and their defined slopes.
All equalities with the corresponding circle, tile, function, and point
actions are part of the data.

The bundle contains exactly one family $(S_i^e,f_i^e)$ carrying every
conclusion of the single reindexed six-piece odometer decomposition of
$(\bar T,\bar h)$: the outer band-prototile certificate, all six
tile-odometer certificates, exact cell and domain covers, footprint
containments, centroid formulas, restriction equalities, pairwise
compatibility, and the six zero-curvature-or-slope alternatives.

It also contains the complete interface of $\bar T$ and $\bar N$ and both
of its endpoint packages.  More precisely it stores two third tiles, two
`ExactTileInterfaceTriple` records whose $\bar T$--$\bar N$ paths
are the same path in opposite orientations, lattice-tile certificates, all
five required cell-disjointness assertions, the two literal touching
triples, an actual common edge through $\bar x$, and the induced-edge
properties for the two outer tiles.  It stores the transported five-point
star cover and the direction $j$ returned by
`CoveredInterfaceOppositeIncidentCells`, so that
$$
 \operatorname{inc}(\bar x,j)\in\operatorname{cells}(\bar T),\qquad
 \operatorname{inc}(\bar x,j+2)\in\operatorname{cells}(\bar N).
$$
The selected signed piece $S_i^e$ contains the first of these squares.

Finally the bundle is tagged with exactly one of two placement
certificates.  In the right-adjacent case it contains a
`BandOrderedGeneralRightPlacement`: the layout is literally rooted
at $\bar N$, exactly the two pieces of $\bar T$ meeting $\bar N$ are the
cyclically labelled boundary occurrences, the selected routed piece is one
of those two, and the central routed occurrence is only a child of
$\bar N$; the exact translated outer-neighbor alignment of $\bar T$ with
$\bar N$ is retained separately.  The other four pieces remain present in
the bundle's single six-piece decomposition but acquire no exterior role.
In the subtile-adjacent case it contains a
`BandOrderedGeneralSubtilePlacement`: the layout is literally
rooted at $\bar T$, its six decomposed pieces are central occurrences, and
$\bar N$ is aligned with the exterior occurrence.  Each alternative stores
the routed occurrence memberships and the five-point cover derived from
the same two opposite incident squares.  Thus the package uses one packing
symmetry and one decomposition family, while never imposing the right
branch's exterior/central roles on the subtile branch or conversely.
-/
structure BandOrderedGeneralNormalizedOccurrenceBundle
    (C D : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt) where
-- BODY
  /-- The proper source presentation of the root circle. -/
  presentation : Fin 4 -> CircleCoordinates
  presentation_proper : ProperBandQuadruple presentation
  presentation_child : presentation 0 = C.1.1
  /-- The cyclic parent rotation used before applying the packing symmetry. -/
  parentRotation : Fin 3
  /-- The single packing-symmetry word used throughout the normalization. -/
  symmetry : BandPackingSymmetry
  /-- The source presentation after the chosen cyclic parent rotation. -/
  rotatedPresentation : Fin 4 -> CircleCoordinates
  rotated_presentation_eq : rotatedPresentation =
    ![presentation 0, presentation parentRotation.succ,
      presentation (parentRotation + 1).succ,
      presentation (parentRotation + 2).succ]
  /-- The ordered-general presentation obtained by the symmetry action. -/
  normalizedPresentation : Fin 4 -> CircleCoordinates
  normalized_presentation_eq : normalizedPresentation =
    BandPackingSymmetryQuadrupleAction symmetry rotatedPresentation
  /-- The ordered-general predecessor data for the normalized presentation. -/
  configuration : BandOrderedGeneralConfiguration normalizedPresentation
  /-- The positive root circle in the normalized presentation. -/
  normalizedCircle : BandCircle
  normalized_circle_eq : normalizedPresentation 0 = normalizedCircle.1.1
  /-- The transformed positive circle of the fixed tile odometer. -/
  normalizedFixedCircle : BandCircle
  normalized_fixed_circle_eq :
    normalizedFixedCircle.1.1 = BandPackingSymmetryCircleAction symmetry D.1.1
  /-- The literal transformed root support. -/
  normalizedRoot : ProtoTile
  /-- The literal transformed fixed support. -/
  normalizedFixed : ProtoTile
  /-- The transformed root odometer on its actual finite domain. -/
  normalizedRootFunction : PartialOdometer
  /-- The transformed fixed odometer on its actual finite domain. -/
  normalizedFixedFunction : PartialOdometer
  /-- The transformed lattice contact point. -/
  normalizedPoint : GaussianInt
  normalized_root_eq : normalizedRoot = BandPackingSymmetryTileAction symmetry T
  normalized_fixed_eq : normalizedFixed = BandPackingSymmetryTileAction symmetry N
  normalized_root_function_eq : normalizedRootFunction =
    BandPackingSymmetryPartialOdometerAction symmetry h
  normalized_fixed_function_eq : normalizedFixedFunction =
    BandPackingSymmetryPartialOdometerAction symmetry k
  normalized_point_eq : normalizedPoint =
    BandPackingSymmetryVectorAction symmetry x
  normalized_root_odometer :
    TileOdometer (normalizedPresentation 0) normalizedRoot normalizedRootFunction
  normalized_fixed_odometer :
    TileOdometer normalizedFixedCircle.1.1 normalizedFixed normalizedFixedFunction
  /-- The defined slope of the transformed root odometer. -/
  normalizedRootSlope : Real × Real
  /-- The defined slope of the transformed fixed odometer. -/
  normalizedFixedSlope : Real × Real
  normalized_root_slope :
    PartialOdometerSlope normalizedRootFunction = some normalizedRootSlope
  normalized_fixed_slope :
    PartialOdometerSlope normalizedFixedFunction = some normalizedFixedSlope
  /-- The single family of six signed supports in the normalized root decomposition. -/
  pieces : Fin 3 -> Bool -> ProtoTile
  /-- The literal partial odometers on that same six-piece family. -/
  functions : Fin 3 -> Bool -> PartialOdometer
  root_band : BandPrototile (normalizedPresentation 0) normalizedRoot
  piece_odometer : forall i s, TileOdometer (normalizedPresentation i.succ)
    (pieces i s) (functions i s)
  piece_cell_cover : forall z, z ∈ normalizedRoot.cells ↔
    exists i s, z ∈ (pieces i s).cells
  piece_footprint : forall i s,
    FootprintVertices (pieces i s) ⊆ FootprintVertices normalizedRoot
  piece_centroid : forall i s,
    TileCentroid (pieces i s) - TileCentroid normalizedRoot =
      (if s = true then (1 : Real) else -1) •
        ((1 / 2 : Real) •
          (GaussianRealPoint
              (BandVectors.1 (normalizedPresentation ((i + 2).succ))
                (normalizedPresentation ((i + 1).succ))) -
            (-((GaussianRealPoint
                (BandVectors.1 (normalizedPresentation ((i + 2).succ))
                  (normalizedPresentation ((i + 1).succ)))).2),
              (GaussianRealPoint
                (BandVectors.1 (normalizedPresentation ((i + 2).succ))
                  (normalizedPresentation ((i + 1).succ)))).1)))
  function_domain_cover : forall z, z ∈ normalizedRootFunction.domain ↔
    exists i s, z ∈ (functions i s).domain
  function_restriction : forall i s z, z ∈ (functions i s).domain ->
    normalizedRootFunction.value z = (functions i s).value z
  function_compatibility : forall i s j t,
    OdometerCompatibility (functions i s) (functions j t)
  piece_slope : forall i s, (normalizedPresentation i.succ).1 = 0 ∨
    exists p p_i : Real × Real,
      PartialOdometerSlope normalizedRootFunction = some p ∧
      PartialOdometerSlope (functions i s) = some p_i ∧
      p_i.1 - p.1 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (normalizedPresentation ((i + 2).succ))
            (normalizedPresentation ((i + 1).succ))).re : Int) -
           ((BandVectors.2 (normalizedPresentation ((i + 2).succ))
            (normalizedPresentation ((i + 1).succ))).im : Int)) ∧
      p_i.2 - p.2 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (normalizedPresentation ((i + 2).succ))
            (normalizedPresentation ((i + 1).succ))).im : Int) +
           ((BandVectors.2 (normalizedPresentation ((i + 2).succ))
            (normalizedPresentation ((i + 1).succ))).re : Int))
  /-- The literal third tile at the initial endpoint of the root-fixed interface. -/
  startCompanion : ProtoTile
  /-- The literal third tile at the terminal endpoint of that same interface. -/
  endCompanion : ProtoTile
  /-- The complete interface triple with its distinguished initial endpoint. -/
  startData : ExactTileInterfaceTriple normalizedRoot normalizedFixed startCompanion
  /-- The complete interface triple with the two root-fixed endpoints exchanged. -/
  endData : ExactTileInterfaceTriple normalizedRoot normalizedFixed endCompanion
  interface_endpoints :
    endData.point = startData.otherAB ∧ endData.otherAB = startData.point
  root_lattice : LatticeTile normalizedRoot
  fixed_lattice : LatticeTile normalizedFixed
  start_lattice : LatticeTile startCompanion
  end_lattice : LatticeTile endCompanion
  root_fixed_disjoint : Disjoint normalizedRoot.cells normalizedFixed.cells
  root_start_disjoint : Disjoint normalizedRoot.cells startCompanion.cells
  fixed_start_disjoint : Disjoint normalizedFixed.cells startCompanion.cells
  root_end_disjoint : Disjoint normalizedRoot.cells endCompanion.cells
  fixed_end_disjoint : Disjoint normalizedFixed.cells endCompanion.cells
  start_touching : TouchingTriple normalizedRoot normalizedFixed startCompanion
  end_touching : TouchingTriple normalizedRoot normalizedFixed endCompanion
  edgeAtPoint : exists edge : Finset GaussianInt,
    normalizedPoint ∈ edge ∧
      edge ∈ FootprintEdges normalizedRoot ∩ FootprintEdges normalizedFixed
  root_induced : forall y, y ∈ FootprintVertices normalizedRoot -> forall z,
    z ∈ FootprintVertices normalizedRoot -> FourNeighborAdjacent y z ->
      ({y, z} : Finset GaussianInt) ∈ FootprintEdges normalizedRoot
  fixed_induced : forall y, y ∈ FootprintVertices normalizedFixed -> forall z,
    z ∈ FootprintVertices normalizedFixed -> FourNeighborAdjacent y z ->
      ({y, z} : Finset GaussianInt) ∈ FootprintEdges normalizedFixed
  normalized_star : forall y,
    y = normalizedPoint ∨ y = normalizedPoint + 1 ∨
      y = normalizedPoint - 1 ∨ y = normalizedPoint + ⟨0, 1⟩ ∨
      y = normalizedPoint - ⟨0, 1⟩ ->
    y ∈ FootprintVertices normalizedRoot ∨
      y ∈ FootprintVertices normalizedFixed
  /-- The incident-square direction with root and fixed cells in opposite sectors. -/
  routedDirection : Fin 4
  routed_root_cell :
    LatticeVertexIncidentCell normalizedPoint routedDirection ∈ normalizedRoot.cells
  routed_fixed_cell : LatticeVertexIncidentCell normalizedPoint
    (routedDirection + 2) ∈ normalizedFixed.cells
  /-- The selected parent slot of the fixed six-piece decomposition. -/
  selectedSlot : Fin 3
  /-- The sign of that selected occurrence in the same decomposition family. -/
  selectedSign : Bool
  selected_piece_cell : LatticeVertexIncidentCell normalizedPoint routedDirection ∈
    (pieces selectedSlot selectedSign).cells
  /-- The branch-specific right or subtile placement of the single normalized decomposition. -/
  placement :
    BandOrderedGeneralRightPlacement normalizedPresentation configuration
        normalizedCircle normalizedRoot normalizedFixed normalizedRootFunction
        normalizedFixedFunction normalizedPoint pieces functions selectedSlot
        selectedSign routedDirection ⊕
      BandOrderedGeneralSubtilePlacement normalizedPresentation configuration
        normalizedCircle normalizedFixedCircle normalizedRoot normalizedFixed
        normalizedRootFunction normalizedFixedFunction normalizedPoint pieces
        functions selectedSlot selectedSign routedDirection

end ApollonianSuperharmonic

end
