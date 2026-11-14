/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent

-- [TABLET NODE: BandOrderedGeneralRightNormalizationCertificate]

/-!
# BandOrderedGeneralRightNormalizationCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For right-lattice adjacent tile odometers $(T,h)$ and $(N,k)$ of a circle
$C$, a right normalization certificate consists of one proper presentation
$q$ of $C$, one cyclic parent rotation, one packing-symmetry word, and the
resulting ordered-general presentation, transformed circle, literal supports,
functions, point, and slopes.  It includes one ordered-general layout rooted
at the transformed fixed support and one reindexed six-piece decomposition of
the transformed root support.  It retains the transformed point's membership
in both transformed function domains, lattice-tile certificates for both
transformed outer supports, and a named
`QuarterTurnSymmetric` witness for the transformed fixed support.

Write $\bar q$ for the resulting ordered-general presentation.  The
certificate also names three parent slots $(i,j,k)$, records that they are one
of the cyclic triples
$$
 (0,1,2),\qquad(1,2,0),\qquad(2,0,1),
$$
and stores a right-neighbor polarity $\epsilon$.  Writing
$$
 b_s=v(\bar q_0,\bar q_{s+1})
$$
for the outgoing vector of the normalized presentation and $d$ for the stored
right-neighbor displacement, its exact displacement field is
$$
 d=\begin{cases}
 b_k,&\epsilon=\mathsf{true},\\
 -b_k,&\epsilon=\mathsf{false}.
 \end{cases}
$$
It records the transported adjacency with this complemented polarity, the
cell and empty-anchor alignment of the two outer supports, the corresponding
observable alignments of the two signed boundary pieces, and the transported
five-point footprint cover.  In particular, the certificate contains only one
layout and one decomposition.
-/
structure BandOrderedGeneralRightNormalizationCertificate
    (C : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
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
  normalized_fixed_circle_eq : normalizedFixedCircle.1.1 =
    BandPackingSymmetryCircleAction symmetry C.1.1
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
  normalized_point_root_domain : normalizedPoint ∈ normalizedRootFunction.domain
  normalized_point_fixed_domain : normalizedPoint ∈ normalizedFixedFunction.domain
  normalized_root_odometer :
    TileOdometer (normalizedPresentation 0) normalizedRoot normalizedRootFunction
  normalized_fixed_odometer :
    TileOdometer normalizedFixedCircle.1.1 normalizedFixed normalizedFixedFunction
  normalized_root_lattice : LatticeTile normalizedRoot
  normalized_fixed_lattice : LatticeTile normalizedFixed
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
  adjacency : RightLatticeAdjacent normalizedCircle normalizedRoot normalizedFixed
    normalizedRootFunction normalizedFixedFunction
  /-- The literal ordered-general layout rooted at the normalized fixed full tile. -/
  layout : BandOrderedGeneralLayoutCertificate normalizedPresentation configuration
    normalizedCircle normalizedFixed
  fixed_quarter_turn : QuarterTurnSymmetric normalizedFixed
  /-- The first parent slot in the retained cyclic boundary triple. -/
  rightFirstSlot : Fin 3
  /-- The second parent slot in that same cyclic boundary triple. -/
  rightSecondSlot : Fin 3
  /-- The parent slot determining the full right-neighbor displacement. -/
  rightDirectionSlot : Fin 3
  right_slots_cyclic :
    (rightFirstSlot = 0 ∧ rightSecondSlot = 1 ∧ rightDirectionSlot = 2) ∨
    (rightFirstSlot = 1 ∧ rightSecondSlot = 2 ∧ rightDirectionSlot = 0) ∨
    (rightFirstSlot = 2 ∧ rightSecondSlot = 0 ∧ rightDirectionSlot = 1)
  /-- The polarity of the retained right-neighbor presentation. -/
  rightNeighborPositive : Bool
  right_adjacency_centroid : TileCentroid normalizedFixed - TileCentroid normalizedRoot =
    (if rightNeighborPositive = true then (-1 : Real) else 1) •
      GaussianRealPoint
        (BandVectors.1 (normalizedPresentation 0)
          (normalizedPresentation rightDirectionSlot.succ))
  right_adjacency_slope_real : normalizedFixedSlope.1 - normalizedRootSlope.1 =
    (if rightNeighborPositive = true then (-1 : Real) else 1) *
      (BandVectors.2 (normalizedPresentation 0)
        (normalizedPresentation rightDirectionSlot.succ)).re
  right_adjacency_slope_imag : normalizedFixedSlope.2 - normalizedRootSlope.2 =
    (if rightNeighborPositive = true then (-1 : Real) else 1) *
      (BandVectors.2 (normalizedPresentation 0)
        (normalizedPresentation rightDirectionSlot.succ)).im
  /-- The actual signed outgoing displacement between the two normalized full tiles. -/
  rightNeighborDisplacement : GaussianInt
  right_neighbor_displacement : rightNeighborDisplacement =
    (if rightNeighborPositive = true then (1 : GaussianInt) else -1) *
      BandVectors.1 (normalizedPresentation 0)
        (normalizedPresentation rightDirectionSlot.succ)
  right_neighbor_cells : normalizedRoot.cells =
    (TileTranslation normalizedFixed rightNeighborDisplacement).cells
  right_neighbor_empty_anchor : normalizedRoot.cells = ∅ -> normalizedRoot.anchor =
    (TileTranslation normalizedFixed rightNeighborDisplacement).anchor
  /-- The sign of the first decomposed piece lying on the fixed-tile boundary. -/
  firstBoundarySign : Bool
  /-- The sign of the second decomposed piece lying on that boundary. -/
  secondBoundarySign : Bool
  boundary_signs :
    (rightNeighborPositive = true ∧ firstBoundarySign = true ∧
      secondBoundarySign = false) ∨
    (rightNeighborPositive = false ∧ firstBoundarySign = false ∧
      secondBoundarySign = true)
  first_boundary_cells : (pieces rightFirstSlot firstBoundarySign).cells =
    (TileTranslation (layout.P rightFirstSlot firstBoundarySign)
      rightNeighborDisplacement).cells
  first_boundary_empty_anchor :
    (pieces rightFirstSlot firstBoundarySign).cells = ∅ ->
      (pieces rightFirstSlot firstBoundarySign).anchor =
        (TileTranslation (layout.P rightFirstSlot firstBoundarySign)
          rightNeighborDisplacement).anchor
  first_boundary_footprint :
    FootprintVertices (pieces rightFirstSlot firstBoundarySign) =
      FootprintVertices
        (TileTranslation (layout.P rightFirstSlot firstBoundarySign)
          rightNeighborDisplacement)
  first_boundary_domain :
    ((functions rightFirstSlot firstBoundarySign).domain : Set GaussianInt) =
      FootprintVertices
        (TileTranslation (layout.P rightFirstSlot firstBoundarySign)
          rightNeighborDisplacement)
  second_boundary_cells : (pieces rightSecondSlot secondBoundarySign).cells =
    (TileTranslation (layout.P rightSecondSlot secondBoundarySign)
      rightNeighborDisplacement).cells
  second_boundary_empty_anchor :
    (pieces rightSecondSlot secondBoundarySign).cells = ∅ ->
      (pieces rightSecondSlot secondBoundarySign).anchor =
        (TileTranslation (layout.P rightSecondSlot secondBoundarySign)
          rightNeighborDisplacement).anchor
  second_boundary_footprint :
    FootprintVertices (pieces rightSecondSlot secondBoundarySign) =
      FootprintVertices
        (TileTranslation (layout.P rightSecondSlot secondBoundarySign)
          rightNeighborDisplacement)
  second_boundary_domain :
    ((functions rightSecondSlot secondBoundarySign).domain : Set GaussianInt) =
      FootprintVertices
        (TileTranslation (layout.P rightSecondSlot secondBoundarySign)
          rightNeighborDisplacement)
  normalized_star : forall y,
    y = normalizedPoint ∨ y = normalizedPoint + 1 ∨
      y = normalizedPoint - 1 ∨ y = normalizedPoint + ⟨0, 1⟩ ∨
      y = normalizedPoint - ⟨0, 1⟩ ->
    y ∈ FootprintVertices normalizedRoot ∨
      y ∈ FootprintVertices normalizedFixed

end ApollonianSuperharmonic

end
