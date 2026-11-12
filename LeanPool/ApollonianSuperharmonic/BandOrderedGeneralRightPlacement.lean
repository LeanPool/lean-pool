/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: BandOrderedGeneralRightPlacement]

/-!
# BandOrderedGeneralRightPlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix an ordered-general presentation $q$, its configuration, a normalized
right-adjacent pair $(\bar T,\bar h),(\bar N,\bar k)$, an externally
supplied family $(S_i^e,f_i^e)$ of six supports and partial odometers, a
selected slot, the normalized contact point, and its routed
incident-square direction.  A *right-adjacent normalized placement*
consists of the following data.  This record imposes only the
branch-specific adjacency, literal layout root, two boundary-piece
alignments, occurrence-index roles, routed memberships, star cover, and
translated full-neighbor alignment listed below.  The
tile-odometer facts, cell and domain covers, restriction values,
compatibility, centroid formulas, and slope alternatives for
$(S_i^e,f_i^e)$ are not fields of this record; they are supplied once by
the enclosing normalized routed occurrence bundle.

It contains the transported right-lattice adjacency and one
`BandOrderedGeneralLayoutCertificate` whose root is literally the
fixed full tile $\bar N$.  It stores a cyclic triple $(i,j,k)$ and a
polarity.  The same $q$, direction $k$, and polarity explicitly realize
the centroid and two slope equations in the transported
`RightLatticeAdjacent` witness.  In the positive polarity the
full-neighbor displacement is $d=v_{0k}$ and the two boundary signs are
$+$ at $i$ and $-$ at $j$; in the reflected polarity they are
$d=-v_{0k}$, $-$ at $i$, and $+$ at $j$.

Exactly the two signed pieces on this boundary are retained.  In the
positive case they are observably aligned with
$$
 R_i^0=P_i^++v_{0k},\qquad R_j^3=P_j^-+v_{0k},
$$
and in the reflected case with
$$
 R_i^2=P_i^--v_{0k},\qquad R_j^1=P_j^+-v_{0k}.
$$
For each of these two pieces the record stores equality of cells,
conditional equality of anchors when those cells are empty, equality of
footprints, and equality of the corresponding function domain with the
literal boundary footprint.  The selected signed piece is one of these
two, and it is observably aligned in the same four senses with the retained
exterior occurrence $a$.  No alignment of the other four decomposed pieces
with exterior occurrences is asserted.

The exterior index $a$ is one of the twelve exterior indices.  A retained
central index $b$ is one of the six central indices and its occurrence
contains the routed square belonging to $\bar N$; it is not identified
with the whole tile $\bar N$.  The occurrence at $a$ contains the opposite
routed square, and the two occurrences' footprints cover the five axial
vertices at the normalized contact point, as derived from those two routed
squares.

Finally the certificate retains the resulting right-neighbor displacement
and the observable full-neighbor alignment
$$
 \operatorname{cells}(\bar T)=
   \operatorname{cells}(\bar N+d)
$$
and equality of the two anchors when this common cell set is empty.  Thus
the decomposed root is the actual translated outer neighbor of the literal
layout root, while the central occurrence selected by the routed square is
only a child occurrence of that layout root.
-/
structure BandOrderedGeneralRightPlacement
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C0 : BandCircle)
    (root fixed : ProtoTile) (rootFunction fixedFunction : PartialOdometer)
    (point : GaussianInt) (pieces : Fin 3 -> Bool -> ProtoTile)
    (functions : Fin 3 -> Bool -> PartialOdometer)
    (selectedSlot : Fin 3) (selectedSign : Bool)
    (routedDirection : Fin 4) where
-- BODY
  adjacency : RightLatticeAdjacent C0 root fixed rootFunction fixedFunction
  /-- The literal ordered-general layout rooted at the normalized fixed full tile. -/
  layout : BandOrderedGeneralLayoutCertificate q cfg C0 fixed
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
  /-- The defined root slope appearing in the transported right-adjacency equations. -/
  rightRootSlope : Real × Real
  /-- The defined fixed slope in the same transported adjacency witness. -/
  rightFixedSlope : Real × Real
  right_root_slope : PartialOdometerSlope rootFunction = some rightRootSlope
  right_fixed_slope : PartialOdometerSlope fixedFunction = some rightFixedSlope
  right_adjacency_centroid : TileCentroid fixed - TileCentroid root =
    (if rightNeighborPositive = true then (-1 : Real) else 1) •
      GaussianRealPoint
        (BandVectors.1 (q 0) (q rightDirectionSlot.succ))
  right_adjacency_slope_real : rightFixedSlope.1 - rightRootSlope.1 =
    (if rightNeighborPositive = true then (-1 : Real) else 1) *
      (BandVectors.2 (q 0) (q rightDirectionSlot.succ)).re
  right_adjacency_slope_imag : rightFixedSlope.2 - rightRootSlope.2 =
    (if rightNeighborPositive = true then (-1 : Real) else 1) *
      (BandVectors.2 (q 0) (q rightDirectionSlot.succ)).im
  /-- The actual signed outgoing displacement between the two normalized full tiles. -/
  rightNeighborDisplacement : GaussianInt
  right_neighbor_displacement : rightNeighborDisplacement =
    (if rightNeighborPositive = true then (1 : GaussianInt) else -1) *
      BandVectors.1 (q 0) (q rightDirectionSlot.succ)
  right_neighbor_cells : root.cells =
    (TileTranslation fixed rightNeighborDisplacement).cells
  right_neighbor_empty_anchor : root.cells = ∅ -> root.anchor =
    (TileTranslation fixed rightNeighborDisplacement).anchor
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
  selected_boundary_piece :
    (selectedSlot = rightFirstSlot ∧ selectedSign = firstBoundarySign) ∨
    (selectedSlot = rightSecondSlot ∧ selectedSign = secondBoundarySign)
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
  selected_exterior_cells : (pieces selectedSlot selectedSign).cells =
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).cells
  selected_exterior_empty_anchor :
    (pieces selectedSlot selectedSign).cells = ∅ ->
      (pieces selectedSlot selectedSign).anchor =
        (SubtileOccurrenceInterpretation layout.P layout.u layout.v
          exteriorIndex).anchor
  selected_exterior_footprint :
    FootprintVertices (pieces selectedSlot selectedSign) = FootprintVertices
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v exteriorIndex)
  selected_exterior_domain :
    ((functions selectedSlot selectedSign).domain : Set GaussianInt) =
      FootprintVertices
        (SubtileOccurrenceInterpretation layout.P layout.u layout.v exteriorIndex)
  exterior_routed_cell : LatticeVertexIncidentCell point routedDirection ∈
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).cells
  central_routed_cell : LatticeVertexIncidentCell point
    (routedDirection + 2) ∈
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        centralIndex).cells
  selected_star : forall y,
    y = point ∨ y = point + 1 ∨ y = point - 1 ∨
      y = point + ⟨0, 1⟩ ∨ y = point - ⟨0, 1⟩ ->
    y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation layout.P layout.u layout.v exteriorIndex) ∨
      y ∈ FootprintVertices
        (SubtileOccurrenceInterpretation layout.P layout.u layout.v centralIndex)

end ApollonianSuperharmonic

end
