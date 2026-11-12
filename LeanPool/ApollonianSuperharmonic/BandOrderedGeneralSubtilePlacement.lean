/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation

-- [TABLET NODE: BandOrderedGeneralSubtilePlacement]

/-!
# BandOrderedGeneralSubtilePlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix an ordered-general presentation $q$, its configuration, a normalized
subtile-adjacent pair $(\bar T,\bar h),(\bar N,\bar k)$, an externally
supplied family $(S_i^e,f_i^e)$ of six supports and partial odometers, a
selected slot, the normalized contact point, and its routed
incident-square direction.  A *subtile-adjacent normalized placement*
consists of the following data.  This record imposes only the
branch-specific adjacency, literal layout root, occurrence-index roles,
cells, empty-anchor, footprint, and domain alignments, routed memberships,
star cover, and fixed-to-exterior observable alignment listed below.  The
tile-odometer facts, cell and domain covers, restriction values,
compatibility, centroid formulas, and slope alternatives for
$(S_i^e,f_i^e)$ are not fields of this record; they are supplied once by
the enclosing normalized routed occurrence bundle.

It contains the transported directed subtile-lattice adjacency and one
`BandOrderedGeneralLayoutCertificate` whose root is literally the
decomposed full tile $\bar T$.  Each of the six pieces $S_i^e$ is aligned,
in cells, empty-case anchor, footprint, and function domain, with a literal
occurrence in this layout, and every one of those six indices is one of the
six central indices.  The selected piece index is the retained central
index $b$.  A retained exterior index $a$ is one of the twelve exterior
indices; its occurrence has exactly the cells of the fixed tile $\bar N$
and the same anchor when this cell set is empty.  The occurrences at $a$
and $b$ contain the two routed opposite squares and their footprints cover
the five axial vertices at the normalized contact point, as derived from
those squares.  In particular, no decomposed piece is forced to play an
exterior role in this branch.
-/
structure BandOrderedGeneralSubtilePlacement
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C0 fixedCircle : BandCircle)
    (root fixed : ProtoTile) (rootFunction fixedFunction : PartialOdometer)
    (point : GaussianInt) (pieces : Fin 3 -> Bool -> ProtoTile)
    (functions : Fin 3 -> Bool -> PartialOdometer)
    (selectedSlot : Fin 3) (selectedSign : Bool)
    (routedDirection : Fin 4) where
-- BODY
  adjacency : SubtileLatticeAdjacent C0 fixedCircle root fixed
    rootFunction fixedFunction
  /-- The literal ordered-general layout rooted at the normalized decomposed root tile. -/
  layout : BandOrderedGeneralLayoutCertificate q cfg C0 root
  /-- The central periodic occurrence index aligned with each signed decomposition piece. -/
  pieceIndex : Fin 3 -> Bool -> PeriodicSubtileIndex
  piece_index_central : forall i s,
    pieceIndex i s = ⟨.A, 0, 0⟩ ∨ pieceIndex i s = ⟨.B, 0, 0⟩ ∨
    pieceIndex i s = ⟨.C, 0, 0⟩ ∨ pieceIndex i s = ⟨.D, 0, 0⟩ ∨
    pieceIndex i s = ⟨.E, 0, 0⟩ ∨ pieceIndex i s = ⟨.F, 0, 0⟩
  piece_layout_cells : forall i s, (pieces i s).cells =
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      (pieceIndex i s)).cells
  piece_layout_empty_anchor : forall i s, (pieces i s).cells = ∅ ->
    (pieces i s).anchor =
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex i s)).anchor
  piece_layout_footprint : forall i s,
    FootprintVertices (pieces i s) = FootprintVertices
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex i s))
  piece_layout_domain : forall i s,
    ((functions i s).domain : Set GaussianInt) = FootprintVertices
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex i s))
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
  selected_central_index : centralIndex = pieceIndex selectedSlot selectedSign
  fixed_exterior_cells :
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).cells = fixed.cells
  fixed_exterior_empty_anchor :
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).cells = ∅ ->
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).anchor = fixed.anchor
  exterior_routed_cell : LatticeVertexIncidentCell point
    (routedDirection + 2) ∈
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        exteriorIndex).cells
  central_routed_cell : LatticeVertexIncidentCell point routedDirection ∈
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
