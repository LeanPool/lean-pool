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
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent

-- [TABLET NODE: BandOrderedGeneralSubtileNormalizationCertificate]

/-!
# BandOrderedGeneralSubtileNormalizationCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For the supplied proper presentation $q$ of a subtile-lattice pair
$(C_0,C_i,T_0,T_i,h_0,h_i)$, a subtile normalization certificate records
one cyclic parent rotation and one packing-symmetry word, the resulting
ordered-general presentation, transformed circles, literal supports,
functions, point, and slopes, and the transported subtile adjacency.  It
retains the transformed parent slot and quarter-turn index and the literal
parent-coordinate, centroid, and two slope equations returned by transport.
It contains one ordered-general layout rooted at the transformed $T_0$, a
centered quarter-turn symmetry of that root, and one reindexed six-piece
decomposition of its transformed odometer.

The certificate assigns each of the six decomposition pieces to one of the
six central periodic occurrences and records equality of cells, conditional
equality of empty anchors, equality of footprints, and equality of function
domains.  It also assigns the transformed fixed support to one of the twelve
exterior occurrences
$$
 A_{-1,-1},A_{0,-1},C_{1,0},C_{1,1},E_{0,1},E_{-1,0},
 B_{1,1},B_{0,1},D_{-1,0},D_{-1,-1},F_{0,-1},F_{1,0}
$$
with cell and conditional empty-anchor equality.  Finally it retains the
transformed point in both function domains and the transported five-point
footprint cover.  It contains no outer-interface record and makes no choice
of a decomposition piece.
-/
structure BandOrderedGeneralSubtileNormalizationCertificate
    (C₀ Cᵢ : BandCircle) (q : Fin 4 → CircleCoordinates)
    (i : Fin 3) (T₀ Tᵢ : ProtoTile)
    (h₀ hᵢ : PartialOdometer) (x : GaussianInt) where
-- BODY
  presentation_proper : ProperBandQuadruple q
  presentation_child : q 0 = C₀.1.1
  presentation_parent : q i.succ = Cᵢ.1.1
  /-- The cyclic parent rotation used before applying the packing symmetry. -/
  parentRotation : Fin 3
  /-- The single packing-symmetry word used throughout the normalization. -/
  symmetry : BandPackingSymmetry
  /-- The source presentation after the chosen cyclic parent rotation. -/
  rotatedPresentation : Fin 4 → CircleCoordinates
  rotated_presentation_eq : rotatedPresentation =
    ![q 0, q parentRotation.succ, q (parentRotation + 1).succ,
      q (parentRotation + 2).succ]
  /-- The ordered-general presentation obtained by the symmetry action. -/
  normalizedPresentation : Fin 4 → CircleCoordinates
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
    BandPackingSymmetryCircleAction symmetry Cᵢ.1.1
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
  normalized_root_eq : normalizedRoot = BandPackingSymmetryTileAction symmetry T₀
  normalized_fixed_eq : normalizedFixed = BandPackingSymmetryTileAction symmetry Tᵢ
  normalized_root_function_eq : normalizedRootFunction =
    BandPackingSymmetryPartialOdometerAction symmetry h₀
  normalized_fixed_function_eq : normalizedFixedFunction =
    BandPackingSymmetryPartialOdometerAction symmetry hᵢ
  normalized_point_eq : normalizedPoint =
    BandPackingSymmetryVectorAction symmetry x
  normalized_point_root_domain : normalizedPoint ∈ normalizedRootFunction.domain
  normalized_point_fixed_domain : normalizedPoint ∈ normalizedFixedFunction.domain
  normalized_root_odometer :
    TileOdometer (normalizedPresentation 0) normalizedRoot normalizedRootFunction
  normalized_fixed_odometer :
    TileOdometer normalizedFixedCircle.1.1 normalizedFixed normalizedFixedFunction
  /-- The defined slope of the transformed root odometer. -/
  normalizedRootSlope : ℝ × ℝ
  /-- The defined slope of the transformed fixed odometer. -/
  normalizedFixedSlope : ℝ × ℝ
  normalized_root_slope :
    PartialOdometerSlope normalizedRootFunction = some normalizedRootSlope
  normalized_fixed_slope :
    PartialOdometerSlope normalizedFixedFunction = some normalizedFixedSlope
  /-- The parent slot after transporting the supplied subtile adjacency. -/
  normalizedParentSlot : Fin 3
  /-- The transported quarter-turn index of that subtile-adjacency witness. -/
  normalizedQuarterTurn : Fin 4
  normalized_parent_coordinate :
    normalizedPresentation normalizedParentSlot.succ = normalizedFixedCircle.1.1
  normalized_adjacency_centroid :
    TileCentroid normalizedFixed - TileCentroid normalizedRoot =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ normalizedQuarterTurn.val *
          (BandVectors.1 (normalizedPresentation normalizedParentSlot.succ)
              (normalizedPresentation 0) +
            BandVectors.1 (normalizedPresentation 0)
              (normalizedPresentation normalizedParentSlot.succ)))
  normalized_adjacency_slope_real :
    normalizedFixedSlope.1 - normalizedRootSlope.1 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ normalizedQuarterTurn.val *
          (BandVectors.2 (normalizedPresentation normalizedParentSlot.succ)
              (normalizedPresentation 0) +
            BandVectors.2 (normalizedPresentation 0)
              (normalizedPresentation normalizedParentSlot.succ)))).1
  normalized_adjacency_slope_imag :
    normalizedFixedSlope.2 - normalizedRootSlope.2 =
      ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ normalizedQuarterTurn.val *
          (BandVectors.2 (normalizedPresentation normalizedParentSlot.succ)
              (normalizedPresentation 0) +
            BandVectors.2 (normalizedPresentation 0)
              (normalizedPresentation normalizedParentSlot.succ)))).2
  /-- The single family of six signed supports in the normalized root decomposition. -/
  pieces : Fin 3 → Bool → ProtoTile
  /-- The literal partial odometers on that same six-piece family. -/
  functions : Fin 3 → Bool → PartialOdometer
  root_band : BandPrototile (normalizedPresentation 0) normalizedRoot
  piece_odometer : ∀ j e, TileOdometer (normalizedPresentation j.succ)
    (pieces j e) (functions j e)
  piece_cell_cover : ∀ z, z ∈ normalizedRoot.cells ↔
    ∃ j e, z ∈ (pieces j e).cells
  piece_footprint : ∀ j e,
    FootprintVertices (pieces j e) ⊆ FootprintVertices normalizedRoot
  piece_centroid : ∀ j e,
    TileCentroid (pieces j e) - TileCentroid normalizedRoot =
      (if e = true then (1 : ℝ) else -1) •
        ((1 / 2 : ℝ) •
          (GaussianRealPoint
              (BandVectors.1 (normalizedPresentation ((j + 2).succ))
                (normalizedPresentation ((j + 1).succ))) -
            (-((GaussianRealPoint
                (BandVectors.1 (normalizedPresentation ((j + 2).succ))
                  (normalizedPresentation ((j + 1).succ)))).2),
              (GaussianRealPoint
                (BandVectors.1 (normalizedPresentation ((j + 2).succ))
                  (normalizedPresentation ((j + 1).succ)))).1)))
  function_domain_cover : ∀ z, z ∈ normalizedRootFunction.domain ↔
    ∃ j e, z ∈ (functions j e).domain
  function_restriction : ∀ j e z, z ∈ (functions j e).domain →
    normalizedRootFunction.value z = (functions j e).value z
  function_compatibility : ∀ j e k t,
    OdometerCompatibility (functions j e) (functions k t)
  piece_slope : ∀ j e, (normalizedPresentation j.succ).1 = 0 ∨
    ∃ p p_j : ℝ × ℝ,
      PartialOdometerSlope normalizedRootFunction = some p ∧
      PartialOdometerSlope (functions j e) = some p_j ∧
      p_j.1 - p.1 =
        (if e = true then (1 : ℝ) else -1) * (1 / 2) *
          (((BandVectors.2 (normalizedPresentation ((j + 2).succ))
            (normalizedPresentation ((j + 1).succ))).re : ℤ) -
           ((BandVectors.2 (normalizedPresentation ((j + 2).succ))
            (normalizedPresentation ((j + 1).succ))).im : ℤ)) ∧
      p_j.2 - p.2 =
        (if e = true then (1 : ℝ) else -1) * (1 / 2) *
          (((BandVectors.2 (normalizedPresentation ((j + 2).succ))
            (normalizedPresentation ((j + 1).succ))).im : ℤ) +
           ((BandVectors.2 (normalizedPresentation ((j + 2).succ))
            (normalizedPresentation ((j + 1).succ))).re : ℤ))
  adjacency : SubtileLatticeAdjacent normalizedCircle normalizedFixedCircle
    normalizedRoot normalizedFixed normalizedRootFunction normalizedFixedFunction
  root_quarter_turn : QuarterTurnSymmetric normalizedRoot
  /-- The literal ordered-general layout rooted at the normalized decomposed root tile. -/
  layout : BandOrderedGeneralLayoutCertificate normalizedPresentation configuration
    normalizedCircle normalizedRoot
  /-- The central periodic occurrence index aligned with each signed decomposition piece. -/
  pieceIndex : Fin 3 → Bool → PeriodicSubtileIndex
  piece_index_central : ∀ j e,
    pieceIndex j e = ⟨.A, 0, 0⟩ ∨ pieceIndex j e = ⟨.B, 0, 0⟩ ∨
    pieceIndex j e = ⟨.C, 0, 0⟩ ∨ pieceIndex j e = ⟨.D, 0, 0⟩ ∨
    pieceIndex j e = ⟨.E, 0, 0⟩ ∨ pieceIndex j e = ⟨.F, 0, 0⟩
  piece_layout_cells : ∀ j e, (pieces j e).cells =
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      (pieceIndex j e)).cells
  piece_layout_empty_anchor : ∀ j e, (pieces j e).cells = ∅ →
    (pieces j e).anchor =
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex j e)).anchor
  piece_layout_footprint : ∀ j e,
    FootprintVertices (pieces j e) = FootprintVertices
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex j e))
  piece_layout_domain : ∀ j e,
    ((functions j e).domain : Set GaussianInt) = FootprintVertices
      (SubtileOccurrenceInterpretation layout.P layout.u layout.v
        (pieceIndex j e))
  /-- The literal exterior occurrence aligned with the entire normalized fixed support. -/
  exteriorIndex : PeriodicSubtileIndex
  exterior_index :
    exteriorIndex = ⟨.A, -1, -1⟩ ∨ exteriorIndex = ⟨.A, 0, -1⟩ ∨
    exteriorIndex = ⟨.C, 1, 0⟩ ∨ exteriorIndex = ⟨.C, 1, 1⟩ ∨
    exteriorIndex = ⟨.E, 0, 1⟩ ∨ exteriorIndex = ⟨.E, -1, 0⟩ ∨
    exteriorIndex = ⟨.B, 1, 1⟩ ∨ exteriorIndex = ⟨.B, 0, 1⟩ ∨
    exteriorIndex = ⟨.D, -1, 0⟩ ∨ exteriorIndex = ⟨.D, -1, -1⟩ ∨
    exteriorIndex = ⟨.F, 0, -1⟩ ∨ exteriorIndex = ⟨.F, 1, 0⟩
  fixed_exterior_cells :
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).cells = normalizedFixed.cells
  fixed_exterior_empty_anchor :
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).cells = ∅ →
    (SubtileOccurrenceInterpretation layout.P layout.u layout.v
      exteriorIndex).anchor = normalizedFixed.anchor
  normalized_star : ∀ y,
    y = normalizedPoint ∨ y = normalizedPoint + 1 ∨
      y = normalizedPoint - 1 ∨ y = normalizedPoint + ⟨0, 1⟩ ∨
      y = normalizedPoint - ⟨0, 1⟩ →
    y ∈ FootprintVertices normalizedRoot ∨
      y ∈ FootprintVertices normalizedFixed

end ApollonianSuperharmonic

end
