/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5630T1MarkedRightOdometerAdjacencyReduction
public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.BandOriginalOccurrenceIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralChildInterfaces
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayout
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralMarkedSectorTransport
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRoutedSelectedContact
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightOuterMarkingCriterion
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightSelectedAdjacency
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightSelectedRowGeometry
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightNormalizedBundleExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRowExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileSelectedRowGeometry
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileNormalizedBundleExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralMixedAggregatePatches
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryInversePhaseCancellation
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryMarkedDataCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetrySlopeAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.CoveredInterfaceOppositeIncidentCells
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.LatticeAdjacentInterfacePath
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.LatticeTileThreeDiskJunction
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TileSubodometer
public import LeanPool.ApollonianSuperharmonic.TileTouchingCovariance
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: MarkedOdometerAdjacencyReduction]

/-!
# MarkedOdometerAdjacencyReduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MarkedAdjacencyGeometry

private theorem hparentPositiveAt344 :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (q
            i.succ = Cᵢ.1.1) → (0 < (q i.succ).1) ) := by
  classical
  intro Cᵢ q i hqᵢ
  rw [hqᵢ]
  exact Cᵢ.property

private theorem hO₀q :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T₀ : ProtoTile), ∀ (h₀ :
            PartialOdometer), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → ((TileOdometer C₀.1.1 T₀ h₀) →
            (TileOdometer (q 0) T₀ h₀)) ) := by
  classical
  intro C₀ q T₀ h₀ hq₀ hO₀
  rw [hq₀]
  exact hO₀

private theorem hOᵢq :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (Tᵢ
            : ProtoTile), ∀ (hᵢ : PartialOdometer), (q i.succ = Cᵢ.1.1) → ((TileOdometer Cᵢ.1.1
            Tᵢ hᵢ) → (TileOdometer (q i.succ) Tᵢ hᵢ)) ) := by
  classical
  intro Cᵢ q i Tᵢ hᵢ hqᵢ hOᵢ
  rw [hqᵢ]
  exact hOᵢ

private theorem hnormAt360 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        bundle.normalizedCircle.1.1 = BandPackingSymmetryCircleAction g C₀.1.1 ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle g
  calc
    bundle.normalizedCircle.1.1 = bundle.normalizedPresentation 0 :=
      bundle.normalized_circle_eq.symm
    _ = BandPackingSymmetryCircleAction g C₀.1.1 := by
      rw [bundle.normalized_presentation_eq, bundle.rotated_presentation_eq]
      simp [g, BandPackingSymmetryQuadrupleAction,
        bundle.presentation_child]

private theorem hr₀ :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T₀
            : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ : PartialOdometer),
            ∀ (x : GaussianInt), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → (∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        (bundle.normalizedCircle.1.1 = BandPackingSymmetryCircleAction g C₀.1.1) →
            (normalizationPresentation 0 = bundle.normalizedCircle.1.1)) ) := by
  classical
  intro C₀ Cᵢ q T₀ Tᵢ h₀ hᵢ x hq₀ bundle g normalizationPresentation hnorm
  calc
    normalizationPresentation 0 = BandPackingSymmetryCircleAction g C₀.1.1 := by
      simp [normalizationPresentation, BandPackingSymmetryQuadrupleAction, hq₀]
    _ = bundle.normalizedCircle.1.1 := by simpa [g] using hnorm.symm

private theorem hrᵢ :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (p₀ : ℝ × ℝ), ∀
            (pᵢ : ℝ × ℝ), (q i.succ = Cᵢ.1.1) → ((TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ)
            • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1
            (q i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))))
            → ((pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)))).1) → ((pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) •
            GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑s : ℕ) * (BandVectors.2
            (q i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            i.succ)))).2) → (∀ (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ
            h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        (0 < (q i.succ).1) → ((TileOdometer (q i.succ) Tᵢ hᵢ) → (∀ (transportedRootSlope : ℝ ×
            ℝ), ∀ (transportedFixedSlope : ℝ × ℝ), ∀ (transportedRotation : Fin (4 : ℕ)),
            (TileOdometer (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryTileAction g Tᵢ) (BandPackingSymmetryPartialOdometerAction g hᵢ))
            → ((TileCentroid (BandPackingSymmetryTileAction g Tᵢ) - TileCentroid
            (BandPackingSymmetryTileAction g T₀) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ^ (↑transportedRotation : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) + BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))) →
            ((transportedFixedSlope.1 - transportedRootSlope.1 = ((1 / 2 : ℝ) • GaussianRealPoint
            ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑transportedRotation : ℕ) * (BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))).1) →
            ((transportedFixedSlope.2 - transportedRootSlope.2 = ((1 / 2 : ℝ) • GaussianRealPoint
            ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑transportedRotation : ℕ) * (BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))).2) →
            (normalizationPresentation (sigma i).succ =
            bundle.normalizedFixedCircle.1.1)))))))))) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x p₀ pᵢ hqᵢ hcentroid hslopex hslopey bundle g
      normalizationPresentation sigma hparentPositive hOᵢq transportedRootSlope
      transportedFixedSlope transportedRotation hfixedOdometer hcentroidForward hslopeXForward
      hslopeYForward
  have hact := congrArg (BandPackingSymmetryCircleAction g) hqᵢ
  have hcoord :
      (BandPackingSymmetryQuadrupleAction g q) (sigma i).succ =
        BandPackingSymmetryCircleAction g (q i.succ) := by
    cases hrev : BandPackingSymmetryReversesOrientation g <;>
      fin_cases i <;>
      simp [sigma, BandPackingSymmetryQuadrupleAction,
        hrev, Fin.neg_def,
        ]
  calc
    normalizationPresentation (sigma i).succ = BandPackingSymmetryCircleAction g (q i.succ)
        := by
      simpa [normalizationPresentation] using hcoord
    _ = BandPackingSymmetryCircleAction g Cᵢ.1.1 := hact
    _ = bundle.normalizedFixedCircle.1.1 := by
      simpa [g] using bundle.normalized_fixed_circle_eq.symm

private theorem htransportRootSlopeEq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        ∀ (transportedRootSlope : ℝ × ℝ), (PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction g h₀) = some transportedRootSlope) →
            (transportedRootSlope = bundle.normalizedRootSlope) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle g transportedRootSlope hrootSlope
  apply Option.some.inj
  rw [← hrootSlope, ← bundle.normalized_root_slope,
    bundle.normalized_root_function_eq]

private theorem htransportFixedSlopeEq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        ∀ (transportedFixedSlope : ℝ × ℝ), (PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction g hᵢ) = some transportedFixedSlope) →
            (transportedFixedSlope = bundle.normalizedFixedSlope) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle g transportedFixedSlope hfixedSlope
  apply Option.some.inj
  rw [← hfixedSlope, ← bundle.normalized_fixed_slope,
    bundle.normalized_fixed_function_eq]

private theorem hnormalizedCentroid :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (transportedRotation : Fin (4 : ℕ)), (TileCentroid (BandPackingSymmetryTileAction g Tᵢ)
            - TileCentroid (BandPackingSymmetryTileAction g T₀) = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑transportedRotation : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) + BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))) →
            (TileCentroid bundle.normalizedFixed - TileCentroid bundle.normalizedRoot = (1 / 2 :
            ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ transportedRotation.val *
            (BandVectors.1 (normalizationPresentation (sigma i).succ) (normalizationPresentation
            0) + BandVectors.1 (normalizationPresentation 0) (normalizationPresentation (sigma
            i).succ)))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma transportedRotation
      hcentroidForward
  simpa [bundle.normalized_root_eq, bundle.normalized_fixed_eq] using hcentroidForward

private theorem hnormalizedSlopeX :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (transportedRootSlope : ℝ × ℝ), ∀ (transportedFixedSlope : ℝ × ℝ), ∀
            (transportedRotation : Fin (4 : ℕ)), (transportedFixedSlope.1 -
            transportedRootSlope.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑transportedRotation : ℕ) * (BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))).1) →
            ((transportedRootSlope = bundle.normalizedRootSlope) → ((transportedFixedSlope =
            bundle.normalizedFixedSlope) → (bundle.normalizedFixedSlope.1 -
            bundle.normalizedRootSlope.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ transportedRotation.val * (BandVectors.2 (normalizationPresentation
            (sigma i).succ) (normalizationPresentation 0) + BandVectors.2
            (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)))).1))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma transportedRootSlope
      transportedFixedSlope transportedRotation hslopeXForward htransportRootSlopeEq
      htransportFixedSlopeEq
  simpa [htransportRootSlopeEq, htransportFixedSlopeEq] using hslopeXForward

private theorem hnormalizedSlopeY :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (transportedRootSlope : ℝ × ℝ), ∀ (transportedFixedSlope : ℝ × ℝ), ∀
            (transportedRotation : Fin (4 : ℕ)), (transportedFixedSlope.2 -
            transportedRootSlope.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑transportedRotation : ℕ) * (BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -j else j) i).succ)))).2) →
            ((transportedRootSlope = bundle.normalizedRootSlope) → ((transportedFixedSlope =
            bundle.normalizedFixedSlope) → (bundle.normalizedFixedSlope.2 -
            bundle.normalizedRootSlope.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ transportedRotation.val * (BandVectors.2 (normalizationPresentation
            (sigma i).succ) (normalizationPresentation 0) + BandVectors.2
            (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)))).2))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma transportedRootSlope
      transportedFixedSlope transportedRotation hslopeYForward htransportRootSlopeEq
      htransportFixedSlopeEq
  simpa [htransportRootSlopeEq, htransportFixedSlopeEq] using hslopeYForward

private theorem hrowUR :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (delta : Bool), ∀ (transportedRotation : Fin (4 : ℕ)), (transportedRotation = if
            BandPackingSymmetryReversesOrientation g = true then -s - (1 : Fin (4 : ℕ)) + if
            delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s + if delta = true
            then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) → (
        let rowUR := TileTranslation bundle.normalizedRoot
          ((⟨0, 1⟩ : GaussianInt) ^ transportedRotation.val *
            (if Even transportedRotation.val then
              BandVectors.1 (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)
            else BandVectors.1 (normalizationPresentation (sigma i).succ) (normalizationPresentation
                0)))
        rowUR = TileTranslation (BandPackingSymmetryTileAction g T₀) ((⟨0, 1⟩ : GaussianInt) ^
            (if BandPackingSymmetryReversesOrientation g then -s - 1 + (if delta then (2 : Fin 4)
            else 0) else s + (if delta then (2 : Fin 4) else 0)).val * (if Even (if
            BandPackingSymmetryReversesOrientation g then -s - 1 + (if delta then (2 : Fin 4)
            else 0) else s + (if delta then (2 : Fin 4) else 0)).val then BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q 0) (BandPackingSymmetryQuadrupleAction g q
            (sigma i).succ) else BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (sigma
            i).succ) (BandPackingSymmetryQuadrupleAction g q 0)))) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma delta
      transportedRotation hrotationForward rowUR
  dsimp [rowUR]
  rw [bundle.normalized_root_eq, hrotationForward]

private theorem hmarkedOld :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (delta : Bool), ∀ (transportedRotation : Fin (4 : ℕ)),
        let oldUR := TileTranslation T₀
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)))
        let rowUR := TileTranslation bundle.normalizedRoot
          ((⟨0, 1⟩ : GaussianInt) ^ transportedRotation.val *
            (if Even transportedRotation.val then
              BandVectors.1 (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)
            else BandVectors.1 (normalizationPresentation (sigma i).succ) (normalizationPresentation
                0)))
        (
        let q' := BandPackingSymmetryQuadrupleAction g q;
        let sigma := fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j;
        let s' := if BandPackingSymmetryReversesOrientation g = true then -s - (1 : Fin (4 : ℕ))
            + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s + if delta =
            true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ));
        let oldRight := TileTranslation T₀ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if
            Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1
            (q i.succ) (q (0 : Fin (4 : ℕ))));
        let newRight := TileTranslation (BandPackingSymmetryTileAction g T₀) ((⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt) ^ (↑s' : ℕ) * if Even (↑s' : ℕ) then BandVectors.1 (q' (0 : Fin (4 :
            ℕ))) (q' (sigma i).succ) else BandVectors.1 (q' (sigma i).succ) (q' (0 : Fin (4 :
            ℕ)))); BandPackingSymmetryTileAction g oldRight = newRight ∧ (x ∈ FootprintVertices
            oldRight ↔ BandPackingSymmetryVectorAction g x ∈ FootprintVertices newRight)) →
            ((rowUR = TileTranslation (BandPackingSymmetryTileAction g T₀) ((⟨0, 1⟩ :
            GaussianInt) ^ (if BandPackingSymmetryReversesOrientation g then -s - 1 + (if delta
            then (2 : Fin 4) else 0) else s + (if delta then (2 : Fin 4) else 0)).val * (if Even
            (if BandPackingSymmetryReversesOrientation g then -s - 1 + (if delta then (2 : Fin 4)
            else 0) else s + (if delta then (2 : Fin 4) else 0)).val then BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q 0) (BandPackingSymmetryQuadrupleAction g q
            (sigma i).succ) else BandVectors.1 (BandPackingSymmetryQuadrupleAction g q (sigma
            i).succ) (BandPackingSymmetryQuadrupleAction g q 0)))) → (x ∈ FootprintVertices oldUR
            ↔ bundle.normalizedPoint ∈ FootprintVertices rowUR)) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma delta
      transportedRotation oldUR rowUR hmarkedTransport hrowUR
  calc
    x ∈ FootprintVertices oldUR ↔
        BandPackingSymmetryVectorAction g x ∈
          FootprintVertices
            (TileTranslation (BandPackingSymmetryTileAction g T₀)
              ((⟨0, 1⟩ : GaussianInt) ^
                (if BandPackingSymmetryReversesOrientation g then
                  -s - 1 + (if delta then (2 : Fin 4) else 0)
                else s + (if delta then (2 : Fin 4) else 0)).val *
                (if Even
                    (if BandPackingSymmetryReversesOrientation g then
                      -s - 1 + (if delta then (2 : Fin 4) else 0)
                    else s + (if delta then (2 : Fin 4) else 0)).val then
                  BandVectors.1 (BandPackingSymmetryQuadrupleAction g q 0)
                    (BandPackingSymmetryQuadrupleAction g q (sigma i).succ)
                else BandVectors.1
                  (BandPackingSymmetryQuadrupleAction g q (sigma i).succ)
                  (BandPackingSymmetryQuadrupleAction g q 0)))) :=
      by simpa [oldUR] using hmarkedTransport.2
    _ ↔ bundle.normalizedPoint ∈ FootprintVertices rowUR := by
      rw [← bundle.normalized_point_eq, ← hrowUR]

private theorem hnormalizedOrbit :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), (¬((∃ (g :
            BandPackingSymmetry) (P : FordFareyParameter), BandPackingSymmetryCircleAction g
            (FordCircleCoordinate P.p P.q) = C₀.1.1) ∨ ∃ (g : BandPackingSymmetry) (K :
            DiamondParameter), BandPackingSymmetryCircleAction g (DiamondRecursiveQuadruple K (0
            : Fin (4 : ℕ))) = C₀.1.1)) → (∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ¬ ((∃ (g :
            BandPackingSymmetry) (P : FordFareyParameter), BandPackingSymmetryCircleAction g
            (FordCircleCoordinate P.p P.q) = bundle.normalizedCircle.1.1) ∨ (∃ (g :
            BandPackingSymmetry) (K : DiamondParameter), BandPackingSymmetryCircleAction g
            (DiamondRecursiveQuadruple K 0) = bundle.normalizedCircle.1.1))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x horbit bundle
  have hnorm : bundle.normalizedCircle.1.1 =
      BandPackingSymmetryCircleAction bundle.symmetry C₀.1.1 := by
    calc
      bundle.normalizedCircle.1.1 = bundle.normalizedPresentation 0 :=
        bundle.normalized_circle_eq.symm
      _ = BandPackingSymmetryCircleAction bundle.symmetry C₀.1.1 := by
        rw [bundle.normalized_presentation_eq, bundle.rotated_presentation_eq]
        simp [BandPackingSymmetryQuadrupleAction,
          bundle.presentation_child]
  obtain ⟨ginv, hcircleL, hcircleR, hquadL, hquadR, htileL,
    htileR, hvecL, hvecR, hfunL, hfunR, hphase⟩ :=
    (BandPackingSymmetryInversePhaseCancellation.2 bundle.symmetry)
  intro horbit'
  rcases horbit' with ⟨g, P, hP⟩ | ⟨g, K, hK⟩
  · apply horbit
    left
    refine ⟨.comp ginv g, P, ?_⟩
    rw [hnorm] at hP
    change BandPackingSymmetryCircleAction ginv
        (BandPackingSymmetryCircleAction g
          (FordCircleCoordinate P.p P.q)) = C₀.1.1
    rw [hP]
    exact hcircleL C₀.1.1
  · apply horbit
    right
    refine ⟨.comp ginv g, K, ?_⟩
    rw [hnorm] at hK
    change BandPackingSymmetryCircleAction ginv
        (BandPackingSymmetryCircleAction g
          (DiamondRecursiveQuadruple K 0)) = C₀.1.1
    rw [hK]
    exact hcircleL C₀.1.1

private theorem hnormAt536 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
            bundle.normalizedCircle.1.1 = BandPackingSymmetryCircleAction bundle.symmetry C₀.1.1
            ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle
  calc
    bundle.normalizedCircle.1.1 = bundle.normalizedPresentation 0 :=
      bundle.normalized_circle_eq.symm
    _ = BandPackingSymmetryCircleAction bundle.symmetry C₀.1.1 := by
      rw [bundle.normalized_presentation_eq, bundle.rotated_presentation_eq]
      simp [BandPackingSymmetryQuadrupleAction,
        bundle.presentation_child]

private theorem actionCurvature :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (c : CircleCoordinates), (BandPackingSymmetryCircleAction
            g c).1 = c.1 ) := by
  classical
  intro g
  induction g with
  | identity => intro c; rfl
  | negate => intro c; rfl
  | conjugate => intro c; rfl
  | shift w => intro c; rfl
  | comp a b iha ihb => intro c; simp [BandPackingSymmetryCircleAction, iha, ihb]

private theorem hinverseCoordinate :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (C' :
            BandCircle), (C'.1.1 = bundle.normalizedPresentation bundle.selectedSlot.succ) → (∀
            (ginv : BandPackingSymmetry),
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        inversePresentation inverseSlot.succ = BandPackingSymmetryCircleAction ginv C'.1.1) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C' hC' ginv inversePresentation inverseSlot
  unfold inversePresentation inverseSlot
  rw [hC']
  generalize hidx : bundle.selectedSlot = j
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  by_cases hrev : BandPackingSymmetryReversesOrientation ginv <;>
    fin_cases j <;>
    simp [BandPackingSymmetryQuadrupleAction,
      hrev, neg1, neg2];

private theorem hinversePositive :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (C' :
            BandCircle), ∀ (ginv : BandPackingSymmetry), (∀ (g : BandPackingSymmetry), ∀ (c :
            CircleCoordinates), (BandPackingSymmetryCircleAction g c).1 = c.1) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        (inversePresentation inverseSlot.succ = BandPackingSymmetryCircleAction ginv C'.1.1) → (0
            < (inversePresentation inverseSlot.succ).1)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C' ginv actionCurvature inversePresentation inverseSlot
      hinverseCoordinate
  rw [hinverseCoordinate, actionCurvature]
  exact C'.property

private theorem hsubNormalized :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
            (bundle.normalizedCircle.1.1 = BandPackingSymmetryCircleAction bundle.symmetry
            C₀.1.1) → (∀ (C' : BandCircle), (TileSubodometer bundle.normalizedCircle.1.1 C'.1.1
                bundle.normalizedRoot (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) bundle.normalizedRootFunction
            (bundle.functions bundle.selectedSlot bundle.selectedSign)) → (TileSubodometer
            (BandPackingSymmetryCircleAction bundle.symmetry C₀.1.1) C'.1.1
            (BandPackingSymmetryTileAction bundle.symmetry T₀) (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) (BandPackingSymmetryPartialOdometerAction bundle.symmetry h₀)
            (bundle.functions bundle.selectedSlot bundle.selectedSign))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hnorm C' hsub'
  simpa [hnorm, bundle.normalized_root_eq,
    bundle.normalized_root_function_eq] using hsub'

private theorem hsubInverse :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        ((∀ (g : BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (C' : CircleCoordinates), ∀
            (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), TileSubodometer C C' T T' h h' ↔ TileSubodometer
            (BandPackingSymmetryCircleAction g C) (BandPackingSymmetryCircleAction g C')
            (BandPackingSymmetryTileAction g T) (BandPackingSymmetryTileAction g T')
            (BandPackingSymmetryPartialOdometerAction g h)
            (BandPackingSymmetryPartialOdometerAction g h')) ∧ (∀ (g : BandPackingSymmetry), ∀ (x
            : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j ∈ U.cells) ↔
            ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell (BandPackingSymmetryVectorAction g x)
            j ∈ (BandPackingSymmetryTileAction g T).cells ∨ LatticeVertexIncidentCell
            (BandPackingSymmetryVectorAction g x) j ∈ (BandPackingSymmetryTileAction g U).cells)
            ∧ ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            ProperBandQuadruple q → ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (delta : Bool),
            BandPackingSymmetryScopedPhase g q delta → ∀ (T : ProtoTile), ∀ (x : GaussianInt),
        let q' := BandPackingSymmetryQuadrupleAction g q;
        let sigma := fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j;
        let s' := if BandPackingSymmetryReversesOrientation g = true then -s - (1 : Fin (4 : ℕ))
            + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s + if delta =
            true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ));
        let oldRight := TileTranslation T ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if
            Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1
            (q i.succ) (q (0 : Fin (4 : ℕ))));
        let newRight := TileTranslation (BandPackingSymmetryTileAction g T) ((⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt) ^ (↑s' : ℕ) * if Even (↑s' : ℕ) then BandVectors.1 (q' (0 : Fin (4 :
            ℕ))) (q' (sigma i).succ) else BandVectors.1 (q' (sigma i).succ) (q' (0 : Fin (4 :
            ℕ)))); BandPackingSymmetryTileAction g oldRight = newRight ∧ (x ∈ FootprintVertices
            oldRight ↔ BandPackingSymmetryVectorAction g x ∈ FootprintVertices newRight)) → (∀
            (C' : BandCircle), ∀ (ginv : BandPackingSymmetry), (∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction ginv (BandPackingSymmetryCircleAction bundle.symmetry
            C) = C) → ((∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → ((∀ (h : PartialOdometer),
            BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → ((TileSubodometer
            (BandPackingSymmetryCircleAction bundle.symmetry C₀.1.1) C'.1.1
            (BandPackingSymmetryTileAction bundle.symmetry T₀) (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) (BandPackingSymmetryPartialOdometerAction bundle.symmetry h₀)
            (bundle.functions bundle.selectedSlot bundle.selectedSign)) → (TileSubodometer C₀.1.1
            inverseCircle.1.1 T₀ (BandPackingSymmetryTileAction ginv (bundle.pieces
            bundle.selectedSlot bundle.selectedSign)) h₀
            (BandPackingSymmetryPartialOdometerAction ginv (bundle.functions bundle.selectedSlot
            bundle.selectedSign)))))))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle markedData C' ginv hcircleL htileL hfunL inversePresentation
      inverseSlot hinverseProper hinversePositive inverseCircle hinverseCircle hsubNormalized
  let g := bundle.symmetry
  let sigma : Fin 3 → Fin 3 := fun j =>
    if BandPackingSymmetryReversesOrientation g then -j else j
  have htransport :=
    (markedData.1 ginv
      (BandPackingSymmetryCircleAction bundle.symmetry C₀.1.1) C'.1.1
      (BandPackingSymmetryTileAction bundle.symmetry T₀)
      (bundle.pieces bundle.selectedSlot bundle.selectedSign)
      (BandPackingSymmetryPartialOdometerAction bundle.symmetry h₀)
      (bundle.functions bundle.selectedSlot bundle.selectedSign)).mp
      hsubNormalized
  simpa [hcircleL, htileL, hfunL, hinverseCircle] using htransport

private theorem inverseDomain :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (v : GaussianInt), BandPackingSymmetryVectorAction ginv
            (BandPackingSymmetryVectorAction bundle.symmetry v) = v) → (∀ (f : PartialOdometer),
            ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction bundle.symmetry y ∈ f.domain) →
            (y ∈ (BandPackingSymmetryPartialOdometerAction ginv f).domain)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv hvecL f y hy
  change y ∈ ((BandPackingSymmetryPartialOdometerAction ginv f).domain : Set GaussianInt)
  rw [(BandPackingSymmetryPartialOdometerActionFormulas ginv f f).1]
  exact ⟨BandPackingSymmetryVectorAction bundle.symmetry y, hy, hvecL y⟩

private theorem hxFixedOriginal :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
            (bundle.normalizedPoint ∈ bundle.normalizedFixedFunction.domain) → (∀ (ginv :
            BandPackingSymmetry), (∀ (h : PartialOdometer),
            BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → ((∀ (f :
            PartialOdometer), ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction
            bundle.symmetry y ∈ f.domain) → (y ∈ (BandPackingSymmetryPartialOdometerAction ginv
            f).domain)) → ((BandPackingSymmetryVectorAction bundle.symmetry x =
            bundle.normalizedPoint) → (x ∈ hᵢ.domain)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hxFixed' ginv hfunL inverseDomain hpoint
  have hmem : bundle.normalizedPoint ∈
      (BandPackingSymmetryPartialOdometerAction bundle.symmetry hᵢ).domain := by
    simpa [hpoint, bundle.normalized_fixed_function_eq] using hxFixed'
  have hback := inverseDomain
    (BandPackingSymmetryPartialOdometerAction bundle.symmetry hᵢ) x
    (by simpa [hpoint] using hmem)
  simpa [hfunL] using hback

private theorem hxSelectedOriginal :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
            (bundle.normalizedPoint ∈ (bundle.functions bundle.selectedSlot
            bundle.selectedSign).domain) → (∀ (ginv : BandPackingSymmetry),
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (∀ (f : PartialOdometer), ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction
            bundle.symmetry y ∈ f.domain) → (y ∈ (BandPackingSymmetryPartialOdometerAction ginv
            f).domain)) → ((BandPackingSymmetryVectorAction bundle.symmetry x =
            bundle.normalizedPoint) → (x ∈ h'.domain))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hxSelected' ginv selectedFunction h' inverseDomain hpoint
  have hmem : bundle.normalizedPoint ∈ selectedFunction.domain := hxSelected'
  have hback := inverseDomain selectedFunction x (by simpa [hpoint] using hmem)
  simpa [h'] using hback

private theorem mapStar :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (b = a ∨ b = a + 1
            ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → (BandPackingSymmetryVectorAction g b
            = BandPackingSymmetryVectorAction g a ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a + 1 ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a - 1 ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a + ⟨0, 1⟩ ∨ BandPackingSymmetryVectorAction g b =
            BandPackingSymmetryVectorAction g a - ⟨0, 1⟩) ) := by
  classical
  intro g
  induction g with
  | identity => intro a b hb; simpa [BandPackingSymmetryVectorAction] using hb
  | shift w => intro a b hb; simpa [BandPackingSymmetryVectorAction] using hb
  | negate =>
      intro a b hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b
        simp [BandPackingSymmetryVectorAction]
      · subst b
        right; right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
      · subst b
        right; right; right; right
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
      · subst b
        right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]; try ring
      · subst b
        right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]; try ring
  | conjugate =>
      intro a b hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b
        simp [BandPackingSymmetryVectorAction]
      · subst b
        right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]; try ring
      · subst b
        right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]; try ring
      · subst b
        right; right; right; left
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]
      · subst b
        right; right; right; right
        ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]
  | comp g₁ g₂ ih₁ ih₂ =>
      intro a b hb
      exact ih₁ _ _ (ih₂ _ _ hb)

private theorem hstarOriginal :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), (∀ (y :
            GaussianInt), y = bundle.normalizedPoint ∨ y = bundle.normalizedPoint + (1 :
            GaussianInt) ∨ y = bundle.normalizedPoint - (1 : GaussianInt) ∨ y =
            bundle.normalizedPoint + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y =
            bundle.normalizedPoint - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈
            bundle.normalizedFixedFunction.domain ∨ y ∈ (bundle.functions bundle.selectedSlot
            bundle.selectedSign).domain) → (∀ (ginv : BandPackingSymmetry), (∀ (h :
            PartialOdometer), BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → (
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (∀ (f : PartialOdometer), ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction
            bundle.symmetry y ∈ f.domain) → (y ∈ (BandPackingSymmetryPartialOdometerAction ginv
            f).domain)) → ((BandPackingSymmetryVectorAction bundle.symmetry x =
            bundle.normalizedPoint) → ((∀ (g : BandPackingSymmetry), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (b = a ∨ b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
            (BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a + 1 ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a - 1 ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a + ⟨0, 1⟩ ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a - ⟨0, 1⟩))
            → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈
            hᵢ.domain ∨ y ∈ h'.domain))))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hstar' ginv hfunL selectedFunction h' inverseDomain hpoint
      mapStar y hy
  have hnormalizedStar := mapStar bundle.symmetry x y hy
  rw [hpoint] at hnormalizedStar
  have hmem := hstar' (BandPackingSymmetryVectorAction bundle.symmetry y)
      hnormalizedStar
  rcases hmem with hfixed | hselected
  · left
    have hback := inverseDomain
      (BandPackingSymmetryPartialOdometerAction bundle.symmetry hᵢ) y (by
        simpa [bundle.normalized_fixed_function_eq] using hfixed)
    simpa [hfunL] using hback
  · right
    have hback := inverseDomain selectedFunction y hselected
    simpa [h'] using hback

private theorem hsizeOriginal :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
            (bundle.normalizedCircle.1.1 = BandPackingSymmetryCircleAction bundle.symmetry
            C₀.1.1) → (∀ (C' : BandCircle), (bundle.normalizedFixedCircle.1.1.1.toNat +
                C'.1.1.1.toNat <
            bundle.normalizedCircle.1.1.1.toNat +
            bundle.normalizedFixedCircle.1.1.1.toNat) →
            (∀ (ginv : BandPackingSymmetry), (∀ (g : BandPackingSymmetry), ∀ (c :
            CircleCoordinates), (BandPackingSymmetryCircleAction g c).1 = c.1) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (Int.toNat Cᵢ.1.1.1 +
            Int.toNat inverseCircle.1.1.1 < Int.toNat C₀.1.1.1 + Int.toNat Cᵢ.1.1.1)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hnorm C' hsize' ginv actionCurvature inversePresentation
      inverseSlot hinverseProper hinversePositive inverseCircle hinverseCircle
  have hleft : Cᵢ.1.1.1 = bundle.normalizedFixedCircle.1.1.1 := by
    rw [bundle.normalized_fixed_circle_eq]
    exact (actionCurvature bundle.symmetry Cᵢ.1.1).symm
  have hroot : C₀.1.1.1 = bundle.normalizedCircle.1.1.1 := by
    rw [hnorm]
    exact (actionCurvature bundle.symmetry C₀.1.1).symm
  have hchild : inverseCircle.1.1.1 = C'.1.1.1 := by
    rw [hinverseCircle]
    exact actionCurvature ginv C'.1.1
  rw [hleft, hroot, hchild]
  exact hsize'

private theorem hinverseCircleFixed :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (C' :
            BandCircle), ∀ (ginv : BandPackingSymmetry), (∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction ginv (BandPackingSymmetryCircleAction bundle.symmetry
            C) = C) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → ((C' =
            bundle.normalizedFixedCircle) → (inverseCircle = Cᵢ))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C' ginv hcircleL inversePresentation inverseSlot
      hinverseProper hinversePositive inverseCircle hinverseCircle hCfixed
  apply Subtype.ext
  apply Subtype.ext
  calc
    inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv
        bundle.normalizedFixedCircle.1.1 := by
          have htmp := hinverseCircle
          rw [hCfixed] at htmp
          exact htmp
    _ = BandPackingSymmetryCircleAction ginv
        (BandPackingSymmetryCircleAction bundle.symmetry Cᵢ.1.1) := by
          rw [bundle.normalized_fixed_circle_eq]
    _ = Cᵢ.1.1 := hcircleL Cᵢ.1.1

private theorem hnotOriginal :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (transportedRotation : Fin (4 : ℕ)),
        let oldUR := TileTranslation T₀
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)))
        let rowUR := TileTranslation bundle.normalizedRoot
          ((⟨0, 1⟩ : GaussianInt) ^ transportedRotation.val *
            (if Even transportedRotation.val then
              BandVectors.1 (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)
            else BandVectors.1 (normalizationPresentation (sigma i).succ) (normalizationPresentation
                0)))
        (x ∈ FootprintVertices oldUR ↔ bundle.normalizedPoint ∈ FootprintVertices rowUR) →
            ((bundle.normalizedPoint ∉ FootprintVertices (TileTranslation bundle.normalizedRoot
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑transportedRotation : ℕ) * if Even
            (↑transportedRotation : ℕ) then BandVectors.1 (normalizationPresentation (0 : Fin (4
            : ℕ))) (normalizationPresentation (sigma i).succ) else BandVectors.1
            (normalizationPresentation (sigma i).succ) (normalizationPresentation (0 : Fin (4 :
            ℕ)))))) → (x ∉ FootprintVertices oldUR)) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma transportedRotation
      oldUR rowUR hmarkedOld hnotMarked hx
  exact hnotMarked (hmarkedOld.mp hx)

private theorem hpFixedEq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (pFixed : ℝ ×
            ℝ), (PartialOdometerSlope bundle.normalizedFixedFunction = some pFixed) → (pFixed =
            bundle.normalizedFixedSlope) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle pFixed hslopeFixed
  apply Option.some.inj
  rw [← hslopeFixed, ← bundle.normalized_fixed_slope]

private theorem hpSelectedEq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (selectedSlope :
            ℝ × ℝ), (PartialOdometerSlope (bundle.functions bundle.selectedSlot
            bundle.selectedSign) = some selectedSlope) → (∀ (pSelected : ℝ × ℝ),
            (PartialOdometerSlope (bundle.functions bundle.selectedSlot bundle.selectedSign) =
            some pSelected) → (pSelected = selectedSlope)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle selectedSlope hslope' pSelected hslopeSelected
  apply Option.some.inj
  rw [← hslopeSelected, ← hslope']

private theorem centroidCov :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (w : GaussianInt),
            TileCentroid V - TileCentroid U = GaussianRealPoint w → TileCentroid
            (BandPackingSymmetryTileAction a V) - TileCentroid (BandPackingSymmetryTileAction a
            U) = GaussianRealPoint (BandPackingSymmetryVectorAction a w) ) := by
  classical
  intro a
  induction a with
  | identity => intro U V w hc; exact hc
  | shift z => intro U V w hc; exact hc
  | negate =>
      intro U V w hc
      change TileCentroid (TileQuarterTurn V) -
        TileCentroid (TileQuarterTurn U) = _
      rw [(TileQuarterTurnFormulas V).2.2.2.2.1,
        (TileQuarterTurnFormulas U).2.2.2.2.1]
      rcases w with ⟨wr, wi⟩
      have hc1 : (TileCentroid V).1 - (TileCentroid U).1 = wr := by
        simpa [GaussianRealPoint] using congrArg Prod.fst hc
      have hc2 : (TileCentroid V).2 - (TileCentroid U).2 = wi := by
        simpa [GaussianRealPoint] using congrArg Prod.snd hc
      apply Prod.ext
      · simp [GaussianRealPoint, BandPackingSymmetryVectorAction,
          GaussianQuarterTurn] at hc2 ⊢
        linarith
      · simp [GaussianRealPoint, BandPackingSymmetryVectorAction,
          GaussianQuarterTurn] at hc1 ⊢
        linarith
  | conjugate =>
      intro U V w hc
      change TileCentroid
          (TileQuarterTurn (TileQuarterTurn (TileReflection V))) -
        TileCentroid
          (TileQuarterTurn (TileQuarterTurn (TileReflection U))) = _
      rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileReflection V))).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn (TileReflection U))).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileReflection V)).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileReflection U)).2.2.2.2.1,
        (TileReflectionFormulas V).2.2.2.2.1,
        (TileReflectionFormulas U).2.2.2.2.1]
      rcases w with ⟨wr, wi⟩
      have hc1 : (TileCentroid V).1 - (TileCentroid U).1 = wr := by
        simpa [GaussianRealPoint] using congrArg Prod.fst hc
      have hc2 : (TileCentroid V).2 - (TileCentroid U).2 = wi := by
        simpa [GaussianRealPoint] using congrArg Prod.snd hc
      apply Prod.ext
      · simp [GaussianRealPoint, BandPackingSymmetryVectorAction,
          GaussianReflection] at hc2 ⊢
        linarith
      · simp [GaussianRealPoint, BandPackingSymmetryVectorAction,
          GaussianReflection] at hc1 ⊢
        linarith
  | comp a b iha ihb =>
      intro U V w hc
      exact iha _ _ _ (ihb U V w hc)

private theorem hinverseUnitCurv :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), (∀ (g :
            BandPackingSymmetry), ∀ (c : CircleCoordinates), (BandPackingSymmetryCircleAction g
            c).1 = c.1) → ((bundle.normalizedFixedCircle.1.1.1 = (1 : ℤ)) → (Cᵢ.1.1.1 = 1)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle actionCurvature hcurvUnit
  calc
    Cᵢ.1.1.1 =
        (BandPackingSymmetryCircleAction bundle.symmetry Cᵢ.1.1).1 :=
      (actionCurvature bundle.symmetry Cᵢ.1.1).symm
    _ = bundle.normalizedFixedCircle.1.1.1 := by
      rw [bundle.normalized_fixed_circle_eq]
    _ = 1 := hcurvUnit

private theorem hcentUnitInv :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        ∀ (v : GaussianInt), (TileCentroid (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) - TileCentroid bundle.normalizedFixed = GaussianRealPoint v) →
            ((∀ (a : BandPackingSymmetry), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (w :
            GaussianInt), TileCentroid V - TileCentroid U = GaussianRealPoint w → TileCentroid
            (BandPackingSymmetryTileAction a V) - TileCentroid (BandPackingSymmetryTileAction a
            U) = GaussianRealPoint (BandPackingSymmetryVectorAction a w)) → (TileCentroid T' -
            TileCentroid Tᵢ = GaussianRealPoint (BandPackingSymmetryVectorAction ginv v)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv htileL selectedSupport T' v hcentUnit centroidCov
  have hc := centroidCov ginv bundle.normalizedFixed selectedSupport v hcentUnit
  simpa [T', bundle.normalized_fixed_eq, htileL] using hc

private theorem unitStepCov :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (o : Bool), ∀ (w : GaussianInt), UnitTriangularStep o w →
            ∃ o', UnitTriangularStep o' (BandPackingSymmetryVectorAction a w) ) := by
  classical
  intro a
  let unitPositive :=
    ({1, -1, ⟨0, 1⟩, -⟨0, 1⟩, 1 + ⟨0, 1⟩,
      -(1 + ⟨0, 1⟩)} : Finset GaussianInt)
  let unitNegative :=
    ({1, -1, ⟨0, 1⟩, -⟨0, 1⟩, -1 + ⟨0, 1⟩,
      -(-1 + ⟨0, 1⟩)} : Finset GaussianInt)
  induction a with
  | identity => intro o w hw; exact ⟨o, by simpa [BandPackingSymmetryVectorAction] using hw⟩
  | shift z => intro o w hw; exact ⟨o, by simpa [BandPackingSymmetryVectorAction] using hw⟩
  | negate =>
      intro o w hw
      cases o with
      | false =>
          refine ⟨true, ?_⟩
          have hmap : unitNegative.image GaussianQuarterTurn = unitPositive := by
            decide
          change w ∈ unitNegative at hw
          have hm : GaussianQuarterTurn w ∈ unitNegative.image GaussianQuarterTurn :=
            Finset.mem_image.mpr ⟨w, hw, rfl⟩
          rw [hmap] at hm
          change GaussianQuarterTurn w ∈ unitPositive
          exact hm
      | true =>
          refine ⟨false, ?_⟩
          have hmap : unitPositive.image GaussianQuarterTurn = unitNegative := by
            decide
          change w ∈ unitPositive at hw
          have hm : GaussianQuarterTurn w ∈ unitPositive.image GaussianQuarterTurn :=
            Finset.mem_image.mpr ⟨w, hw, rfl⟩
          rw [hmap] at hm
          change GaussianQuarterTurn w ∈ unitNegative
          exact hm
  | conjugate =>
      intro o w hw
      cases o with
      | false =>
          refine ⟨true, ?_⟩
          have hmap : unitNegative.image (fun z => -GaussianReflection z) =
              unitPositive := by
            decide
          change w ∈ unitNegative at hw
          have hm : -GaussianReflection w ∈
              unitNegative.image (fun z => -GaussianReflection z) :=
            Finset.mem_image.mpr ⟨w, hw, rfl⟩
          rw [hmap] at hm
          change -GaussianReflection w ∈ unitPositive
          exact hm
      | true =>
          refine ⟨false, ?_⟩
          have hmap : unitPositive.image (fun z => -GaussianReflection z) =
              unitNegative := by
            decide
          change w ∈ unitPositive at hw
          have hm : -GaussianReflection w ∈
              unitPositive.image (fun z => -GaussianReflection z) :=
            Finset.mem_image.mpr ⟨w, hw, rfl⟩
          rw [hmap] at hm
          change -GaussianReflection w ∈ unitNegative
          exact hm
  | comp a b iha ihb =>
      intro o w hw
      obtain ⟨o', hw'⟩ := ihb o w hw
      exact iha o' _ hw'

private theorem matrixCov :
    (by
      classical
      exact
        (∀ (g : BandPackingSymmetry), ∀ (c : CircleCoordinates), (BandPackingSymmetryCircleAction
            g c).1 = c.1) → (
        let matrixVector (c : CircleCoordinates) (w : GaussianInt) : ℝ × ℝ :=
          (((1 + (c.2.re : ℝ)) * (w.re : ℝ) +
              (c.2.im : ℝ) * (w.im : ℝ)) / 2,
            ((c.2.im : ℝ) * (w.re : ℝ) +
              (1 - (c.2.re : ℝ)) * (w.im : ℝ)) / 2)
        let slopeDifferenceAction : BandPackingSymmetry → GaussianInt →
            (ℝ × ℝ) → ℝ × ℝ :=
          BandPackingSymmetry.rec
            (fun _ d => d)
            (fun _ d => (-d.2, d.1))
            (fun _ d => (-d.1, d.2))
            (fun z w d =>
              (d.1 + (z.re : ℝ) * (w.re : ℝ) + (z.im : ℝ) * (w.im : ℝ),
                d.2 + (z.im : ℝ) * (w.re : ℝ) - (z.re : ℝ) * (w.im : ℝ)))
            (fun _ b iha ihb w d =>
              iha (BandPackingSymmetryVectorAction b w) (ihb w d))
        ∀ (a : BandPackingSymmetry), ∀ (c : CircleCoordinates), ∀ (w : GaussianInt), c.1 = 1 →
            matrixVector (BandPackingSymmetryCircleAction a c) (BandPackingSymmetryVectorAction a
            w) = slopeDifferenceAction a w (matrixVector c w)) ) := by
  classical
  intro actionCurvature matrixVector slopeDifferenceAction a
  induction a with
  | identity => intro c w hc; rfl
  | shift z =>
      intro c w hc
      rcases c with ⟨k, ⟨cx, cy⟩⟩
      rcases z with ⟨zx, zy⟩
      rcases w with ⟨wx, wy⟩
      have hk : k = 1 := by exact_mod_cast hc
      subst k
      simp [matrixVector, slopeDifferenceAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryVectorAction,
        GaussianInt.intCast_re,
        GaussianInt.intCast_im];
        norm_num [GaussianInt.toComplex_def]; ring; simp
  | negate =>
      intro c w hc
      rcases c with ⟨k, ⟨cx, cy⟩⟩
      rcases w with ⟨wx, wy⟩
      have hk : k = 1 := by exact_mod_cast hc
      subst k
      simp [matrixVector, slopeDifferenceAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryVectorAction,
        GaussianQuarterTurn, GaussianInt.intCast_re,
        GaussianInt.intCast_im];
         ring; simp
  | conjugate =>
      intro c w hc
      rcases c with ⟨k, ⟨cx, cy⟩⟩
      rcases w with ⟨wx, wy⟩
      have hk : k = 1 := by exact_mod_cast hc
      subst k
      simp [matrixVector, slopeDifferenceAction,
        BandPackingSymmetryCircleAction, BandPackingSymmetryVectorAction,
        GaussianReflection, GaussianInt.intCast_re,
        GaussianInt.intCast_im];
         ring
  | comp a b iha ihb =>
      intro c w hc
      have hcurv : (BandPackingSymmetryCircleAction b c).1 = 1 := by
        rw [actionCurvature]
        exact hc
      change matrixVector
          (BandPackingSymmetryCircleAction a
            (BandPackingSymmetryCircleAction b c))
          (BandPackingSymmetryVectorAction a
            (BandPackingSymmetryVectorAction b w)) =
        slopeDifferenceAction a (BandPackingSymmetryVectorAction b w)
          (slopeDifferenceAction b w (matrixVector c w))
      rw [iha _ _ hcurv, ihb _ _ hc]

private theorem slopeDiffCov :
    (by
      classical
      exact
        (∀ (g : BandPackingSymmetry), ∀ (c : CircleCoordinates), (BandPackingSymmetryCircleAction
            g c).1 = c.1) → ((∀ (a : BandPackingSymmetry), ∀ (U : ProtoTile), ∀ (V : ProtoTile),
            ∀ (w : GaussianInt), TileCentroid V - TileCentroid U = GaussianRealPoint w →
            TileCentroid (BandPackingSymmetryTileAction a V) - TileCentroid
            (BandPackingSymmetryTileAction a U) = GaussianRealPoint
            (BandPackingSymmetryVectorAction a w)) → (
        let matrixVector (c : CircleCoordinates) (w : GaussianInt) : ℝ × ℝ :=
          (((1 + (c.2.re : ℝ)) * (w.re : ℝ) +
              (c.2.im : ℝ) * (w.im : ℝ)) / 2,
            ((c.2.im : ℝ) * (w.re : ℝ) +
              (1 - (c.2.re : ℝ)) * (w.im : ℝ)) / 2)
        let slopeDifferenceAction : BandPackingSymmetry → GaussianInt →
            (ℝ × ℝ) → ℝ × ℝ :=
          BandPackingSymmetry.rec
            (fun _ d => d)
            (fun _ d => (-d.2, d.1))
            (fun _ d => (-d.1, d.2))
            (fun z w d =>
              (d.1 + (z.re : ℝ) * (w.re : ℝ) + (z.im : ℝ) * (w.im : ℝ),
                d.2 + (z.im : ℝ) * (w.re : ℝ) - (z.re : ℝ) * (w.im : ℝ)))
            (fun _ b iha ihb w d =>
              iha (BandPackingSymmetryVectorAction b w) (ihb w d))
        (∀ (a : BandPackingSymmetry), ∀ (c : CircleCoordinates), ∀ (w : GaussianInt), c.1 = 1 →
            matrixVector (BandPackingSymmetryCircleAction a c) (BandPackingSymmetryVectorAction a
            w) = slopeDifferenceAction a w (matrixVector c w)) → (∀ (a : BandPackingSymmetry), ∀
            (c : CircleCoordinates), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (p : ℝ × ℝ), ∀ (p' :
            ℝ × ℝ), ∀ (w : GaussianInt), c.1 = 1 → TileCentroid V - TileCentroid U =
            GaussianRealPoint w → p' - p = matrixVector c w → BandPackingSymmetrySlopeAction a V
            p' - BandPackingSymmetrySlopeAction a U p = slopeDifferenceAction a w (matrixVector c
            w)))) ) := by
  classical
  intro actionCurvature centroidCov matrixVector slopeDifferenceAction matrixCov a
  induction a with
  | identity => intro c U V p p' w hc hcent hdiff; exact hdiff
  | shift z =>
      intro c U V p p' w hc hcent hdiff
      rcases z with ⟨zx, zy⟩
      rcases w with ⟨wx, wy⟩
      have hcent1 : (TileCentroid V).1 - (TileCentroid U).1 = wx := by
        simpa [GaussianRealPoint] using congrArg Prod.fst hcent
      have hcent2 : (TileCentroid V).2 - (TileCentroid U).2 = wy := by
        simpa [GaussianRealPoint] using congrArg Prod.snd hcent
      rcases p with ⟨px, py⟩
      rcases p' with ⟨p'x, p'y⟩
      have hdiff1 : p'x - px = (matrixVector c ⟨wx, wy⟩).1 := by
        simpa using congrArg Prod.fst hdiff
      have hdiff2 : p'y - py = (matrixVector c ⟨wx, wy⟩).2 := by
        simpa using congrArg Prod.snd hdiff
      simp [matrixVector] at hdiff1 hdiff2
      apply Prod.ext
      · simp [BandPackingSymmetrySlopeAction,
          slopeDifferenceAction, matrixVector]
        linear_combination hdiff1 + (zx : ℝ) * hcent1 + (zy : ℝ) * hcent2
      · simp [BandPackingSymmetrySlopeAction,
          slopeDifferenceAction, matrixVector]
        linear_combination hdiff2 + (zy : ℝ) * hcent1 - (zx : ℝ) * hcent2
  | negate =>
      intro c U V p p' w hc hcent hdiff
      rcases p with ⟨px, py⟩
      rcases p' with ⟨p'x, p'y⟩
      have h1 := congrArg Prod.fst hdiff
      have h2 := congrArg Prod.snd hdiff
      simp? [BandPackingSymmetrySlopeAction,
        slopeDifferenceAction] at h1 h2 ⊢
      exact ⟨by linarith [h2], by linarith [h1]⟩
  | conjugate =>
      intro c U V p p' w hc hcent hdiff
      rcases p with ⟨px, py⟩
      rcases p' with ⟨p'x, p'y⟩
      have h1 := congrArg Prod.fst hdiff
      have h2 := congrArg Prod.snd hdiff
      simp? [BandPackingSymmetrySlopeAction,
        slopeDifferenceAction] at h1 h2 ⊢
      exact ⟨by linarith [h1], by linarith [h2]⟩
  | comp a b iha ihb =>
      intro c U V p p' w hc hcent hdiff
      have hcentB := centroidCov b U V w hcent
      have hdiffB := ihb c U V p p' w hc hcent hdiff
      have hcurvB : (BandPackingSymmetryCircleAction b c).1 = 1 := by
        rw [actionCurvature]
        exact hc
      have hdiffB' :
          BandPackingSymmetrySlopeAction b V p' -
            BandPackingSymmetrySlopeAction b U p =
            matrixVector (BandPackingSymmetryCircleAction b c)
              (BandPackingSymmetryVectorAction b w) :=
        hdiffB.trans (matrixCov b c w hc).symm
      have hdiffA := iha (BandPackingSymmetryCircleAction b c)
        (BandPackingSymmetryTileAction b U)
        (BandPackingSymmetryTileAction b V)
        (BandPackingSymmetrySlopeAction b U p)
        (BandPackingSymmetrySlopeAction b V p')
        (BandPackingSymmetryVectorAction b w) hcurvB hcentB hdiffB'
      rw [matrixCov b c w hc] at hdiffA
      simpa [BandPackingSymmetrySlopeAction,
        BandPackingSymmetryVectorAction, slopeDifferenceAction] using hdiffA

private theorem hinverseFixedCircleCoord :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction
            ginv (BandPackingSymmetryCircleAction bundle.symmetry C) = C) →
            (BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1 = Cᵢ.1.1) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv hcircleL
  rw [bundle.normalized_fixed_circle_eq]
  exact hcircleL Cᵢ.1.1

private theorem hmatrix00 :
    (by
      classical
      exact
        ∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 0 0 = (1 + ((D.1.1.2).re : ℝ)) / 2 ) := by
  classical
  intro D hD
  simp [CircleMatrix, BandCircleEuclideanData, hD]; ring

private theorem hmatrix01 :
    (by
      classical
      exact
        ∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 0 1 = ((D.1.1.2).im : ℝ) / 2 ) := by
  classical
  intro D hD
  simp [CircleMatrix, BandCircleEuclideanData, hD]; ring

private theorem hmatrix10 :
    (by
      classical
      exact
        ∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 1 0 = ((D.1.1.2).im : ℝ) / 2 ) := by
  classical
  intro D hD
  simp [CircleMatrix, BandCircleEuclideanData, hD]; ring

private theorem hmatrix11 :
    (by
      classical
      exact
        ∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 1 1 = (1 - ((D.1.1.2).re : ℝ)) / 2 ) := by
  classical
  intro D hD
  simp [CircleMatrix, BandCircleEuclideanData, hD]; ring

private theorem hdiffUnit :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (pFixed : ℝ ×
            ℝ), ∀ (pSelected : ℝ × ℝ), (bundle.normalizedFixedCircle.1.1.1 = (1 : ℤ)) → (∀ (v :
                GaussianInt), (pSelected.1 - pFixed.1 =
            CircleMatrix bundle.normalizedFixedCircle (0 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) *
            (↑v.re : ℝ) + CircleMatrix bundle.normalizedFixedCircle (0 : Fin (2 : ℕ)) (1 : Fin (2
            : ℕ)) * (↑v.im : ℝ)) → ((pSelected.2 - pFixed.2 = CircleMatrix
            bundle.normalizedFixedCircle (1 : Fin (2 : ℕ)) (0 : Fin (2 : ℕ)) * (↑v.re : ℝ) +
            CircleMatrix bundle.normalizedFixedCircle (1 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ)) *
            (↑v.im : ℝ)) → (
        let matrixVector (c : CircleCoordinates) (w : GaussianInt) : ℝ × ℝ :=
          (((1 + (c.2.re : ℝ)) * (w.re : ℝ) +
              (c.2.im : ℝ) * (w.im : ℝ)) / 2,
            ((c.2.im : ℝ) * (w.re : ℝ) +
              (1 - (c.2.re : ℝ)) * (w.im : ℝ)) / 2)
        (∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 0 0 = (1 + ((D.1.1.2).re : ℝ)) / 2) →
            ((∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 0 1 = ((D.1.1.2).im : ℝ) / 2) →
            ((∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 1 0 = ((D.1.1.2).im : ℝ) / 2) →
            ((∀ (D : BandCircle), D.1.1.1 = 1 → CircleMatrix D 1 1 = (1 - ((D.1.1.2).re : ℝ)) /
            2) → (pSelected - pFixed = matrixVector bundle.normalizedFixedCircle.1.1 v))))))) )
            := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle pFixed pSelected hcurvUnit v hslopeUnitRe hslopeUnitIm
      matrixVector hmatrix00 hmatrix01 hmatrix10 hmatrix11
  apply Prod.ext
  · have hh := hslopeUnitRe
    rw [hmatrix00 bundle.normalizedFixedCircle hcurvUnit,
      hmatrix01 bundle.normalizedFixedCircle hcurvUnit] at hh
    calc
      pSelected.1 - pFixed.1 = _ := hh
      _ = (matrixVector bundle.normalizedFixedCircle.1.1 v).1 := by
        simp [matrixVector]
        ring
  · have hh := hslopeUnitIm
    rw [hmatrix10 bundle.normalizedFixedCircle hcurvUnit,
      hmatrix11 bundle.normalizedFixedCircle hcurvUnit] at hh
    calc
      pSelected.2 - pFixed.2 = _ := hh
      _ = (matrixVector bundle.normalizedFixedCircle.1.1 v).2 := by
        simp [matrixVector]
        ring

private theorem hdiffUnitInv' :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        ∀ (pFixed : ℝ × ℝ), ∀ (pSelected : ℝ × ℝ), (bundle.normalizedFixedCircle.1.1.1 = (1 : ℤ))
            → (∀ (v : GaussianInt),
        let matrixVector (c : CircleCoordinates) (w : GaussianInt) : ℝ × ℝ :=
          (((1 + (c.2.re : ℝ)) * (w.re : ℝ) +
              (c.2.im : ℝ) * (w.im : ℝ)) / 2,
            ((c.2.im : ℝ) * (w.re : ℝ) +
              (1 - (c.2.re : ℝ)) * (w.im : ℝ)) / 2)
        let slopeDifferenceAction : BandPackingSymmetry → GaussianInt →
            (ℝ × ℝ) → ℝ × ℝ :=
          BandPackingSymmetry.rec
            (fun _ d => d)
            (fun _ d => (-d.2, d.1))
            (fun _ d => (-d.1, d.2))
            (fun z w d =>
              (d.1 + (z.re : ℝ) * (w.re : ℝ) + (z.im : ℝ) * (w.im : ℝ),
                d.2 + (z.im : ℝ) * (w.re : ℝ) - (z.re : ℝ) * (w.im : ℝ)))
            (fun _ b iha ihb w d =>
              iha (BandPackingSymmetryVectorAction b w) (ihb w d))
        (∀ (a : BandPackingSymmetry), ∀ (c : CircleCoordinates), ∀ (w : GaussianInt), c.1 = 1 →
            matrixVector (BandPackingSymmetryCircleAction a c) (BandPackingSymmetryVectorAction a
            w) = slopeDifferenceAction a w (matrixVector c w)) → ((BandPackingSymmetrySlopeAction
            ginv selectedSupport pSelected - BandPackingSymmetrySlopeAction ginv
            bundle.normalizedFixed pFixed = slopeDifferenceAction ginv v (matrixVector
            bundle.normalizedFixedCircle.1.1 v)) →
            (BandPackingSymmetrySlopeAction ginv selectedSupport pSelected -
            BandPackingSymmetrySlopeAction ginv bundle.normalizedFixed pFixed = matrixVector
            (BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1)
            (BandPackingSymmetryVectorAction ginv v)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv selectedSupport pFixed pSelected hcurvUnit v matrixVector
      slopeDifferenceAction matrixCov hdiffUnitInv
  exact hdiffUnitInv.trans (matrixCov ginv
    bundle.normalizedFixedCircle.1.1 v hcurvUnit).symm

private theorem htargetMatrix :
    (by
      classical
      exact
        ∀ (Cᵢ : BandCircle), ∀ (ginv : BandPackingSymmetry), ∀ (v : GaussianInt),
        let matrixVector (c : CircleCoordinates) (w : GaussianInt) : ℝ × ℝ :=
          (((1 + (c.2.re : ℝ)) * (w.re : ℝ) +
              (c.2.im : ℝ) * (w.im : ℝ)) / 2,
            ((c.2.im : ℝ) * (w.re : ℝ) +
              (1 - (c.2.re : ℝ)) * (w.im : ℝ)) / 2)
        (CircleMatrix Cᵢ 0 0 = (1 + ((Cᵢ.1.1.2).re : ℝ)) / 2) → ((CircleMatrix Cᵢ 0 1 =
            ((Cᵢ.1.1.2).im : ℝ) / 2) → ((CircleMatrix Cᵢ 1 0 = ((Cᵢ.1.1.2).im : ℝ) / 2) →
            ((CircleMatrix Cᵢ 1 1 = (1 - ((Cᵢ.1.1.2).re : ℝ)) / 2) → (matrixVector Cᵢ.1.1
            (BandPackingSymmetryVectorAction ginv v) = (CircleMatrix Cᵢ 0 0 *
            (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 0 1 *
            (BandPackingSymmetryVectorAction ginv v).im, CircleMatrix Cᵢ 1 0 *
            (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 1 1 *
            (BandPackingSymmetryVectorAction ginv v).im))))) ) := by
  classical
  intro Cᵢ ginv v matrixVector hmatrixInv0 hmatrixInv1 hmatrixInv2 hmatrixInv3
  apply Prod.ext
  · simp [matrixVector, hmatrixInv0, hmatrixInv1]
    ring
  · simp [matrixVector, hmatrixInv2, hmatrixInv3]
    ring

private theorem hdiffUnitInvFinal :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        ∀ (pFixed : ℝ × ℝ), ∀ (pSelected : ℝ × ℝ), ∀ (v : GaussianInt),
        let matrixVector (c : CircleCoordinates) (w : GaussianInt) : ℝ × ℝ :=
          (((1 + (c.2.re : ℝ)) * (w.re : ℝ) +
              (c.2.im : ℝ) * (w.im : ℝ)) / 2,
            ((c.2.im : ℝ) * (w.re : ℝ) +
              (1 - (c.2.re : ℝ)) * (w.im : ℝ)) / 2)
        (BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1 = Cᵢ.1.1) →
            ((BandPackingSymmetrySlopeAction ginv selectedSupport pSelected -
            BandPackingSymmetrySlopeAction ginv bundle.normalizedFixed pFixed = matrixVector
            (BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1)
            (BandPackingSymmetryVectorAction ginv v)) → ((matrixVector Cᵢ.1.1
            (BandPackingSymmetryVectorAction ginv v) = (CircleMatrix Cᵢ 0 0 *
            (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 0 1 *
            (BandPackingSymmetryVectorAction ginv v).im, CircleMatrix Cᵢ 1 0 *
            (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 1 1 *
            (BandPackingSymmetryVectorAction ginv v).im)) → (BandPackingSymmetrySlopeAction ginv
            selectedSupport pSelected - BandPackingSymmetrySlopeAction ginv
            bundle.normalizedFixed pFixed = (CircleMatrix Cᵢ 0 0 *
            (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 0 1 *
            (BandPackingSymmetryVectorAction ginv v).im, CircleMatrix Cᵢ 1 0 *
            (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 1 1 *
            (BandPackingSymmetryVectorAction ginv v).im)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv selectedSupport pFixed pSelected v matrixVector
      hinverseFixedCircleCoord hdiffUnitInv' htargetMatrix
  rw [hinverseFixedCircleCoord] at hdiffUnitInv'
  exact hdiffUnitInv'.trans htargetMatrix

private theorem fixedCells :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), (TileOdometer
            bundle.normalizedFixedCircle.1.1
            bundle.normalizedFixed bundle.normalizedFixedFunction) → (∀ (pFixed : ℝ × ℝ),
            (PartialOdometerSlope bundle.normalizedFixedFunction = some pFixed) →
            (bundle.normalizedFixed.cells.Nonempty)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hOFixed pFixed hslopeFixed
  have hdom := PositiveCurvatureTileOdometerDomain
    bundle.normalizedFixedCircle.1.1 bundle.normalizedFixed
    bundle.normalizedFixedFunction bundle.normalizedFixedCircle.property hOFixed
  by_contra hne
  have hsingleton : (bundle.normalizedFixedFunction.domain : Set GaussianInt) =
      {bundle.normalizedFixed.anchor} := by
    rw [hdom]
    simp [FootprintVertices, hne]
  have hsquares : (PartialOdometerSquares bundle.normalizedFixedFunction).Nonempty := by
    by_contra hsq
    have hnone : PartialOdometerSlope bundle.normalizedFixedFunction = none := by
      simp [PartialOdometerSlope, hsq]
    rw [hnone] at hslopeFixed
    cases hslopeFixed
  rcases hsquares with ⟨y, hy⟩
  simp only [PartialOdometerSquares, Finset.mem_filter] at hy
  have hy0 : y = bundle.normalizedFixed.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hsingleton]
    exact hy.1
  have hy1 : y + 1 = bundle.normalizedFixed.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hsingleton]
    exact hy.2.1
  have hbad : y + 1 = y := hy1.trans hy0.symm
  have hbad' := congrArg (fun z : GaussianInt => z.re) hbad
  norm_num at hbad'

private theorem selectedCells :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        (TileOdometer bundle.normalizedFixedCircle.1.1
            (bundle.pieces bundle.selectedSlot bundle.selectedSign) (bundle.functions
            bundle.selectedSlot bundle.selectedSign)) → (∀ (pSelected : ℝ × ℝ),
            (PartialOdometerSlope (bundle.functions bundle.selectedSlot bundle.selectedSign) =
            some pSelected) → (selectedSupport.cells.Nonempty)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle selectedSupport hOSelected pSelected hslopeSelected
  let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
  have hdom := PositiveCurvatureTileOdometerDomain
    bundle.normalizedFixedCircle.1.1 selectedSupport selectedFunction
    bundle.normalizedFixedCircle.property hOSelected
  by_contra hne
  have hsingleton : (selectedFunction.domain : Set GaussianInt) =
      {selectedSupport.anchor} := by
    rw [hdom]
    simp [FootprintVertices, hne]
  have hsquares : (PartialOdometerSquares selectedFunction).Nonempty := by
    by_contra hsq
    have hnone : PartialOdometerSlope selectedFunction = none := by
      simp [PartialOdometerSlope, hsq]
    rw [hnone] at hslopeSelected
    cases hslopeSelected
  rcases hsquares with ⟨y, hy⟩
  simp only [PartialOdometerSquares, Finset.mem_filter] at hy
  have hy0 : y = selectedSupport.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hsingleton]
    exact hy.1
  have hy1 : y + 1 = selectedSupport.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hsingleton]
    exact hy.2.1
  have hbad : y + 1 = y := hy1.trans hy0.symm
  have hbad' := congrArg (fun z : GaussianInt => z.re) hbad
  norm_num at hbad'

private theorem hslopeFixedInv :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), ∀ (pFixed : ℝ × ℝ), (PartialOdometerSlope
            bundle.normalizedFixedFunction = some pFixed) →
            ((bundle.normalizedFixed.cells.Nonempty) → ((TileOdometer
            (BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1)
                (BandPackingSymmetryTileAction ginv
            bundle.normalizedFixed) (BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction) ∧ (↑(BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction).domain : Set GaussianInt) =
            BandPackingSymmetryVectorAction ginv '' (↑bundle.normalizedFixedFunction.domain : Set
            GaussianInt) ∧ (Finset.Nonempty bundle.normalizedFixed.cells → PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction ginv bundle.normalizedFixedFunction) =
            Option.map (BandPackingSymmetrySlopeAction ginv bundle.normalizedFixed)
            (PartialOdometerSlope bundle.normalizedFixedFunction))) → (
        let pFixedInv := BandPackingSymmetrySlopeAction ginv
          bundle.normalizedFixed pFixed
        PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction) = some pFixedInv))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv pFixed hslopeFixed fixedCells hcovFixed pFixedInv
  rw [hcovFixed.2.2 fixedCells, hslopeFixed]
  rfl

private theorem hslopeSelectedInv :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        ∀ (pSelected : ℝ × ℝ), (PartialOdometerSlope (bundle.functions bundle.selectedSlot
            bundle.selectedSign) = some pSelected) → ((selectedSupport.cells.Nonempty) →
            ((TileOdometer (BandPackingSymmetryCircleAction ginv
                bundle.normalizedFixedCircle.1.1) (BandPackingSymmetryTileAction ginv
            selectedSupport) (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) ∧
            (↑(BandPackingSymmetryPartialOdometerAction ginv selectedFunction).domain : Set
            GaussianInt) = BandPackingSymmetryVectorAction ginv '' (↑selectedFunction.domain :
            Set GaussianInt) ∧ (Finset.Nonempty selectedSupport.cells → PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) = Option.map
            (BandPackingSymmetrySlopeAction ginv selectedSupport) (PartialOdometerSlope
            selectedFunction))) → (
        let pSelectedInv := BandPackingSymmetrySlopeAction ginv
          selectedSupport pSelected
        PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) =
            some pSelectedInv))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv selectedSupport selectedFunction pSelected hslopeSelected
      selectedCells hcovSelected pSelectedInv
  rw [hcovSelected.2.2 selectedCells, hslopeSelected]
  rfl

private theorem hOFixedOriginalAt1198 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → ((∀ (h : PartialOdometer),
            BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) →
            ((BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1 = Cᵢ.1.1) →
            ((TileOdometer (BandPackingSymmetryCircleAction ginv
                bundle.normalizedFixedCircle.1.1) (BandPackingSymmetryTileAction ginv
            bundle.normalizedFixed) (BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction) ∧ (↑(BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction).domain : Set GaussianInt) =
            BandPackingSymmetryVectorAction ginv '' (↑bundle.normalizedFixedFunction.domain : Set
            GaussianInt) ∧ (Finset.Nonempty bundle.normalizedFixed.cells → PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction ginv bundle.normalizedFixedFunction) =
            Option.map (BandPackingSymmetrySlopeAction ginv bundle.normalizedFixed)
            (PartialOdometerSlope bundle.normalizedFixedFunction))) → (TileOdometer Cᵢ.1.1 Tᵢ
            hᵢ)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv htileL hfunL hinverseFixedCircleCoord hcovFixed
  have h := hcovFixed.1
  change TileOdometer
    (BandPackingSymmetryCircleAction ginv
      bundle.normalizedFixedCircle.1.1)
    (BandPackingSymmetryTileAction ginv bundle.normalizedFixed)
    (BandPackingSymmetryPartialOdometerAction ginv
      bundle.normalizedFixedFunction) at h
  rw [hinverseFixedCircleCoord, bundle.normalized_fixed_eq, htileL,
    bundle.normalized_fixed_function_eq, hfunL] at h
  exact h

private theorem hOSelectedOriginalAt1209 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1 = Cᵢ.1.1) →
            ((TileOdometer (BandPackingSymmetryCircleAction ginv
                bundle.normalizedFixedCircle.1.1) (BandPackingSymmetryTileAction ginv
            selectedSupport) (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) ∧
            (↑(BandPackingSymmetryPartialOdometerAction ginv selectedFunction).domain : Set
            GaussianInt) = BandPackingSymmetryVectorAction ginv '' (↑selectedFunction.domain :
            Set GaussianInt) ∧ (Finset.Nonempty selectedSupport.cells → PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) = Option.map
            (BandPackingSymmetrySlopeAction ginv selectedSupport) (PartialOdometerSlope
            selectedFunction))) → (TileOdometer Cᵢ.1.1 T' h')) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv selectedSupport selectedFunction T' h'
      hinverseFixedCircleCoord hcovSelected
  have h := hcovSelected.1
  change TileOdometer
    (BandPackingSymmetryCircleAction ginv
      bundle.normalizedFixedCircle.1.1)
    (BandPackingSymmetryTileAction ginv selectedSupport)
    (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) at h
  simpa [hinverseFixedCircleCoord, T', h', bundle.normalized_fixed_eq] using h

private theorem hleftInvAt1222 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        ∀ (pFixed : ℝ × ℝ), ∀ (pSelected : ℝ × ℝ), ∀ (v : GaussianInt), (Cᵢ.1.1.1 = 1) →
            ((TileCentroid T' - TileCentroid Tᵢ = GaussianRealPoint
            (BandPackingSymmetryVectorAction ginv v)) → (∀ (orientationInv : Bool),
            (UnitTriangularStep orientationInv (BandPackingSymmetryVectorAction ginv v)) →
            ((BandPackingSymmetrySlopeAction ginv selectedSupport pSelected -
            BandPackingSymmetrySlopeAction ginv bundle.normalizedFixed pFixed = (CircleMatrix Cᵢ
            0 0 * (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 0 1 *
            (BandPackingSymmetryVectorAction ginv v).im, CircleMatrix Cᵢ 1 0 *
            (BandPackingSymmetryVectorAction ginv v).re + CircleMatrix Cᵢ 1 1 *
            (BandPackingSymmetryVectorAction ginv v).im)) → (
        let pFixedInv := BandPackingSymmetrySlopeAction ginv
          bundle.normalizedFixed pFixed
        let pSelectedInv := BandPackingSymmetrySlopeAction ginv
          selectedSupport pSelected
        (TileOdometer Cᵢ.1.1 Tᵢ hᵢ) → ((TileOdometer Cᵢ.1.1 T' h') → ((PartialOdometerSlope hᵢ =
            some pFixedInv) → ((PartialOdometerSlope h' = some pSelectedInv) →
            (LeftLatticeAdjacent Cᵢ Tᵢ T' hᵢ h')))))))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv selectedSupport selectedFunction T' h' pFixed pSelected v
      hinverseUnitCurv hcentUnitInv orientationInv hunitStepInv hdiffUnitInvFinal pFixedInv
      pSelectedInv hOFixedOriginal hOSelectedOriginal hslopeFixedOriginal hslopeSelectedOriginal
  refine ⟨hOFixedOriginal, hOSelectedOriginal, pFixedInv, pSelectedInv,
    hslopeFixedOriginal, hslopeSelectedOriginal, ?_⟩
  left
  refine ⟨hinverseUnitCurv, orientationInv,
    BandPackingSymmetryVectorAction ginv v, hunitStepInv,
    hcentUnitInv, ?_⟩
  have hdiff := hdiffUnitInvFinal
  exact ⟨by simpa [pFixedInv, pSelectedInv] using congrArg Prod.fst hdiff,
    by simpa [pFixedInv, pSelectedInv] using congrArg Prod.snd hdiff⟩

private theorem hOFixedq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), (TileOdometer
            bundle.normalizedFixedCircle.1.1
            bundle.normalizedFixed bundle.normalizedFixedFunction) → (∀ (qLeft : Fin (4 : ℕ) →
            CircleCoordinates), (qLeft (0 : Fin (4 : ℕ)) = bundle.normalizedFixedCircle.1.1) →
                (TileOdometer (qLeft 0)
            bundle.normalizedFixed bundle.normalizedFixedFunction)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hOFixed qLeft hqLeft0
  rw [hqLeft0]
  exact hOFixed

private theorem hOSelectedq :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        (TileOdometer bundle.normalizedFixedCircle.1.1
            (bundle.pieces bundle.selectedSlot bundle.selectedSign) (bundle.functions
            bundle.selectedSlot bundle.selectedSign)) → (∀ (qLeft : Fin (4 : ℕ) →
            CircleCoordinates), (qLeft (0 : Fin (4 : ℕ)) = bundle.normalizedFixedCircle.1.1) →
                (TileOdometer (qLeft 0) selectedSupport
            selectedFunction)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle selectedSupport selectedFunction hOSelected qLeft hqLeft0
  rw [hqLeft0]
  exact hOSelected

private theorem hleftRootCoord :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction
            ginv (BandPackingSymmetryCircleAction bundle.symmetry C) = C) → (∀ (qLeft : Fin (4 :
            ℕ) → CircleCoordinates), (qLeft (0 : Fin (4 : ℕ)) = bundle.normalizedFixedCircle.1.1)
                → ((BandPackingSymmetryQuadrupleAction
            ginv qLeft) 0 = Cᵢ.1.1)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv hcircleL qLeft hqLeft0
  calc
    (BandPackingSymmetryQuadrupleAction ginv qLeft) 0 =
        BandPackingSymmetryCircleAction ginv (qLeft 0) := by
          simp [BandPackingSymmetryQuadrupleAction]
    _ = Cᵢ.1.1 := by
          rw [hqLeft0, bundle.normalized_fixed_circle_eq]
          exact hcircleL Cᵢ.1.1

private theorem hOFixedOriginalAt1264 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → ((∀ (h : PartialOdometer),
            BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → (∀ (qLeft : Fin
            (4 : ℕ) → CircleCoordinates), (TileOdometer (BandPackingSymmetryQuadrupleAction ginv
            qLeft (0 : Fin (4 : ℕ))) (BandPackingSymmetryTileAction ginv bundle.normalizedFixed)
            (BandPackingSymmetryPartialOdometerAction ginv bundle.normalizedFixedFunction)) →
            (((BandPackingSymmetryQuadrupleAction ginv qLeft) 0 = Cᵢ.1.1) → (TileOdometer Cᵢ.1.1
            Tᵢ hᵢ)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv htileL hfunL qLeft hOFixedInv hleftRootCoord
  have h := hOFixedInv
  change TileOdometer
    ((BandPackingSymmetryQuadrupleAction ginv qLeft) 0)
    (BandPackingSymmetryTileAction ginv bundle.normalizedFixed)
    (BandPackingSymmetryPartialOdometerAction ginv
      bundle.normalizedFixedFunction) at h
  rw [hleftRootCoord, bundle.normalized_fixed_eq, htileL,
    bundle.normalized_fixed_function_eq, hfunL] at h
  exact h

private theorem hOSelectedOriginalAt1274 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        ∀ (qLeft : Fin (4 : ℕ) → CircleCoordinates), (TileOdometer
            (BandPackingSymmetryQuadrupleAction ginv qLeft (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction ginv selectedSupport)
            (BandPackingSymmetryPartialOdometerAction ginv selectedFunction)) →
            (((BandPackingSymmetryQuadrupleAction ginv qLeft) 0 = Cᵢ.1.1) → (TileOdometer Cᵢ.1.1
            T' h')) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv selectedSupport selectedFunction T' h' qLeft
      hOSelectedInv hleftRootCoord
  change TileOdometer
    ((BandPackingSymmetryQuadrupleAction ginv qLeft) 0)
    (BandPackingSymmetryTileAction ginv selectedSupport)
    (BandPackingSymmetryPartialOdometerAction ginv selectedFunction)
    at hOSelectedInv
  simpa [hleftRootCoord, T', h'] using hOSelectedInv

private theorem hleftInvAt1283 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        ∀ (qLeft : Fin (4 : ℕ) → CircleCoordinates), ∀ (jLeft : Fin (3 : ℕ)), ∀ (eLeft : Bool),
            (ProperBandQuadruple qLeft) → (∀ (negative : Bool), ∀ (pFixedInv : ℝ × ℝ), ∀
            (pSelectedInv : ℝ × ℝ), (PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) = some pSelectedInv)
            → ((TileCentroid (BandPackingSymmetryTileAction ginv selectedSupport) - TileCentroid
            (BandPackingSymmetryTileAction ginv bundle.normalizedFixed) = (if (eLeft ^^ negative)
            = true then (1 : ℝ) else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv qLeft (if
            BandPackingSymmetryReversesOrientation ginv = true then -jLeft else jLeft).succ)
            (BandPackingSymmetryQuadrupleAction ginv qLeft (0 : Fin (4 : ℕ))))) →
            ((pSelectedInv.1 - pFixedInv.1 = (if (eLeft ^^ negative) = true then (1 : ℝ) else (-1
            : ℝ)) * (↑(BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv qLeft (if
            BandPackingSymmetryReversesOrientation ginv = true then -jLeft else jLeft).succ)
            (BandPackingSymmetryQuadrupleAction ginv qLeft (0 : Fin (4 : ℕ)))).re : ℝ)) →
            ((pSelectedInv.2 - pFixedInv.2 = (if (eLeft ^^ negative) = true then (1 : ℝ) else (-1
            : ℝ)) * (↑(BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv qLeft (if
            BandPackingSymmetryReversesOrientation ginv = true then -jLeft else jLeft).succ)
            (BandPackingSymmetryQuadrupleAction ginv qLeft (0 : Fin (4 : ℕ)))).im : ℝ)) →
            (((BandPackingSymmetryQuadrupleAction ginv qLeft) 0 = Cᵢ.1.1) → ((TileOdometer Cᵢ.1.1
            Tᵢ hᵢ) → ((TileOdometer Cᵢ.1.1 T' h') → ((PartialOdometerSlope hᵢ = some pFixedInv) →
            (LeftLatticeAdjacent Cᵢ Tᵢ T' hᵢ h')))))))))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv htileL selectedSupport selectedFunction T' h' qLeft jLeft
      eLeft hqLeft negative pFixedInv pSelectedInv hslopeSelectedInv hcentLeftInv hslopeLeftReInv
      hslopeLeftImInv hleftRootCoord hOFixedOriginal hOSelectedOriginal hslopeFixedOriginal
  refine ⟨hOFixedOriginal, hOSelectedOriginal, pFixedInv, pSelectedInv,
    hslopeFixedOriginal, hslopeSelectedInv, ?_⟩
  · right
    refine ⟨BandPackingSymmetryQuadrupleAction ginv qLeft,
      (if BandPackingSymmetryReversesOrientation ginv then -jLeft else jLeft),
      (eLeft ^^ negative),
      BandPackingSymmetryProperCovariance ginv qLeft hqLeft,
      hleftRootCoord,
      (by simpa [T', bundle.normalized_fixed_eq, htileL] using hcentLeftInv),
      hslopeLeftReInv, hslopeLeftImInv⟩

private theorem hparentPositiveAt1298 :
    (by
      classical
      exact
        ∀ (C' : BandCircle), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (r
            j.succ = C'.1.1) → (0 < (r j.succ).1) ) := by
  classical
  intro C' r j hrj
  rw [hrj]
  exact C'.property

private theorem hOfixedAt1301 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (r : Fin (4 : ℕ)
            → CircleCoordinates), (r (0 : Fin (4 : ℕ)) = bundle.normalizedFixedCircle.1.1) →
                (TileOdometer (r 0) bundle.normalizedFixed
            bundle.normalizedFixedFunction) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle r hr0
  rw [hr0]
  exact bundle.normalized_fixed_odometer

private theorem hOselectedAt1305 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (C' :
            BandCircle), (C'.1.1 = bundle.normalizedPresentation bundle.selectedSlot.succ) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (r j.succ = C'.1.1) →
            (TileOdometer (r j.succ) selectedSupport selectedFunction)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C' hC' selectedSupport selectedFunction r j hrj
  rw [hrj, hC']
  exact bundle.piece_odometer bundle.selectedSlot bundle.selectedSign

private theorem hOFixedOriginalAt1322 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction
            ginv (BandPackingSymmetryCircleAction bundle.symmetry C) = C) → ((∀ (T : ProtoTile),
            BandPackingSymmetryTileAction ginv (BandPackingSymmetryTileAction bundle.symmetry T)
            = T) → ((∀ (h : PartialOdometer), BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → (∀ (r : Fin (4 :
            ℕ) → CircleCoordinates), (r (0 : Fin (4 : ℕ)) = bundle.normalizedFixedCircle.1.1) →
                ((TileOdometer
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryTileAction ginv bundle.normalizedFixed)
            (BandPackingSymmetryPartialOdometerAction ginv bundle.normalizedFixedFunction)) →
            (TileOdometer Cᵢ.1.1 Tᵢ hᵢ))))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv hcircleL htileL hfunL r hr0 hOFixedInv
  simpa [BandPackingSymmetryQuadrupleAction, hr0,
    bundle.normalized_fixed_circle_eq, bundle.normalized_fixed_eq,
    bundle.normalized_fixed_function_eq, hcircleL, htileL, hfunL]
    using hOFixedInv

private theorem hselectedCoordAt1327 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (0 < (r j.succ).1) → (∀
            (transportedRotation : Fin (4 : ℕ)), ∀ (C' : BandCircle), ∀ (selectedSlope : ℝ × ℝ),
            ∀ (ginv : BandPackingSymmetry),
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        ∀ (t : Fin (4 : ℕ)), (r j.succ = C'.1.1) → ((TileCentroid (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) - TileCentroid bundle.normalizedFixed = (1 /
            2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) *
            (BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ)))
            (r j.succ)))) → ((selectedSlope.1 - bundle.normalizedFixedSlope.1 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2
            (r j.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.2 (r (0 : Fin (4 : ℕ))) (r
            j.succ)))).1) → ((selectedSlope.2 - bundle.normalizedFixedSlope.2 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2
            (r j.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.2 (r (0 : Fin (4 : ℕ))) (r
            j.succ)))).2) → ((bundle.normalizedPoint ∈ FootprintVertices (TileTranslation
            bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑transportedRotation :
            ℕ) * if Even (↑transportedRotation : ℕ) then BandVectors.1 (normalizationPresentation
            (0 : Fin (4 : ℕ))) (normalizationPresentation (sigma i).succ) else BandVectors.1
            (normalizationPresentation (sigma i).succ) (normalizationPresentation (0 : Fin (4 :
            ℕ))))) ↔ bundle.normalizedPoint ∈ FootprintVertices (TileTranslation
            bundle.normalizedFixed ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) * if Even (↑t :
            ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r j.succ) else BandVectors.1 (r j.succ)
            (r (0 : Fin (4 : ℕ)))))) → ((TileOdometer (r j.succ) selectedSupport
            selectedFunction) → (∀ (pFixed : ℝ × ℝ), ∀ (pSelected : ℝ × ℝ), ∀ (t' : Fin (4 : ℕ)),
            (TileOdometer (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryTileAction ginv selectedSupport)
            (BandPackingSymmetryPartialOdometerAction ginv selectedFunction)) → ((TileCentroid
            (BandPackingSymmetryTileAction ginv selectedSupport) - TileCentroid
            (BandPackingSymmetryTileAction ginv bundle.normalizedFixed) = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t' : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ) (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin
            (4 : ℕ))) + BandVectors.1 (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)))) →
            ((pSelected.1 - pFixed.1 = (1 / 2 : ℝ) * (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑t' : ℕ) * (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r
            (if BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).1) → ((pSelected.2 - pFixed.2 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).2) → ((BandPackingSymmetryQuadrupleAction ginv
            r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ =
            inverseCircle.1.1)))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma r j hparentPositive
      transportedRotation C' selectedSlope ginv inversePresentation inverseSlot hinverseProper
      hinversePositive inverseCircle hinverseCircle selectedSupport selectedFunction t hrj hcent
      hslopeRe hslopeIm hmarked hOselected pFixed pSelected t' hOSelectedInv hcentInv hslopeReInv
      hslopeImInv
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  calc
    (BandPackingSymmetryQuadrupleAction ginv r)
        (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ =
        BandPackingSymmetryCircleAction ginv (r j.succ) := by
          by_cases hrev : BandPackingSymmetryReversesOrientation ginv <;>
            fin_cases j <;>
            simp [BandPackingSymmetryQuadrupleAction,
              hrev, neg1, neg2]
    _ = BandPackingSymmetryCircleAction ginv C'.1.1 :=
      congrArg (BandPackingSymmetryCircleAction ginv) hrj
    _ = inverseCircle.1.1 := hinverseCircle.symm

private theorem hcentOriginalAt1348 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), ∀ (t' : Fin (4 : ℕ)),
            (TileCentroid (BandPackingSymmetryTileAction ginv selectedSupport) - TileCentroid
            (BandPackingSymmetryTileAction ginv bundle.normalizedFixed) = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t' : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ) (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin
            (4 : ℕ))) + BandVectors.1 (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)))) →
            (TileCentroid T' - TileCentroid Tᵢ = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ t'.val * (BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv r)
            (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) + BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) ((BandPackingSymmetryQuadrupleAction
            ginv r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ))))) )
            := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv htileL selectedSupport T' r j t' hcentInv
  simpa [T', bundle.normalized_fixed_eq, htileL] using hcentInv

private theorem hrootCoord :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction
            ginv (BandPackingSymmetryCircleAction bundle.symmetry C) = C) → (∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), (r (0 : Fin (4 : ℕ)) = bundle.normalizedFixedCircle.1.1) →
                ((BandPackingSymmetryQuadrupleAction ginv
            r) 0 = Cᵢ.1.1)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv hcircleL r hr0
  calc
    (BandPackingSymmetryQuadrupleAction ginv r) 0 =
        BandPackingSymmetryCircleAction ginv (r 0) := by
          simp [BandPackingSymmetryQuadrupleAction]
    _ = BandPackingSymmetryCircleAction ginv
        bundle.normalizedFixedCircle.1.1 :=
          congrArg (BandPackingSymmetryCircleAction ginv) hr0
    _ = Cᵢ.1.1 := by
        rw [bundle.normalized_fixed_circle_eq]
        exact hcircleL Cᵢ.1.1

private theorem hnewAdjAt1371 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (ProperBandQuadruple r) →
            (∀ (pFixed : ℝ × ℝ), ∀ (pSelected : ℝ × ℝ), ∀ (t' : Fin (4 : ℕ)),
            (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction ginv
            selectedFunction) = some pSelected) → ((pSelected.1 - pFixed.1 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).1) → ((pSelected.2 - pFixed.2 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).2) → ((TileOdometer Cᵢ.1.1 Tᵢ hᵢ) →
            (((BandPackingSymmetryQuadrupleAction ginv r) (if
            BandPackingSymmetryReversesOrientation ginv then -j else j).succ = inverseCircle.1.1)
            → ((TileOdometer inverseCircle.1.1 T' h') → ((PartialOdometerSlope hᵢ = some pFixed)
            → ((TileCentroid T' - TileCentroid Tᵢ = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ t'.val * (BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv r)
            (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) + BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) ((BandPackingSymmetryQuadrupleAction
            ginv r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)))) →
            (((BandPackingSymmetryQuadrupleAction ginv r) 0 = Cᵢ.1.1) → (SubtileLatticeAdjacent
            Cᵢ inverseCircle Tᵢ T' hᵢ h')))))))))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv inversePresentation inverseSlot hinverseProper
      hinversePositive inverseCircle selectedSupport selectedFunction T' h' r j hr pFixed
      pSelected t' hslopeSelectedInv hslopeReInv hslopeImInv hOFixedOriginal hselectedCoord
      hOSelectedOriginal hslopeFixedOriginal hcentOriginal hrootCoord
  refine ⟨hOFixedOriginal, hOSelectedOriginal, pFixed, pSelected,
    hslopeFixedOriginal, hslopeSelectedInv, ?_⟩
  exact ⟨BandPackingSymmetryQuadrupleAction ginv r,
    (if BandPackingSymmetryReversesOrientation ginv then -j else j),
    t', BandPackingSymmetryProperCovariance ginv r hr, hrootCoord,
    hselectedCoord, hcentOriginal, hslopeReInv, hslopeImInv⟩

private theorem hpointInvAt1389 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (v : GaussianInt), BandPackingSymmetryVectorAction ginv
            (BandPackingSymmetryVectorAction bundle.symmetry v) = v) →
            ((BandPackingSymmetryVectorAction bundle.symmetry x = bundle.normalizedPoint) →
            (BandPackingSymmetryVectorAction ginv bundle.normalizedPoint = x)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv hvecL hpoint
  rw [← hpoint]
  exact hvecL x

private theorem hmarkedOriginalAt1396 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (delta : Bool), ∀ (transportedRotation : Fin (4 : ℕ)),
        let oldUR := TileTranslation T₀
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)))
        let rowUR := TileTranslation bundle.normalizedRoot
          ((⟨0, 1⟩ : GaussianInt) ^ transportedRotation.val *
            (if Even transportedRotation.val then
              BandVectors.1 (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)
            else BandVectors.1 (normalizationPresentation (sigma i).succ) (normalizationPresentation
                0)))
        (x ∈ FootprintVertices oldUR ↔ bundle.normalizedPoint ∈ FootprintVertices rowUR) → (∀
            (ginv : BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → (∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), ∀ (j : Fin (3 : ℕ)), ∀ (t : Fin (4 : ℕ)), (bundle.normalizedPoint
            ∈ FootprintVertices (TileTranslation bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑transportedRotation : ℕ) * if Even (↑transportedRotation : ℕ) then
            BandVectors.1 (normalizationPresentation (0 : Fin (4 : ℕ)))
            (normalizationPresentation (sigma i).succ) else BandVectors.1
            (normalizationPresentation (sigma i).succ) (normalizationPresentation (0 : Fin (4 :
            ℕ))))) ↔ bundle.normalizedPoint ∈ FootprintVertices (TileTranslation
            bundle.normalizedFixed ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) * if Even (↑t :
            ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r j.succ) else BandVectors.1 (r j.succ)
            (r (0 : Fin (4 : ℕ)))))) → (∀ (t' : Fin (4 : ℕ)), (t' = if
            BandPackingSymmetryReversesOrientation ginv = true then -t - (1 : Fin (4 : ℕ)) + if
            delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else t + if delta = true
            then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) → (
        (BandPackingSymmetryVectorAction ginv bundle.normalizedPoint = x) →
            ((bundle.normalizedPoint ∈ FootprintVertices (TileTranslation bundle.normalizedFixed
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) * if Even (↑t : ℕ) then BandVectors.1
            (r (0 : Fin (4 : ℕ))) (r j.succ) else BandVectors.1 (r j.succ) (r (0 : Fin (4 :
            ℕ))))) ↔ BandPackingSymmetryVectorAction ginv bundle.normalizedPoint ∈
            FootprintVertices (TileTranslation (BandPackingSymmetryTileAction ginv
            bundle.normalizedFixed) ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(if
            BandPackingSymmetryReversesOrientation ginv = true then -t - (1 : Fin (4 : ℕ)) + if
            delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else t + if delta = true
            then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) : ℕ) * if Even (↑(if
            BandPackingSymmetryReversesOrientation ginv = true then -t - (1 : Fin (4 : ℕ)) + if
            delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else t + if delta = true
            then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) : ℕ) then BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j) j).succ) else
            BandVectors.1 (BandPackingSymmetryQuadrupleAction ginv r ((fun (j : Fin (3 : ℕ)) =>
            if BandPackingSymmetryReversesOrientation ginv = true then -j else j) j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))))) → (x ∈
            FootprintVertices oldUR ↔ x ∈ FootprintVertices (TileTranslation Tᵢ ((⟨0, 1⟩ :
            GaussianInt) ^ t'.val * (if Even t'.val then BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) ((BandPackingSymmetryQuadrupleAction
            ginv r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ) else
            BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv r) (if
            BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
            ((BandPackingSymmetryQuadrupleAction ginv r) 0)))))))))) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma delta
      transportedRotation oldUR rowUR hmarkedOld ginv htileL r j t hmarked t' ht' hpointInv hmarkCov
  let companionForward := TileTranslation bundle.normalizedFixed
    ((⟨0, 1⟩ : GaussianInt) ^ t.val *
      (if Even t.val then BandVectors.1 (r 0) (r j.succ)
        else BandVectors.1 (r j.succ) (r 0)))
  calc
    x ∈ FootprintVertices oldUR ↔
        bundle.normalizedPoint ∈ FootprintVertices rowUR := hmarkedOld
    _ ↔ bundle.normalizedPoint ∈ FootprintVertices companionForward := by
      simpa [rowUR, companionForward] using hmarked
    _ ↔ BandPackingSymmetryVectorAction ginv bundle.normalizedPoint ∈
          FootprintVertices
            (TileTranslation (BandPackingSymmetryTileAction ginv
                bundle.normalizedFixed)
              ((⟨0, 1⟩ : GaussianInt) ^ t'.val *
                (if Even t'.val then
                  BandVectors.1
                    ((BandPackingSymmetryQuadrupleAction ginv r) 0)
                    ((BandPackingSymmetryQuadrupleAction ginv r)
                      (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
                else BandVectors.1
                  ((BandPackingSymmetryQuadrupleAction ginv r)
                    (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
                    ((BandPackingSymmetryQuadrupleAction ginv r) 0)))) := by
        simpa [companionForward, ht'] using hmarkCov
    _ ↔ x ∈ FootprintVertices
          (TileTranslation Tᵢ
            ((⟨0, 1⟩ : GaussianInt) ^ t'.val *
              (if Even t'.val then
                BandVectors.1
                  ((BandPackingSymmetryQuadrupleAction ginv r) 0)
                  ((BandPackingSymmetryQuadrupleAction ginv r)
                    (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
              else BandVectors.1
                ((BandPackingSymmetryQuadrupleAction ginv r)
                  (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
                ((BandPackingSymmetryQuadrupleAction ginv r) 0)))) := by
        rw [hpointInv, bundle.normalized_fixed_eq, htileL]

private theorem hparentPositiveAt1447 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (r : Fin (4 : ℕ)
            → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (r j.succ =
            bundle.normalizedFixedCircle.1.1) → (0 < (r
            j.succ).1) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle r j hrj
  rw [hrj]
  exact bundle.normalizedFixedCircle.property

private theorem hOselectedAt1450 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (C' :
            BandCircle), (C'.1.1 = bundle.normalizedPresentation bundle.selectedSlot.succ) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), (r (0 : Fin (4 : ℕ)) = C'.1.1) → (TileOdometer
            (r 0) selectedSupport selectedFunction)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C' hC' selectedSupport selectedFunction r hr0
  rw [hr0, hC']
  exact bundle.piece_odometer bundle.selectedSlot bundle.selectedSign

private theorem hOfixedAt1453 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (r : Fin (4 : ℕ)
            → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (r j.succ =
            bundle.normalizedFixedCircle.1.1) →
            (TileOdometer (r j.succ) bundle.normalizedFixed bundle.normalizedFixedFunction) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle r j hrj
  rw [hrj]
  exact bundle.normalized_fixed_odometer

private theorem hselectedCoordAt1468 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (C' :
            BandCircle), ∀ (ginv : BandPackingSymmetry),
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (∀ (r : Fin (4 : ℕ) →
            CircleCoordinates), (r (0 : Fin (4 : ℕ)) = C'.1.1) →
            ((BandPackingSymmetryQuadrupleAction ginv r) 0 = inverseCircle.1.1)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C' ginv inversePresentation inverseSlot hinverseProper
      hinversePositive inverseCircle hinverseCircle r hr0
  calc
    (BandPackingSymmetryQuadrupleAction ginv r) 0 =
        BandPackingSymmetryCircleAction ginv (r 0) := by
          simp [BandPackingSymmetryQuadrupleAction]
    _ = BandPackingSymmetryCircleAction ginv C'.1.1 :=
        congrArg (BandPackingSymmetryCircleAction ginv) hr0
    _ = inverseCircle.1.1 := hinverseCircle.symm

private theorem hfixedCoord :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (hᵢ
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (0 < (r j.succ).1) → (∀
            (transportedRotation : Fin (4 : ℕ)), ∀ (selectedSlope : ℝ × ℝ), ∀ (ginv :
            BandPackingSymmetry), (∀ (C : CircleCoordinates), BandPackingSymmetryCircleAction
            ginv (BandPackingSymmetryCircleAction bundle.symmetry C) = C) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        ∀ (t : Fin (4 : ℕ)), (r j.succ = bundle.normalizedFixedCircle.1.1) → ((TileCentroid
            bundle.normalizedFixed - TileCentroid
            (bundle.pieces bundle.selectedSlot bundle.selectedSign) = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) * (BandVectors.1 (r
            j.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r j.succ)))) →
            ((bundle.normalizedFixedSlope.1 - selectedSlope.1 = (1 / 2 : ℝ) * (GaussianRealPoint
            ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2 (r j.succ) (r (0 :
            Fin (4 : ℕ))) + BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ)))).1) →
            ((bundle.normalizedFixedSlope.2 - selectedSlope.2 = (1 / 2 : ℝ) * (GaussianRealPoint
            ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2 (r j.succ) (r (0 :
            Fin (4 : ℕ))) + BandVectors.2 (r (0 : Fin (4 : ℕ))) (r j.succ)))).2) →
            ((bundle.normalizedPoint ∈ FootprintVertices (TileTranslation bundle.normalizedRoot
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑transportedRotation : ℕ) * if Even
            (↑transportedRotation : ℕ) then BandVectors.1 (normalizationPresentation (0 : Fin (4
            : ℕ))) (normalizationPresentation (sigma i).succ) else BandVectors.1
            (normalizationPresentation (sigma i).succ) (normalizationPresentation (0 : Fin (4 :
            ℕ))))) ↔ bundle.normalizedPoint ∈ FootprintVertices (TileTranslation (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t :
            ℕ) * if Even (↑t : ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r j.succ) else
            BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ)))))) → ((TileOdometer (r j.succ)
            bundle.normalizedFixed bundle.normalizedFixedFunction) → (∀ (pSelected : ℝ × ℝ), ∀
            (pFixed : ℝ × ℝ), ∀ (t' : Fin (4 : ℕ)), (TileOdometer
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ) (BandPackingSymmetryTileAction ginv
            bundle.normalizedFixed) (BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction)) → ((TileCentroid (BandPackingSymmetryTileAction ginv
            bundle.normalizedFixed) - TileCentroid (BandPackingSymmetryTileAction ginv
            selectedSupport) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t' : ℕ) * (BandVectors.1 (BandPackingSymmetryQuadrupleAction ginv r
            (if BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))) → ((pFixed.1 - pSelected.1 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).1) → ((pFixed.2 - pSelected.2 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).2) → ((BandPackingSymmetryQuadrupleAction ginv
            r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ =
            Cᵢ.1.1)))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma r j hparentPositive
      transportedRotation selectedSlope ginv hcircleL selectedSupport t hrj hcent hslopeRe
      hslopeIm hmarked hOfixed pSelected pFixed t' hOFixedInv hcentInv hslopeReInv hslopeImInv
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  calc
    (BandPackingSymmetryQuadrupleAction ginv r)
        (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ =
        BandPackingSymmetryCircleAction ginv (r j.succ) := by
          by_cases hrev : BandPackingSymmetryReversesOrientation ginv <;>
            fin_cases j <;>
            simp [BandPackingSymmetryQuadrupleAction,
              hrev, neg1, neg2]
    _ = BandPackingSymmetryCircleAction ginv bundle.normalizedFixedCircle.1.1 :=
        congrArg (BandPackingSymmetryCircleAction ginv) hrj
    _ = Cᵢ.1.1 := by
        rw [bundle.normalized_fixed_circle_eq]
        exact hcircleL Cᵢ.1.1

private theorem hOFixedOriginalAt1498 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → ((∀ (h : PartialOdometer),
            BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → (∀ (r : Fin (4 :
            ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (TileOdometer
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ) (BandPackingSymmetryTileAction ginv
            bundle.normalizedFixed) (BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction)) → (((BandPackingSymmetryQuadrupleAction ginv r) (if
            BandPackingSymmetryReversesOrientation ginv then -j else j).succ = Cᵢ.1.1) →
            (TileOdometer Cᵢ.1.1 Tᵢ hᵢ)))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv htileL hfunL r j hOFixedInv hfixedCoord
  have h := hOFixedInv
  change TileOdometer
    ((BandPackingSymmetryQuadrupleAction ginv r)
      (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
    (BandPackingSymmetryTileAction ginv bundle.normalizedFixed)
    (BandPackingSymmetryPartialOdometerAction ginv bundle.normalizedFixedFunction) at h
  rw [hfixedCoord, bundle.normalized_fixed_eq, htileL,
    bundle.normalized_fixed_function_eq, hfunL] at h
  exact h

private theorem hcentOriginalAt1510 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), ∀ (t' : Fin (4 : ℕ)),
            (TileCentroid (BandPackingSymmetryTileAction ginv bundle.normalizedFixed) -
            TileCentroid (BandPackingSymmetryTileAction ginv selectedSupport) = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t' : ℕ) * (BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ) (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin
            (4 : ℕ))) + BandVectors.1 (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)))) →
            (TileCentroid Tᵢ - TileCentroid T' = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ t'.val * (BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv r)
            (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) + BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) ((BandPackingSymmetryQuadrupleAction
            ginv r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ))))) )
            := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv htileL selectedSupport T' r j t' hcentInv
  simpa [T', bundle.normalized_fixed_eq, htileL] using hcentInv

private theorem hnewAdjAt1521 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry),
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), (ProperBandQuadruple r) →
            (∀ (pSelected : ℝ × ℝ), ∀ (pFixed : ℝ × ℝ), ∀ (t' : Fin (4 : ℕ)),
            (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction ginv
            selectedFunction) = some pSelected) → ((pFixed.1 - pSelected.1 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).1) → ((pFixed.2 - pSelected.2 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv r (if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r (if BandPackingSymmetryReversesOrientation
            ginv = true then -j else j).succ)))).2) → (((BandPackingSymmetryQuadrupleAction ginv
            r) 0 = inverseCircle.1.1) → (((BandPackingSymmetryQuadrupleAction ginv r) (if
            BandPackingSymmetryReversesOrientation ginv then -j else j).succ = Cᵢ.1.1) →
            ((TileOdometer inverseCircle.1.1 T' h') → ((TileOdometer Cᵢ.1.1 Tᵢ hᵢ) →
            ((PartialOdometerSlope hᵢ = some pFixed) → ((TileCentroid Tᵢ - TileCentroid T' = (1 /
            2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ t'.val * (BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv r) (if
            BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) + BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) ((BandPackingSymmetryQuadrupleAction
            ginv r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)))) →
            (SubtileLatticeAdjacent inverseCircle Cᵢ T' Tᵢ h' hᵢ)))))))))) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv inversePresentation inverseSlot hinverseProper
      hinversePositive inverseCircle selectedSupport selectedFunction T' h' r j hr pSelected
      pFixed t' hslopeSelectedInv hslopeReInv hslopeImInv hselectedCoord hfixedCoord
      hOSelectedOriginal hOFixedOriginal hslopeFixedOriginal hcentOriginal
  refine ⟨hOSelectedOriginal, hOFixedOriginal, pSelected, pFixed,
    hslopeSelectedInv, hslopeFixedOriginal, ?_⟩
  exact ⟨BandPackingSymmetryQuadrupleAction ginv r,
    (if BandPackingSymmetryReversesOrientation ginv then -j else j),
    t', BandPackingSymmetryProperCovariance ginv r hr,
    hselectedCoord, hfixedCoord, hcentOriginal, hslopeReInv, hslopeImInv⟩

private theorem hpointInvAt1538 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (v : GaussianInt), BandPackingSymmetryVectorAction ginv
            (BandPackingSymmetryVectorAction bundle.symmetry v) = v) →
            ((BandPackingSymmetryVectorAction bundle.symmetry x = bundle.normalizedPoint) →
            (BandPackingSymmetryVectorAction ginv bundle.normalizedPoint = x)) ) := by
  classical
  intro C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv hvecL hpoint
  rw [← hpoint]
  exact hvecL x

private theorem hmarkedOriginalAt1545 :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (delta : Bool), ∀ (transportedRotation : Fin (4 : ℕ)),
        let oldUR := TileTranslation T₀
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)))
        let rowUR := TileTranslation bundle.normalizedRoot
          ((⟨0, 1⟩ : GaussianInt) ^ transportedRotation.val *
            (if Even transportedRotation.val then
              BandVectors.1 (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)
            else BandVectors.1 (normalizationPresentation (sigma i).succ) (normalizationPresentation
                0)))
        (x ∈ FootprintVertices oldUR ↔ bundle.normalizedPoint ∈ FootprintVertices rowUR) → (∀
            (ginv : BandPackingSymmetry),
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)), ∀ (t : Fin (4 : ℕ)),
            (bundle.normalizedPoint ∈ FootprintVertices (TileTranslation bundle.normalizedRoot
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑transportedRotation : ℕ) * if Even
            (↑transportedRotation : ℕ) then BandVectors.1 (normalizationPresentation (0 : Fin (4
            : ℕ))) (normalizationPresentation (sigma i).succ) else BandVectors.1
            (normalizationPresentation (sigma i).succ) (normalizationPresentation (0 : Fin (4 :
            ℕ))))) ↔ bundle.normalizedPoint ∈ FootprintVertices (TileTranslation (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t :
            ℕ) * if Even (↑t : ℕ) then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r j.succ) else
            BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ)))))) → (∀ (t' : Fin (4 : ℕ)), (t' = if
            BandPackingSymmetryReversesOrientation ginv = true then -t - (1 : Fin (4 : ℕ)) + if
            delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else t + if delta = true
            then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) → (
        (BandPackingSymmetryVectorAction ginv bundle.normalizedPoint = x) →
            ((bundle.normalizedPoint ∈ FootprintVertices (TileTranslation selectedSupport ((⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) * if Even (↑t : ℕ) then BandVectors.1 (r (0 :
            Fin (4 : ℕ))) (r j.succ) else BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))))) ↔
            BandPackingSymmetryVectorAction ginv bundle.normalizedPoint ∈ FootprintVertices
            (TileTranslation (BandPackingSymmetryTileAction ginv selectedSupport) ((⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt) ^ (↑(if BandPackingSymmetryReversesOrientation ginv = true then
            -t - (1 : Fin (4 : ℕ)) + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 :
            ℕ)) else t + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) : ℕ) * if
            Even (↑(if BandPackingSymmetryReversesOrientation ginv = true then -t - (1 : Fin (4 :
            ℕ)) + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else t + if delta
            = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) : ℕ) then BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction ginv r ((fun (j : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation ginv = true then -j else j) j).succ) else
            BandVectors.1 (BandPackingSymmetryQuadrupleAction ginv r ((fun (j : Fin (3 : ℕ)) =>
            if BandPackingSymmetryReversesOrientation ginv = true then -j else j) j).succ)
            (BandPackingSymmetryQuadrupleAction ginv r (0 : Fin (4 : ℕ)))))) → (x ∈
            FootprintVertices oldUR ↔ x ∈ FootprintVertices (TileTranslation T' ((⟨0, 1⟩ :
            GaussianInt) ^ t'.val * (if Even t'.val then BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv r) 0) ((BandPackingSymmetryQuadrupleAction
            ginv r) (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ) else
            BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv r) (if
            BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
            ((BandPackingSymmetryQuadrupleAction ginv r) 0))))))))) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma delta
      transportedRotation oldUR rowUR hmarkedOld ginv selectedSupport T' r j t hmarked t' ht'
      hpointInv hmarkCov
  let companionReverse := TileTranslation selectedSupport
    ((⟨0, 1⟩ : GaussianInt) ^ t.val *
      (if Even t.val then BandVectors.1 (r 0) (r j.succ)
        else BandVectors.1 (r j.succ) (r 0)))
  calc
    x ∈ FootprintVertices oldUR ↔
        bundle.normalizedPoint ∈ FootprintVertices rowUR := hmarkedOld
    _ ↔ bundle.normalizedPoint ∈ FootprintVertices companionReverse := by
      simpa [rowUR, companionReverse] using hmarked
    _ ↔ BandPackingSymmetryVectorAction ginv bundle.normalizedPoint ∈
          FootprintVertices
            (TileTranslation (BandPackingSymmetryTileAction ginv selectedSupport)
              ((⟨0, 1⟩ : GaussianInt) ^ t'.val *
                (if Even t'.val then
                  BandVectors.1
                    ((BandPackingSymmetryQuadrupleAction ginv r) 0)
                    ((BandPackingSymmetryQuadrupleAction ginv r)
                      (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
                else BandVectors.1
                  ((BandPackingSymmetryQuadrupleAction ginv r)
                    (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
                    ((BandPackingSymmetryQuadrupleAction ginv r) 0)))) := by
        simpa [companionReverse, ht'] using hmarkCov
    _ ↔ x ∈ FootprintVertices
          (TileTranslation T'
            ((⟨0, 1⟩ : GaussianInt) ^ t'.val *
              (if Even t'.val then
                BandVectors.1
                  ((BandPackingSymmetryQuadrupleAction ginv r) 0)
                  ((BandPackingSymmetryQuadrupleAction ginv r)
                    (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
              else BandVectors.1
                ((BandPackingSymmetryQuadrupleAction ginv r)
                  (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ)
                ((BandPackingSymmetryQuadrupleAction ginv r) 0)))) := by
        rw [hpointInv]

end MarkedAdjacencyGeometry

namespace MarkedAdjacencyConclusions

private theorem leftAdjacencyCase :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ∀ (transportedRotation : Fin (4 : ℕ)),
        let oldUR := TileTranslation T₀
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)))
        (x ∈ FootprintVertices (TileTranslation T₀ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ)
            * if Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) ↔ bundle.normalizedPoint ∈
            FootprintVertices (TileTranslation bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑transportedRotation : ℕ) * if Even (↑transportedRotation : ℕ) then
            BandVectors.1 (BandPackingSymmetryQuadrupleAction bundle.symmetry q (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction bundle.symmetry q ((fun (j : Fin (3 : ℕ)) =>
            if BandPackingSymmetryReversesOrientation bundle.symmetry = true then -j else j)
            i).succ) else BandVectors.1 (BandPackingSymmetryQuadrupleAction bundle.symmetry q
            ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation bundle.symmetry
            = true then -j else j) i).succ) (BandPackingSymmetryQuadrupleAction bundle.symmetry q
            (0 : Fin (4 : ℕ)))))) → (∀ (C' : BandCircle), ∀ (selectedSlope : ℝ × ℝ),
            (PartialOdometerSlope (bundle.functions bundle.selectedSlot bundle.selectedSign) =
            some selectedSlope) → (∀ (ginv : BandPackingSymmetry), (∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction ginv (BandPackingSymmetryCircleAction bundle.symmetry
            C) = C) → ((∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → ((∀ (h : PartialOdometer),
            BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → ((∀ (g :
            BandPackingSymmetry), ∀ (c : CircleCoordinates), (BandPackingSymmetryCircleAction g
            c).1 = c.1) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : (0 :
            ℤ) < (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (if
            BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (C' = bundle.normalizedFixedCircle ∧ LeftLatticeAdjacent bundle.normalizedFixedCircle
            bundle.normalizedFixed (bundle.pieces bundle.selectedSlot bundle.selectedSign)
            bundle.normalizedFixedFunction (bundle.functions bundle.selectedSlot
            bundle.selectedSign) ∧ bundle.normalizedPoint ∉ FootprintVertices (TileTranslation
            bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑transportedRotation :
            ℕ) * if Even (↑transportedRotation : ℕ) then BandVectors.1 (normalizationPresentation
            (0 : Fin (4 : ℕ))) (normalizationPresentation (sigma i).succ) else BandVectors.1
            (normalizationPresentation (sigma i).succ) (normalizationPresentation (0 : Fin (4 :
            ℕ)))))) → (((inverseCircle = Cᵢ ∧ LeftLatticeAdjacent Cᵢ Tᵢ T' hᵢ h' ∧ x ∉
            FootprintVertices oldUR) ∨ (∃ (a₀ a' : ℝ × ℝ) (r : Fin 4 → CircleCoordinates) (j :
            Fin 3) (t : Fin 4), PartialOdometerSlope hᵢ = some a₀ ∧ PartialOdometerSlope h' =
            some a' ∧ ProperBandQuadruple r ∧ r 0 = Cᵢ.1.1 ∧ r j.succ = inverseCircle.1.1 ∧
            TileCentroid T' - TileCentroid Tᵢ = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ t.val * (BandVectors.1 (r j.succ) (r 0) + BandVectors.1 (r 0) (r
            j.succ))) ∧ a'.1 - a₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt) ^
            t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r 0) (r j.succ)))).1 ∧ a'.2
            - a₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
            (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r 0) (r j.succ)))).2 ∧
            SubtileLatticeAdjacent Cᵢ inverseCircle Tᵢ T' hᵢ h' ∧ (x ∈ FootprintVertices oldUR ↔
            x ∈ FootprintVertices (TileTranslation Tᵢ ((⟨0, 1⟩ : GaussianInt) ^ t.val * (if Even
            t.val then BandVectors.1 (r 0) (r j.succ) else BandVectors.1 (r j.succ) (r 0)))))) ∨
            (∃ (a₀ aᵢ : ℝ × ℝ) (r : Fin 4 → CircleCoordinates) (j : Fin 3) (t : Fin 4),
            PartialOdometerSlope h' = some a₀ ∧ PartialOdometerSlope hᵢ = some aᵢ ∧
            ProperBandQuadruple r ∧ r 0 = inverseCircle.1.1 ∧ r j.succ = Cᵢ.1.1 ∧ TileCentroid Tᵢ
            - TileCentroid T' = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ t.val *
            (BandVectors.1 (r j.succ) (r 0) + BandVectors.1 (r 0) (r j.succ))) ∧ aᵢ.1 - a₀.1 =
            ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.2 (r
            j.succ) (r 0) + BandVectors.2 (r 0) (r j.succ)))).1 ∧ aᵢ.2 - a₀.2 = ((1 / 2 : ℝ) •
            GaussianRealPoint ((-⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0)
            + BandVectors.2 (r 0) (r j.succ)))).2 ∧ SubtileLatticeAdjacent inverseCircle Cᵢ T' Tᵢ
            h' hᵢ ∧ (x ∈ FootprintVertices oldUR ↔ x ∈ FootprintVertices (TileTranslation T'
            ((⟨0, 1⟩ : GaussianInt) ^ t.val * (if Even t.val then BandVectors.1 (r 0) (r j.succ)
            else BandVectors.1 (r j.succ) (r 0))))))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g normalizationPresentation sigma transportedRotation
      oldUR hmarkedOld C' selectedSlope hslope' ginv hcircleL htileL hfunL actionCurvature
      inversePresentation inverseSlot hinverseProper hinversePositive inverseCircle
      hinverseCircle selectedSupport selectedFunction T' h' hleft
  rcases hleft with ⟨hCfixed, hleftAdj, hnotMarked⟩
  have hinverseCircleFixed := MarkedAdjacencyGeometry.hinverseCircleFixed C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
      bundle C' ginv hcircleL hinverseProper hinversePositive hinverseCircle hCfixed
  have hnotOriginal := MarkedAdjacencyGeometry.hnotOriginal C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle
      transportedRotation hmarkedOld hnotMarked
  rcases hleftAdj with ⟨hOFixed, hOSelected, pFixed, pSelected,
    hslopeFixed, hslopeSelected, hleftGeometry⟩
  have hpFixedEq := MarkedAdjacencyGeometry.hpFixedEq C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle pFixed
      hslopeFixed
  have hpSelectedEq := MarkedAdjacencyGeometry.hpSelectedEq C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle
      selectedSlope hslope' pSelected hslopeSelected
  rcases hleftGeometry with hunit | hpresented
  · rcases hunit with ⟨hcurvUnit, orientation, v, hunitStep,
      hcentUnit, hslopeUnitRe, hslopeUnitIm⟩
    have centroidCov := MarkedAdjacencyGeometry.centroidCov
    have hinverseUnitCurv := MarkedAdjacencyGeometry.hinverseUnitCurv C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
        bundle actionCurvature hcurvUnit
    have hcentUnitInv := MarkedAdjacencyGeometry.hcentUnitInv C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
        htileL v hcentUnit centroidCov
    let unitPositive :=
      ({1, -1, ⟨0, 1⟩, -⟨0, 1⟩, 1 + ⟨0, 1⟩,
        -(1 + ⟨0, 1⟩)} : Finset GaussianInt)
    let unitNegative :=
      ({1, -1, ⟨0, 1⟩, -⟨0, 1⟩, -1 + ⟨0, 1⟩,
        -(-1 + ⟨0, 1⟩)} : Finset GaussianInt)
    let matrixVector (c : CircleCoordinates) (w : GaussianInt) : ℝ × ℝ :=
      (((1 + (c.2.re : ℝ)) * (w.re : ℝ) +
          (c.2.im : ℝ) * (w.im : ℝ)) / 2,
        ((c.2.im : ℝ) * (w.re : ℝ) +
          (1 - (c.2.re : ℝ)) * (w.im : ℝ)) / 2)
    let slopeDifferenceAction : BandPackingSymmetry → GaussianInt →
        (ℝ × ℝ) → ℝ × ℝ :=
      BandPackingSymmetry.rec
        (fun _ d => d)
        (fun _ d => (-d.2, d.1))
        (fun _ d => (-d.1, d.2))
        (fun z w d =>
          (d.1 + (z.re : ℝ) * (w.re : ℝ) + (z.im : ℝ) * (w.im : ℝ),
            d.2 + (z.im : ℝ) * (w.re : ℝ) - (z.re : ℝ) * (w.im : ℝ)))
        (fun a b iha ihb w d =>
          iha (BandPackingSymmetryVectorAction b w) (ihb w d))
    have matrixCov := MarkedAdjacencyGeometry.matrixCov actionCurvature
    have slopeDiffCov := MarkedAdjacencyGeometry.slopeDiffCov actionCurvature centroidCov
        matrixCov
    have hinverseFixedCircleCoord := MarkedAdjacencyGeometry.hinverseFixedCircleCoord C₀ Cᵢ
        T₀ Tᵢ h₀ hᵢ x bundle ginv hcircleL
    have hmatrix00 := MarkedAdjacencyGeometry.hmatrix00
    have hmatrix01 := MarkedAdjacencyGeometry.hmatrix01
    have hmatrix10 := MarkedAdjacencyGeometry.hmatrix10
    have hmatrix11 := MarkedAdjacencyGeometry.hmatrix11
    have hdiffUnit := MarkedAdjacencyGeometry.hdiffUnit C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle pFixed
        pSelected hcurvUnit v hslopeUnitRe hslopeUnitIm hmatrix00 hmatrix01 hmatrix10
            hmatrix11
    have hinverseUnitStep := (MarkedAdjacencyGeometry.unitStepCov) ginv orientation v
        hunitStep
    rcases hinverseUnitStep with ⟨orientationInv, hunitStepInv⟩
    have hdiffUnitInv := slopeDiffCov ginv
      bundle.normalizedFixedCircle.1.1 bundle.normalizedFixed selectedSupport
      pFixed pSelected v hcurvUnit hcentUnit hdiffUnit
    have hmatrixInv0 :
        CircleMatrix Cᵢ 0 0 =
          (1 + ((Cᵢ.1.1.2).re : ℝ)) / 2 :=
      hmatrix00 Cᵢ hinverseUnitCurv
    have hmatrixInv1 :
        CircleMatrix Cᵢ 0 1 = ((Cᵢ.1.1.2).im : ℝ) / 2 :=
      hmatrix01 Cᵢ hinverseUnitCurv
    have hmatrixInv2 :
        CircleMatrix Cᵢ 1 0 = ((Cᵢ.1.1.2).im : ℝ) / 2 :=
      hmatrix10 Cᵢ hinverseUnitCurv
    have hmatrixInv3 :
        CircleMatrix Cᵢ 1 1 =
          (1 - ((Cᵢ.1.1.2).re : ℝ)) / 2 :=
      hmatrix11 Cᵢ hinverseUnitCurv
    have hcovFixed := BandPackingSymmetryTileOdometerCovariance ginv
      bundle.normalizedFixedCircle.1.1 bundle.normalizedFixed
      bundle.normalizedFixedFunction hOFixed
    have hcovSelected := BandPackingSymmetryTileOdometerCovariance ginv
      bundle.normalizedFixedCircle.1.1 selectedSupport selectedFunction hOSelected
    let pFixedInv := BandPackingSymmetrySlopeAction ginv
      bundle.normalizedFixed pFixed
    let pSelectedInv := BandPackingSymmetrySlopeAction ginv
      selectedSupport pSelected
    have hslopeFixedInv :
        PartialOdometerSlope
          (BandPackingSymmetryPartialOdometerAction ginv
            bundle.normalizedFixedFunction) = some pFixedInv :=
                MarkedAdjacencyGeometry.hslopeFixedInv C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv pFixed
                hslopeFixed (MarkedAdjacencyGeometry.fixedCells C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle
                hOFixed pFixed hslopeFixed) hcovFixed
    have hslopeSelectedInv :
        PartialOdometerSlope
          (BandPackingSymmetryPartialOdometerAction ginv selectedFunction) =
            some pSelectedInv := MarkedAdjacencyGeometry.hslopeSelectedInv C₀ Cᵢ T₀ Tᵢ h₀ hᵢ
                x bundle ginv pSelected hslopeSelected (MarkedAdjacencyGeometry.selectedCells
                C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hOSelected pSelected hslopeSelected) hcovSelected
    have hOFixedOriginal := MarkedAdjacencyGeometry.hOFixedOriginalAt1198 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
        bundle ginv htileL hfunL hinverseFixedCircleCoord hcovFixed
    have hOSelectedOriginal := MarkedAdjacencyGeometry.hOSelectedOriginalAt1209 C₀ Cᵢ T₀ Tᵢ
        h₀ hᵢ x bundle ginv hinverseFixedCircleCoord hcovSelected
    have hslopeFixedOriginal : PartialOdometerSlope hᵢ = some pFixedInv := by
      simpa [bundle.normalized_fixed_function_eq, hfunL] using hslopeFixedInv
    have hslopeSelectedOriginal : PartialOdometerSlope h' = some pSelectedInv := by
      simpa [h', hfunL] using hslopeSelectedInv
    have hleftInv := MarkedAdjacencyGeometry.hleftInvAt1222 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
        pFixed pSelected v hinverseUnitCurv hcentUnitInv orientationInv hunitStepInv
        (MarkedAdjacencyGeometry.hdiffUnitInvFinal C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv pFixed
        pSelected v hinverseFixedCircleCoord (MarkedAdjacencyGeometry.hdiffUnitInv' C₀ Cᵢ T₀
        Tᵢ h₀ hᵢ x bundle ginv pFixed pSelected hcurvUnit v matrixCov hdiffUnitInv)
        (MarkedAdjacencyGeometry.htargetMatrix Cᵢ ginv v hmatrixInv0 hmatrixInv1 hmatrixInv2
        hmatrixInv3)) hOFixedOriginal hOSelectedOriginal hslopeFixedOriginal
        hslopeSelectedOriginal
    exact Or.inl ⟨hinverseCircleFixed, hleftInv, hnotOriginal⟩
  · rcases hpresented with
      ⟨qLeft, jLeft, eLeft, hqLeft, hqLeft0,
        hcentLeft, hslopeLeftRe, hslopeLeftIm⟩
    have hleftTransport :=
      LeftLatticeAdjacentPackingSymmetryTransport ginv qLeft hqLeft
        jLeft eLeft bundle.normalizedFixed selectedSupport
        bundle.normalizedFixedFunction selectedFunction pFixed pSelected
        (MarkedAdjacencyGeometry.hOFixedq C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hOFixed qLeft hqLeft0)
            (MarkedAdjacencyGeometry.hOSelectedq C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hOSelected qLeft
            hqLeft0) hslopeFixed hslopeSelected hcentLeft
        hslopeLeftRe hslopeLeftIm
    dsimp at hleftTransport
    rcases hleftTransport with
      ⟨negative, pFixedInv, pSelectedInv, hphaseLeft,
        hOFixedInv, hOSelectedInv, hslopeFixedInv, hslopeSelectedInv,
        hcentLeftInv, hslopeLeftReInv, hslopeLeftImInv, hcompatLeft⟩
    have hleftRootCoord := MarkedAdjacencyGeometry.hleftRootCoord C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle
        ginv hcircleL qLeft hqLeft0
    have hOFixedOriginal := MarkedAdjacencyGeometry.hOFixedOriginalAt1264 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
        bundle ginv htileL hfunL qLeft hOFixedInv hleftRootCoord
    have hOSelectedOriginal := MarkedAdjacencyGeometry.hOSelectedOriginalAt1274 C₀ Cᵢ T₀ Tᵢ
        h₀ hᵢ x bundle ginv qLeft hOSelectedInv hleftRootCoord
    have hslopeFixedOriginal : PartialOdometerSlope hᵢ = some pFixedInv := by
      simpa [bundle.normalized_fixed_function_eq, hfunL] using hslopeFixedInv
    have hleftInv := MarkedAdjacencyGeometry.hleftInvAt1283 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
        htileL qLeft jLeft eLeft hqLeft negative pFixedInv pSelectedInv hslopeSelectedInv
        hcentLeftInv hslopeLeftReInv hslopeLeftImInv hleftRootCoord hOFixedOriginal
        hOSelectedOriginal hslopeFixedOriginal
    exact Or.inl ⟨hinverseCircleFixed, hleftInv, hnotOriginal⟩

private theorem forwardAdjacencyCase :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ((∀ (g : BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (C' : CircleCoordinates), ∀
            (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), TileSubodometer C C' T T' h h' ↔ TileSubodometer
            (BandPackingSymmetryCircleAction g C) (BandPackingSymmetryCircleAction g C')
            (BandPackingSymmetryTileAction g T) (BandPackingSymmetryTileAction g T')
            (BandPackingSymmetryPartialOdometerAction g h)
            (BandPackingSymmetryPartialOdometerAction g h')) ∧ (∀ (g : BandPackingSymmetry), ∀ (x
            : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j ∈ U.cells) ↔
            ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell (BandPackingSymmetryVectorAction g x)
            j ∈ (BandPackingSymmetryTileAction g T).cells ∨ LatticeVertexIncidentCell
            (BandPackingSymmetryVectorAction g x) j ∈ (BandPackingSymmetryTileAction g U).cells)
            ∧ ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            ProperBandQuadruple q → ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (delta : Bool),
            BandPackingSymmetryScopedPhase g q delta → ∀ (T : ProtoTile), ∀ (x : GaussianInt),
        let q' := BandPackingSymmetryQuadrupleAction g q;
        let sigma := fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j;
        let s' := if BandPackingSymmetryReversesOrientation g = true then -s - (1 : Fin (4 : ℕ))
            + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s + if delta =
            true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ));
        let oldRight := TileTranslation T ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if
            Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1
            (q i.succ) (q (0 : Fin (4 : ℕ))));
        let newRight := TileTranslation (BandPackingSymmetryTileAction g T) ((⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt) ^ (↑s' : ℕ) * if Even (↑s' : ℕ) then BandVectors.1 (q' (0 : Fin (4 :
            ℕ))) (q' (sigma i).succ) else BandVectors.1 (q' (sigma i).succ) (q' (0 : Fin (4 :
            ℕ)))); BandPackingSymmetryTileAction g oldRight = newRight ∧ (x ∈ FootprintVertices
            oldRight ↔ BandPackingSymmetryVectorAction g x ∈ FootprintVertices newRight)) → (
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        ∀ (transportedRotation : Fin (4 : ℕ)),
        let oldUR := TileTranslation T₀
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)))
        (x ∈ FootprintVertices (TileTranslation T₀ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ)
            * if Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) ↔ bundle.normalizedPoint ∈
            FootprintVertices (TileTranslation bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑transportedRotation : ℕ) * if Even (↑transportedRotation : ℕ) then
            BandVectors.1 (BandPackingSymmetryQuadrupleAction bundle.symmetry q (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction bundle.symmetry q ((fun (j : Fin (3 : ℕ)) =>
            if BandPackingSymmetryReversesOrientation bundle.symmetry = true then -j else j)
            i).succ) else BandVectors.1 (BandPackingSymmetryQuadrupleAction bundle.symmetry q
            ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation bundle.symmetry
            = true then -j else j) i).succ) (BandPackingSymmetryQuadrupleAction bundle.symmetry q
            (0 : Fin (4 : ℕ)))))) → (∀ (C' : BandCircle), ∀ (selectedSlope : ℝ × ℝ), (C'.1.1 =
            bundle.normalizedPresentation bundle.selectedSlot.succ) → ((PartialOdometerSlope
            (bundle.functions bundle.selectedSlot bundle.selectedSign) = some selectedSlope) → (∀
            (ginv : BandPackingSymmetry), (∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction ginv (BandPackingSymmetryCircleAction bundle.symmetry
            C) = C) → ((∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → ((∀ (v : GaussianInt),
            BandPackingSymmetryVectorAction ginv (BandPackingSymmetryVectorAction bundle.symmetry
            v) = v) → ((∀ (h : PartialOdometer), BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : (0 :
            ℤ) < (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (if
            BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (BandPackingSymmetryVectorAction bundle.symmetry x = bundle.normalizedPoint) → ((∃ (q :
            Fin (4 : ℕ) → CircleCoordinates) (j : Fin (3 : ℕ)) (t : Fin (4 : ℕ)),
            ProperBandQuadruple q ∧ q (0 : Fin (4 : ℕ)) = bundle.normalizedFixedCircle.1.1 ∧ q
                j.succ = C'.1.1 ∧ TileCentroid
            (bundle.pieces bundle.selectedSlot bundle.selectedSign) - TileCentroid
            bundle.normalizedFixed = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * (BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ))) ∧ selectedSlope.1 -
            bundle.normalizedFixedSlope.1 = (1 / 2 : ℝ) * (GaussianRealPoint ((-(⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ)))).1 ∧ selectedSlope.2 -
            bundle.normalizedFixedSlope.2 = (1 / 2 : ℝ) * (GaussianRealPoint ((-(⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ)))).2 ∧ SubtileLatticeAdjacent
            bundle.normalizedFixedCircle C' bundle.normalizedFixed (bundle.pieces
            bundle.selectedSlot bundle.selectedSign) bundle.normalizedFixedFunction
            (bundle.functions bundle.selectedSlot bundle.selectedSign) ∧ (bundle.normalizedPoint
            ∈ FootprintVertices (TileTranslation bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑transportedRotation : ℕ) * if Even (↑transportedRotation : ℕ) then
            BandVectors.1 (normalizationPresentation (0 : Fin (4 : ℕ)))
            (normalizationPresentation (sigma i).succ) else BandVectors.1
            (normalizationPresentation (sigma i).succ) (normalizationPresentation (0 : Fin (4 :
            ℕ))))) ↔ bundle.normalizedPoint ∈ FootprintVertices (TileTranslation
            bundle.normalizedFixed ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) * if Even (↑t :
            ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) else BandVectors.1 (q j.succ)
            (q (0 : Fin (4 : ℕ))))))) → (((inverseCircle = Cᵢ ∧ LeftLatticeAdjacent Cᵢ Tᵢ T' hᵢ
            h' ∧ x ∉ FootprintVertices oldUR) ∨ (∃ (a₀ a' : ℝ × ℝ) (r : Fin 4 →
            CircleCoordinates) (j : Fin 3) (t : Fin 4), PartialOdometerSlope hᵢ = some a₀ ∧
            PartialOdometerSlope h' = some a' ∧ ProperBandQuadruple r ∧ r 0 = Cᵢ.1.1 ∧ r j.succ =
            inverseCircle.1.1 ∧ TileCentroid T' - TileCentroid Tᵢ = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.1 (r j.succ) (r 0) +
            BandVectors.1 (r 0) (r j.succ))) ∧ a'.1 - a₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r
            0) (r j.succ)))).1 ∧ a'.2 - a₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r 0) (r
            j.succ)))).2 ∧ SubtileLatticeAdjacent Cᵢ inverseCircle Tᵢ T' hᵢ h' ∧ (x ∈
            FootprintVertices oldUR ↔ x ∈ FootprintVertices (TileTranslation Tᵢ ((⟨0, 1⟩ :
            GaussianInt) ^ t.val * (if Even t.val then BandVectors.1 (r 0) (r j.succ) else
            BandVectors.1 (r j.succ) (r 0)))))) ∨ (∃ (a₀ aᵢ : ℝ × ℝ) (r : Fin 4 →
            CircleCoordinates) (j : Fin 3) (t : Fin 4), PartialOdometerSlope h' = some a₀ ∧
            PartialOdometerSlope hᵢ = some aᵢ ∧ ProperBandQuadruple r ∧ r 0 = inverseCircle.1.1 ∧
            r j.succ = Cᵢ.1.1 ∧ TileCentroid Tᵢ - TileCentroid T' = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.1 (r j.succ) (r 0) +
            BandVectors.1 (r 0) (r j.succ))) ∧ aᵢ.1 - a₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r
            0) (r j.succ)))).1 ∧ aᵢ.2 - a₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r 0) (r
            j.succ)))).2 ∧ SubtileLatticeAdjacent inverseCircle Cᵢ T' Tᵢ h' hᵢ ∧ (x ∈
            FootprintVertices oldUR ↔ x ∈ FootprintVertices (TileTranslation T' ((⟨0, 1⟩ :
            GaussianInt) ^ t.val * (if Even t.val then BandVectors.1 (r 0) (r j.succ) else
            BandVectors.1 (r j.succ) (r 0)))))))))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g sigma markedData normalizationPresentation
      transportedRotation oldUR hmarkedOld C' selectedSlope hC' hslope' ginv hcircleL htileL
      hvecL hfunL inversePresentation inverseSlot hinverseProper hinversePositive inverseCircle
      hinverseCircle selectedSupport selectedFunction T' h' hpoint hforward
  rcases hforward with
    ⟨r, j, t, hr, hr0, hrj, hcent, hslopeRe, hslopeIm,
      hadj, hmarked⟩
  have hparentPositive := MarkedAdjacencyGeometry.hparentPositiveAt1298 C' r j hrj
  have hOfixed := MarkedAdjacencyGeometry.hOfixedAt1301 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle r hr0
  have hOselected := MarkedAdjacencyGeometry.hOselectedAt1305 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C'
      hC' r j hrj
  have inverseAdjacency :=
    SubtileLatticeAdjacentPackingSymmetryTransport ginv r hr j t
      hparentPositive bundle.normalizedFixed selectedSupport
      bundle.normalizedFixedFunction selectedFunction
      bundle.normalizedFixedSlope selectedSlope
      hOfixed hOselected
      bundle.normalized_fixed_slope hslope'
      hcent hslopeRe hslopeIm
  dsimp at inverseAdjacency
  rcases inverseAdjacency with
    ⟨delta, pFixed, pSelected, t', hphaseInv, ht',
      hOFixedInv, hOSelectedInv, hslopeFixedInv, hslopeSelectedInv,
      hcentInv, hslopeReInv, hslopeImInv, hcompat⟩
  have hOFixedOriginal := MarkedAdjacencyGeometry.hOFixedOriginalAt1322 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
      bundle ginv hcircleL htileL hfunL r hr0 hOFixedInv
  have hselectedCoord :
        (BandPackingSymmetryQuadrupleAction ginv r)
            (if BandPackingSymmetryReversesOrientation ginv then -j else j).succ =
          inverseCircle.1.1 := MarkedAdjacencyGeometry.hselectedCoordAt1327 C₀ Cᵢ q i T₀ Tᵢ
              h₀ hᵢ x bundle r j hparentPositive transportedRotation C' selectedSlope ginv
              hinverseProper hinversePositive hinverseCircle t hrj hcent hslopeRe hslopeIm
              hmarked hOselected pFixed pSelected t' hOSelectedInv hcentInv hslopeReInv
              hslopeImInv
  have hOSelectedOriginal : TileOdometer inverseCircle.1.1 T' h' := by
    simpa [hselectedCoord, h', T'] using hOSelectedInv
  have hslopeFixedOriginal : PartialOdometerSlope hᵢ = some pFixed := by
    simpa [bundle.normalized_fixed_function_eq, hfunL] using hslopeFixedInv
  have hcentOriginal := MarkedAdjacencyGeometry.hcentOriginalAt1348 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
      bundle ginv htileL r j t' hcentInv
  have hrootCoord := MarkedAdjacencyGeometry.hrootCoord C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
      hcircleL r hr0
  have hnewAdj := MarkedAdjacencyGeometry.hnewAdjAt1371 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
      hinverseProper hinversePositive r j hr pFixed pSelected t' hslopeSelectedInv
      hslopeReInv hslopeImInv hOFixedOriginal hselectedCoord hOSelectedOriginal
      hslopeFixedOriginal hcentOriginal hrootCoord
  refine Or.inr (Or.inl ⟨pFixed, pSelected,
    BandPackingSymmetryQuadrupleAction ginv r,
    (if BandPackingSymmetryReversesOrientation ginv then -j else j),
    t', hslopeFixedOriginal, hslopeSelectedInv,
    BandPackingSymmetryProperCovariance ginv r hr, hrootCoord,
    hselectedCoord, hcentOriginal, hslopeReInv, hslopeImInv,
    hnewAdj, ?_⟩)
  let companionForward := TileTranslation bundle.normalizedFixed
    ((⟨0, 1⟩ : GaussianInt) ^ t.val *
      (if Even t.val then BandVectors.1 (r 0) (r j.succ)
        else BandVectors.1 (r j.succ) (r 0)))
  have hpointInv := MarkedAdjacencyGeometry.hpointInvAt1389 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
      hvecL hpoint
  have hmarkCov :=
    (markedData.2.2 ginv r hr j t delta hphaseInv
      bundle.normalizedFixed bundle.normalizedPoint).2
  have hmarkedOriginal := MarkedAdjacencyGeometry.hmarkedOriginalAt1396 C₀ Cᵢ q i s T₀ Tᵢ h₀
      hᵢ x bundle delta transportedRotation hmarkedOld ginv htileL r j t hmarked t' ht'
      hpointInv hmarkCov
  exact hmarkedOriginal

private theorem reverseAdjacencyCase :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (Cᵢ : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (h₀ :
            PartialOdometer), ∀ (hᵢ : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x),
        let g := bundle.symmetry
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        ((∀ (g : BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (C' : CircleCoordinates), ∀
            (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), TileSubodometer C C' T T' h h' ↔ TileSubodometer
            (BandPackingSymmetryCircleAction g C) (BandPackingSymmetryCircleAction g C')
            (BandPackingSymmetryTileAction g T) (BandPackingSymmetryTileAction g T')
            (BandPackingSymmetryPartialOdometerAction g h)
            (BandPackingSymmetryPartialOdometerAction g h')) ∧ (∀ (g : BandPackingSymmetry), ∀ (x
            : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j ∈ U.cells) ↔
            ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell (BandPackingSymmetryVectorAction g x)
            j ∈ (BandPackingSymmetryTileAction g T).cells ∨ LatticeVertexIncidentCell
            (BandPackingSymmetryVectorAction g x) j ∈ (BandPackingSymmetryTileAction g U).cells)
            ∧ ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            ProperBandQuadruple q → ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (delta : Bool),
            BandPackingSymmetryScopedPhase g q delta → ∀ (T : ProtoTile), ∀ (x : GaussianInt),
        let q' := BandPackingSymmetryQuadrupleAction g q;
        let sigma := fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j;
        let s' := if BandPackingSymmetryReversesOrientation g = true then -s - (1 : Fin (4 : ℕ))
            + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s + if delta =
            true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ));
        let oldRight := TileTranslation T ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if
            Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1
            (q i.succ) (q (0 : Fin (4 : ℕ))));
        let newRight := TileTranslation (BandPackingSymmetryTileAction g T) ((⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt) ^ (↑s' : ℕ) * if Even (↑s' : ℕ) then BandVectors.1 (q' (0 : Fin (4 :
            ℕ))) (q' (sigma i).succ) else BandVectors.1 (q' (sigma i).succ) (q' (0 : Fin (4 :
            ℕ)))); BandPackingSymmetryTileAction g oldRight = newRight ∧ (x ∈ FootprintVertices
            oldRight ↔ BandPackingSymmetryVectorAction g x ∈ FootprintVertices newRight)) → (
        let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
        ∀ (transportedRotation : Fin (4 : ℕ)),
        let oldUR := TileTranslation T₀
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then BandVectors.1 (q 0) (q i.succ)
              else BandVectors.1 (q i.succ) (q 0)))
        (x ∈ FootprintVertices (TileTranslation T₀ ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ)
            * if Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) ↔ bundle.normalizedPoint ∈
            FootprintVertices (TileTranslation bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑transportedRotation : ℕ) * if Even (↑transportedRotation : ℕ) then
            BandVectors.1 (BandPackingSymmetryQuadrupleAction bundle.symmetry q (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction bundle.symmetry q ((fun (j : Fin (3 : ℕ)) =>
            if BandPackingSymmetryReversesOrientation bundle.symmetry = true then -j else j)
            i).succ) else BandVectors.1 (BandPackingSymmetryQuadrupleAction bundle.symmetry q
            ((fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation bundle.symmetry
            = true then -j else j) i).succ) (BandPackingSymmetryQuadrupleAction bundle.symmetry q
            (0 : Fin (4 : ℕ)))))) → (∀ (C' : BandCircle), ∀ (selectedSlope : ℝ × ℝ), (C'.1.1 =
            bundle.normalizedPresentation bundle.selectedSlot.succ) → ((PartialOdometerSlope
            (bundle.functions bundle.selectedSlot bundle.selectedSign) = some selectedSlope) → (∀
            (ginv : BandPackingSymmetry), (∀ (C : CircleCoordinates),
            BandPackingSymmetryCircleAction ginv (BandPackingSymmetryCircleAction bundle.symmetry
            C) = C) → ((∀ (T : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T) = T) → ((∀ (v : GaussianInt),
            BandPackingSymmetryVectorAction ginv (BandPackingSymmetryVectorAction bundle.symmetry
            v) = v) → ((∀ (h : PartialOdometer), BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) = h) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : (0 :
            ℤ) < (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (if
            BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ).1),
        let inverseCircle : BandCircle :=
            ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (BandPackingSymmetryVectorAction bundle.symmetry x = bundle.normalizedPoint) → ((∃ (q :
            Fin (4 : ℕ) → CircleCoordinates) (j : Fin (3 : ℕ)) (t : Fin (4 : ℕ)),
            ProperBandQuadruple q ∧ q (0 : Fin (4 : ℕ)) = C'.1.1 ∧ q j.succ =
            bundle.normalizedFixedCircle.1.1 ∧
            TileCentroid bundle.normalizedFixed - TileCentroid (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ^ (↑t : ℕ) * (BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ))) ∧ bundle.normalizedFixedSlope.1 -
            selectedSlope.1 = (1 / 2 : ℝ) * (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ)))).1 ∧ bundle.normalizedFixedSlope.2 -
            selectedSlope.2 = (1 / 2 : ℝ) * (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt)) ^ (↑t : ℕ) * (BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ))) +
            BandVectors.2 (q (0 : Fin (4 : ℕ))) (q j.succ)))).2 ∧ SubtileLatticeAdjacent C'
            bundle.normalizedFixedCircle (bundle.pieces bundle.selectedSlot bundle.selectedSign)
            bundle.normalizedFixed (bundle.functions bundle.selectedSlot bundle.selectedSign)
            bundle.normalizedFixedFunction ∧ (bundle.normalizedPoint ∈ FootprintVertices
            (TileTranslation bundle.normalizedRoot ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^
            (↑transportedRotation : ℕ) * if Even (↑transportedRotation : ℕ) then BandVectors.1
            (normalizationPresentation (0 : Fin (4 : ℕ))) (normalizationPresentation (sigma
            i).succ) else BandVectors.1 (normalizationPresentation (sigma i).succ)
            (normalizationPresentation (0 : Fin (4 : ℕ))))) ↔ bundle.normalizedPoint ∈
            FootprintVertices (TileTranslation (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑t : ℕ) * if Even (↑t :
            ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) else BandVectors.1 (q j.succ)
            (q (0 : Fin (4 : ℕ))))))) → (((inverseCircle = Cᵢ ∧ LeftLatticeAdjacent Cᵢ Tᵢ T' hᵢ
            h' ∧ x ∉ FootprintVertices oldUR) ∨ (∃ (a₀ a' : ℝ × ℝ) (r : Fin 4 →
            CircleCoordinates) (j : Fin 3) (t : Fin 4), PartialOdometerSlope hᵢ = some a₀ ∧
            PartialOdometerSlope h' = some a' ∧ ProperBandQuadruple r ∧ r 0 = Cᵢ.1.1 ∧ r j.succ =
            inverseCircle.1.1 ∧ TileCentroid T' - TileCentroid Tᵢ = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.1 (r j.succ) (r 0) +
            BandVectors.1 (r 0) (r j.succ))) ∧ a'.1 - a₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r
            0) (r j.succ)))).1 ∧ a'.2 - a₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r 0) (r
            j.succ)))).2 ∧ SubtileLatticeAdjacent Cᵢ inverseCircle Tᵢ T' hᵢ h' ∧ (x ∈
            FootprintVertices oldUR ↔ x ∈ FootprintVertices (TileTranslation Tᵢ ((⟨0, 1⟩ :
            GaussianInt) ^ t.val * (if Even t.val then BandVectors.1 (r 0) (r j.succ) else
            BandVectors.1 (r j.succ) (r 0)))))) ∨ (∃ (a₀ aᵢ : ℝ × ℝ) (r : Fin 4 →
            CircleCoordinates) (j : Fin 3) (t : Fin 4), PartialOdometerSlope h' = some a₀ ∧
            PartialOdometerSlope hᵢ = some aᵢ ∧ ProperBandQuadruple r ∧ r 0 = inverseCircle.1.1 ∧
            r j.succ = Cᵢ.1.1 ∧ TileCentroid Tᵢ - TileCentroid T' = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.1 (r j.succ) (r 0) +
            BandVectors.1 (r 0) (r j.succ))) ∧ aᵢ.1 - a₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
            ((-⟨0, 1⟩ : GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r
            0) (r j.succ)))).1 ∧ aᵢ.2 - a₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint ((-⟨0, 1⟩ :
            GaussianInt) ^ t.val * (BandVectors.2 (r j.succ) (r 0) + BandVectors.2 (r 0) (r
            j.succ)))).2 ∧ SubtileLatticeAdjacent inverseCircle Cᵢ T' Tᵢ h' hᵢ ∧ (x ∈
            FootprintVertices oldUR ↔ x ∈ FootprintVertices (TileTranslation T' ((⟨0, 1⟩ :
            GaussianInt) ^ t.val * (if Even t.val then BandVectors.1 (r 0) (r j.succ) else
            BandVectors.1 (r j.succ) (r 0)))))))))))))))))) ) := by
  classical
  intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle g sigma markedData normalizationPresentation
      transportedRotation oldUR hmarkedOld C' selectedSlope hC' hslope' ginv hcircleL htileL
      hvecL hfunL inversePresentation inverseSlot hinverseProper hinversePositive inverseCircle
      hinverseCircle selectedSupport selectedFunction T' h' hpoint hreverse
  rcases hreverse with
    ⟨r, j, t, hr, hr0, hrj, hcent, hslopeRe, hslopeIm,
      hadj, hmarked⟩
  have hparentPositive := MarkedAdjacencyGeometry.hparentPositiveAt1447 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
      bundle r j hrj
  have hOselected := MarkedAdjacencyGeometry.hOselectedAt1450 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C'
      hC' r hr0
  have hOfixed := MarkedAdjacencyGeometry.hOfixedAt1453 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle r j hrj
  have inverseAdjacency :=
    SubtileLatticeAdjacentPackingSymmetryTransport ginv r hr j t
      hparentPositive selectedSupport bundle.normalizedFixed
      selectedFunction bundle.normalizedFixedFunction selectedSlope
      bundle.normalizedFixedSlope hOselected hOfixed hslope'
      bundle.normalized_fixed_slope hcent hslopeRe hslopeIm
  dsimp at inverseAdjacency
  rcases inverseAdjacency with
    ⟨delta, pSelected, pFixed, t', hphaseInv, ht',
      hOSelectedInv, hOFixedInv, hslopeSelectedInv, hslopeFixedInv,
      hcentInv, hslopeReInv, hslopeImInv, hcompat⟩
  have hselectedCoord :
      (BandPackingSymmetryQuadrupleAction ginv r) 0 = inverseCircle.1.1 :=
          MarkedAdjacencyGeometry.hselectedCoordAt1468 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle C' ginv
          hinverseProper hinversePositive hinverseCircle r hr0
  have hfixedCoord := MarkedAdjacencyGeometry.hfixedCoord C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle r j
      hparentPositive transportedRotation selectedSlope ginv hcircleL t hrj hcent hslopeRe
      hslopeIm hmarked hOfixed pSelected pFixed t' hOFixedInv hcentInv hslopeReInv hslopeImInv
  have hOSelectedOriginal : TileOdometer inverseCircle.1.1 T' h' := by
    simpa [hselectedCoord, T', h'] using hOSelectedInv
  have hOFixedOriginal := MarkedAdjacencyGeometry.hOFixedOriginalAt1498 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
      bundle ginv htileL hfunL r j hOFixedInv hfixedCoord
  have hslopeFixedOriginal : PartialOdometerSlope hᵢ = some pFixed := by
    simpa [bundle.normalized_fixed_function_eq, hfunL] using hslopeFixedInv
  have hcentOriginal := MarkedAdjacencyGeometry.hcentOriginalAt1510 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
      bundle ginv htileL r j t' hcentInv
  have hnewAdj := MarkedAdjacencyGeometry.hnewAdjAt1521 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
      hinverseProper hinversePositive r j hr pSelected pFixed t' hslopeSelectedInv
      hslopeReInv hslopeImInv hselectedCoord hfixedCoord hOSelectedOriginal hOFixedOriginal
      hslopeFixedOriginal hcentOriginal
  refine Or.inr (Or.inr ⟨pSelected, pFixed,
    BandPackingSymmetryQuadrupleAction ginv r,
    (if BandPackingSymmetryReversesOrientation ginv then -j else j),
    t', hslopeSelectedInv, hslopeFixedOriginal,
    BandPackingSymmetryProperCovariance ginv r hr, hselectedCoord,
    hfixedCoord, hcentOriginal, hslopeReInv, hslopeImInv, hnewAdj, ?_⟩)
  let companionReverse := TileTranslation selectedSupport
    ((⟨0, 1⟩ : GaussianInt) ^ t.val *
      (if Even t.val then BandVectors.1 (r 0) (r j.succ)
        else BandVectors.1 (r j.succ) (r 0)))
  have hpointInv := MarkedAdjacencyGeometry.hpointInvAt1538 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
      hvecL hpoint
  have hmarkCov :=
    (markedData.2.2 ginv r hr j t delta hphaseInv
      selectedSupport bundle.normalizedPoint).2
  have hmarkedOriginal := MarkedAdjacencyGeometry.hmarkedOriginalAt1545 C₀ Cᵢ q i s T₀ Tᵢ h₀
      hᵢ x bundle delta transportedRotation hmarkedOld ginv r j t hmarked t' ht' hpointInv
      hmarkCov
  exact hmarkedOriginal

end MarkedAdjacencyConclusions

theorem MarkedOdometerAdjacencyReduction :
    (∀ (C : BandCircle) (T T₀ : ProtoTile) (h h₀ : PartialOdometer)
        (x : GaussianInt),
      ¬ ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
            BandPackingSymmetryCircleAction g
              (FordCircleCoordinate P.p P.q) = C.1.1) ∨
          (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
            BandPackingSymmetryCircleAction g
              (DiamondRecursiveQuadruple K 0) = C.1.1)) →
      RightLatticeAdjacent C T T₀ h h₀ →
      x ∈ h.domain → x ∈ h₀.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h.domain ∨ y ∈ h₀.domain) →
      ∃ (C' : BandCircle) (T' : ProtoTile) (h' : PartialOdometer)
          (p₀ p' : ℝ × ℝ) (q : Fin 4 → CircleCoordinates)
          (i : Fin 3) (s : Fin 4),
        TileSubodometer C.1.1 C'.1.1 T T' h h' ∧
        PartialOdometerSlope h₀ = some p₀ ∧
        PartialOdometerSlope h' = some p' ∧
        ProperBandQuadruple q ∧ q 0 = C.1.1 ∧ q i.succ = C'.1.1 ∧
        TileCentroid T' - TileCentroid T₀ =
          (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val *
              (BandVectors.1 (q i.succ) (q 0) +
               BandVectors.1 (q 0) (q i.succ))) ∧
        p'.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.2 (q i.succ) (q 0) +
             BandVectors.2 (q 0) (q i.succ)))).1 ∧
        p'.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.2 (q i.succ) (q 0) +
             BandVectors.2 (q 0) (q i.succ)))).2 ∧
        SubtileLatticeAdjacent C C' T₀ T' h₀ h' ∧
        x ∈ h₀.domain ∧ x ∈ h'.domain ∧
        (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ h₀.domain ∨ y ∈ h'.domain) ∧
        Int.toNat C.1.1.1 + Int.toNat C'.1.1.1 <
          Int.toNat C.1.1.1 + Int.toNat C.1.1.1 ∧
        (¬ (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
              z = x - 1 - ⟨0, 1⟩ → z ∈ T.cells ∨ z ∈ T₀.cells) ↔
          x ∈ FootprintVertices
            (TileTranslation T₀
              ((⟨0, 1⟩ : GaussianInt) ^ s.val *
                (if Even s.val then BandVectors.1 (q 0) (q i.succ)
                  else BandVectors.1 (q i.succ) (q 0)))))) ∧
    ∀ (C₀ Cᵢ : BandCircle) (q : Fin 4 → CircleCoordinates)
        (i : Fin 3) (s : Fin 4) (T₀ Tᵢ : ProtoTile)
        (h₀ hᵢ : PartialOdometer) (x : GaussianInt) (p₀ pᵢ : ℝ × ℝ),
      ¬ ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
            BandPackingSymmetryCircleAction g
              (FordCircleCoordinate P.p P.q) = C₀.1.1) ∨
          (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
            BandPackingSymmetryCircleAction g
              (DiamondRecursiveQuadruple K 0) = C₀.1.1)) →
      ProperBandQuadruple q → q 0 = C₀.1.1 → q i.succ = Cᵢ.1.1 →
      PartialOdometerSlope h₀ = some p₀ →
      PartialOdometerSlope hᵢ = some pᵢ →
      TileCentroid Tᵢ - TileCentroid T₀ =
        (1 / 2 : ℝ) • GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
             BandVectors.1 (q 0) (q i.succ))) →
      pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).1 →
      pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.2 (q i.succ) (q 0) +
           BandVectors.2 (q 0) (q i.succ)))).2 →
      SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ →
      x ∈ h₀.domain → x ∈ hᵢ.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h₀.domain ∨ y ∈ hᵢ.domain) →
      let oldUR := TileTranslation T₀
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q 0) (q i.succ)
            else BandVectors.1 (q i.succ) (q 0)))
      ∃ (C' : BandCircle) (T' : ProtoTile) (h' : PartialOdometer),
        TileSubodometer C₀.1.1 C'.1.1 T₀ T' h₀ h' ∧
        x ∈ hᵢ.domain ∧ x ∈ h'.domain ∧
        (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ hᵢ.domain ∨ y ∈ h'.domain) ∧
        Int.toNat Cᵢ.1.1.1 + Int.toNat C'.1.1.1 <
          Int.toNat C₀.1.1.1 + Int.toNat Cᵢ.1.1.1 ∧
        ((C' = Cᵢ ∧ LeftLatticeAdjacent Cᵢ Tᵢ T' hᵢ h' ∧
            x ∉ FootprintVertices oldUR) ∨
          (∃ (a₀ a' : ℝ × ℝ) (r : Fin 4 → CircleCoordinates)
              (j : Fin 3) (t : Fin 4),
            PartialOdometerSlope hᵢ = some a₀ ∧
            PartialOdometerSlope h' = some a' ∧
            ProperBandQuadruple r ∧ r 0 = Cᵢ.1.1 ∧
            r j.succ = C'.1.1 ∧
            TileCentroid T' - TileCentroid Tᵢ =
              (1 / 2 : ℝ) • GaussianRealPoint
                ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                  (BandVectors.1 (r j.succ) (r 0) +
                   BandVectors.1 (r 0) (r j.succ))) ∧
            a'.1 - a₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (r j.succ) (r 0) +
                 BandVectors.2 (r 0) (r j.succ)))).1 ∧
            a'.2 - a₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (r j.succ) (r 0) +
                 BandVectors.2 (r 0) (r j.succ)))).2 ∧
            SubtileLatticeAdjacent Cᵢ C' Tᵢ T' hᵢ h' ∧
            (x ∈ FootprintVertices oldUR ↔
              x ∈ FootprintVertices
                (TileTranslation Tᵢ
                  ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                    (if Even t.val then BandVectors.1 (r 0) (r j.succ)
                      else BandVectors.1 (r j.succ) (r 0)))))) ∨
          (∃ (a₀ aᵢ : ℝ × ℝ) (r : Fin 4 → CircleCoordinates)
              (j : Fin 3) (t : Fin 4),
            PartialOdometerSlope h' = some a₀ ∧
            PartialOdometerSlope hᵢ = some aᵢ ∧
            ProperBandQuadruple r ∧ r 0 = C'.1.1 ∧
            r j.succ = Cᵢ.1.1 ∧
            TileCentroid Tᵢ - TileCentroid T' =
              (1 / 2 : ℝ) • GaussianRealPoint
                ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                  (BandVectors.1 (r j.succ) (r 0) +
                   BandVectors.1 (r 0) (r j.succ))) ∧
            aᵢ.1 - a₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (r j.succ) (r 0) +
                 BandVectors.2 (r 0) (r j.succ)))).1 ∧
            aᵢ.2 - a₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
              ((-⟨0, 1⟩ : GaussianInt) ^ t.val *
                (BandVectors.2 (r j.succ) (r 0) +
                 BandVectors.2 (r 0) (r j.succ)))).2 ∧
            SubtileLatticeAdjacent C' Cᵢ T' Tᵢ h' hᵢ ∧
            (x ∈ FootprintVertices oldUR ↔
              x ∈ FootprintVertices
                (TileTranslation T'
                  ((⟨0, 1⟩ : GaussianInt) ^ t.val *
                    (if Even t.val then BandVectors.1 (r 0) (r j.succ)
                      else BandVectors.1 (r j.succ) (r 0))))))) := by
-- BODY
  constructor
  · exact P5630T1MarkedRightOdometerAdjacencyReduction
  · intro C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x p₀ pᵢ horbit hq hq₀ hqᵢ
      hslope₀ hslopeᵢ hcentroid hslopex hslopey hadj hx₀ hxᵢ hstar
    have inversePhase := BandPackingSymmetryInversePhaseCancellation
    have markedData := BandPackingSymmetryMarkedDataCovariance
    dsimp
    obtain ⟨bundle, subtilePlacement, hsubtilePlacement⟩ :=
      BandOrderedGeneralSubtileNormalizedBundleExists
        C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x p₀ pᵢ horbit hq hq₀ hqᵢ
        hslope₀ hslopeᵢ hcentroid hslopex hslopey hadj hx₀ hxᵢ hstar
    obtain ⟨selectedEdge, hxSelectedEdge, hselectedEdge, selectedRow⟩ :=
        BandOrderedGeneralRoutedSelectedContact
          bundle.normalizedPresentation bundle.configuration
          bundle.normalizedCircle bundle.normalizedRoot subtilePlacement.layout
          subtilePlacement.exteriorIndex subtilePlacement.centralIndex
          bundle.normalizedPoint (bundle.routedDirection + 2)
          subtilePlacement.exterior_index subtilePlacement.central_index
          subtilePlacement.exterior_routed_cell
          (by
            have hdir : bundle.routedDirection + 2 + 2 =
                bundle.routedDirection := by omega
            simpa [hdir] using subtilePlacement.central_routed_cell)
          subtilePlacement.selected_star
    obtain ⟨row⟩ := selectedRow
    have hO₀ : TileOdometer C₀.1.1 T₀ h₀ := hadj.1
    have hOᵢ : TileOdometer Cᵢ.1.1 Tᵢ hᵢ := hadj.2.1
    let g := bundle.symmetry
    let normalizationPresentation := BandPackingSymmetryQuadrupleAction g q
    let sigma : Fin 3 → Fin 3 := fun j =>
      if BandPackingSymmetryReversesOrientation g then -j else j
    have hparentPositive := MarkedAdjacencyGeometry.hparentPositiveAt344 Cᵢ q i hqᵢ
    have hO₀q := MarkedAdjacencyGeometry.hO₀q C₀ q T₀ h₀ hq₀ hO₀
    have hOᵢq := MarkedAdjacencyGeometry.hOᵢq Cᵢ q i Tᵢ hᵢ hqᵢ hOᵢ
    obtain ⟨delta, transportedRootSlope, transportedFixedSlope, transportedRotation,
      hphaseForward, hrotationForward, hrootOdometer, hfixedOdometer,
      hrootSlope, hfixedSlope, hcentroidForward, hslopeXForward,
      hslopeYForward, hcompatForward⟩ :=
      SubtileLatticeAdjacentPackingSymmetryTransport g q hq i s hparentPositive
        T₀ Tᵢ h₀ hᵢ p₀ pᵢ hO₀q hOᵢq hslope₀ hslopeᵢ
        hcentroid hslopex hslopey
    have hnorm := MarkedAdjacencyGeometry.hnormAt360 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle
    have htransportRootSlopeEq := MarkedAdjacencyGeometry.htransportRootSlopeEq C₀ Cᵢ T₀ Tᵢ h₀ hᵢ
        x bundle transportedRootSlope hrootSlope
    have htransportFixedSlopeEq := MarkedAdjacencyGeometry.htransportFixedSlopeEq C₀ Cᵢ T₀ Tᵢ h₀
        hᵢ x bundle transportedFixedSlope hfixedSlope
    have hnormalizedProper : ProperBandQuadruple normalizationPresentation :=
      BandPackingSymmetryProperCovariance g q hq
    let oldUR := TileTranslation T₀
      ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0)))
    let rowUR := TileTranslation bundle.normalizedRoot
      ((⟨0, 1⟩ : GaussianInt) ^ transportedRotation.val *
        (if Even transportedRotation.val then
          BandVectors.1 (normalizationPresentation 0) (normalizationPresentation (sigma i).succ)
        else BandVectors.1 (normalizationPresentation (sigma i).succ) (normalizationPresentation
            0)))
    have hmarkedTransport :=
      markedData.2.2 g q hq i s delta hphaseForward T₀ x
    have hmarkedOld := MarkedAdjacencyGeometry.hmarkedOld C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x bundle delta
        transportedRotation hmarkedTransport (MarkedAdjacencyGeometry.hrowUR C₀ Cᵢ q i s T₀ Tᵢ h₀
        hᵢ x bundle delta transportedRotation hrotationForward)
    have subtileGeometry := BandOrderedGeneralSubtileSelectedRowGeometry
        C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle subtilePlacement selectedEdge
        hxSelectedEdge hselectedEdge row (MarkedAdjacencyGeometry.hnormalizedOrbit C₀ Cᵢ T₀ Tᵢ h₀
            hᵢ x horbit bundle)
        normalizationPresentation (sigma i) transportedRotation
        hnormalizedProper (MarkedAdjacencyGeometry.hr₀ C₀ Cᵢ q T₀ Tᵢ h₀ hᵢ x hq₀ bundle hnorm)
            (MarkedAdjacencyGeometry.hrᵢ C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x p₀ pᵢ hqᵢ hcentroid hslopex
            hslopey bundle hparentPositive hOᵢq transportedRootSlope transportedFixedSlope
            transportedRotation hfixedOdometer hcentroidForward hslopeXForward hslopeYForward)
        (MarkedAdjacencyGeometry.hnormalizedCentroid C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle
            transportedRotation hcentroidForward)
        (MarkedAdjacencyGeometry.hnormalizedSlopeX C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle
            transportedRootSlope transportedFixedSlope transportedRotation hslopeXForward
            htransportRootSlopeEq htransportFixedSlopeEq)
            (MarkedAdjacencyGeometry.hnormalizedSlopeY C₀ Cᵢ q i T₀ Tᵢ h₀ hᵢ x bundle
            transportedRootSlope transportedFixedSlope transportedRotation hslopeYForward
            htransportRootSlopeEq htransportFixedSlopeEq)
    dsimp at subtileGeometry
    rcases subtileGeometry with
      ⟨C', selectedSlope, hC', hsub', hslope', hxFixed', hxSelected',
        hstar', hsize', hrowOutput⟩
    obtain ⟨ginv, hcircleL, hcircleR, hquadL, hquadR, htileL,
      htileR, hvecL, hvecR, hfunL, hfunR, hphase⟩ :=
      (BandPackingSymmetryInversePhaseCancellation.2 bundle.symmetry)
    have hnorm := MarkedAdjacencyGeometry.hnormAt536 C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle
    have actionCurvature := MarkedAdjacencyGeometry.actionCurvature
    let inversePresentation :=
      BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
    let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
        -bundle.selectedSlot else bundle.selectedSlot
    have hinverseProper : ProperBandQuadruple inversePresentation :=
      BandPackingSymmetryProperCovariance ginv bundle.normalizedPresentation
        bundle.configuration.proper
    have hinverseCoordinate := MarkedAdjacencyGeometry.hinverseCoordinate C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
        bundle C' hC' ginv
    have hinversePositive := MarkedAdjacencyGeometry.hinversePositive C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle
        C' ginv actionCurvature hinverseCoordinate
    let inverseCircle : BandCircle :=
        ⟨⟨inversePresentation inverseSlot.succ,
        ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
          ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
    have hinverseCircle : inverseCircle.1.1 =
        BandPackingSymmetryCircleAction ginv C'.1.1 := hinverseCoordinate
    let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
    let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
    let T' := BandPackingSymmetryTileAction ginv selectedSupport
    let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
    have inverseDomain := MarkedAdjacencyGeometry.inverseDomain C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle ginv
        hvecL
    have hpoint : BandPackingSymmetryVectorAction bundle.symmetry x =
        bundle.normalizedPoint := bundle.normalized_point_eq.symm
    refine ⟨inverseCircle, T', h', (MarkedAdjacencyGeometry.hsubInverse C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
        bundle markedData C' ginv hcircleL htileL hfunL hinverseProper hinversePositive
        hinverseCircle (MarkedAdjacencyGeometry.hsubNormalized C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hnorm
        C' hsub')), (MarkedAdjacencyGeometry.hxFixedOriginal C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hxFixed'
        ginv hfunL inverseDomain hpoint),
      (MarkedAdjacencyGeometry.hxSelectedOriginal C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hxSelected' ginv
          inverseDomain hpoint), (MarkedAdjacencyGeometry.hstarOriginal C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x
          bundle hstar' ginv hfunL inverseDomain hpoint (MarkedAdjacencyGeometry.mapStar)),
          (MarkedAdjacencyGeometry.hsizeOriginal C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x bundle hnorm C' hsize' ginv
          actionCurvature hinverseProper hinversePositive hinverseCircle), ?_⟩
    rcases hrowOutput with hleft | hforward | hreverse
    · have leftAdjacencyCase := MarkedAdjacencyConclusions.leftAdjacencyCase C₀ Cᵢ q i s T₀ Tᵢ h₀
        hᵢ x bundle transportedRotation hmarkedOld C' selectedSlope hslope' ginv hcircleL htileL
        hfunL actionCurvature hinverseProper hinversePositive hinverseCircle hleft
      exact leftAdjacencyCase
    · have forwardAdjacencyCase := MarkedAdjacencyConclusions.forwardAdjacencyCase C₀ Cᵢ q i s T₀
        Tᵢ h₀ hᵢ x bundle markedData transportedRotation hmarkedOld C' selectedSlope hC' hslope'
        ginv hcircleL htileL hvecL hfunL hinverseProper hinversePositive hinverseCircle hpoint
        hforward
      exact forwardAdjacencyCase
    · have reverseAdjacencyCase := MarkedAdjacencyConclusions.reverseAdjacencyCase C₀ Cᵢ q i s T₀
        Tᵢ h₀ hᵢ x bundle markedData transportedRotation hmarkedOld C' selectedSlope hC' hslope'
        ginv hcircleL htileL hvecL hfunL hinverseProper hinversePositive hinverseCircle hpoint
        hreverse
      exact reverseAdjacencyCase

end ApollonianSuperharmonic

end
