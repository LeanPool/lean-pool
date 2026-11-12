/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileInterfaceCertificateExists
public import
    LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileNormalizationCertificateExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSubtileRoutingCertificateExists

-- [TABLET NODE: BandOrderedGeneralSubtileNormalizedBundleExists]

/-!
# BandOrderedGeneralSubtileNormalizedBundleExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralSubtileNormalizedBundleExists
    (C₀ Cᵢ : BandCircle) (q : Fin 4 → CircleCoordinates)
    (i : Fin 3) (s : Fin 4) (T₀ Tᵢ : ProtoTile)
    (h₀ hᵢ : PartialOdometer) (x : GaussianInt) (p₀ pᵢ : ℝ × ℝ)
    (horbit :
      ¬ ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
              BandPackingSymmetryCircleAction g
                (FordCircleCoordinate P.p P.q) = C₀.1.1) ∨
            (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
              BandPackingSymmetryCircleAction g
                (DiamondRecursiveQuadruple K 0) = C₀.1.1)))
    (hq : ProperBandQuadruple q) (hq₀ : q 0 = C₀.1.1)
    (hqᵢ : q i.succ = Cᵢ.1.1)
    (hslope₀ : PartialOdometerSlope h₀ = some p₀)
    (hslopeᵢ : PartialOdometerSlope hᵢ = some pᵢ)
    (hcentroid : TileCentroid Tᵢ - TileCentroid T₀ =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (q i.succ) (q 0) +
           BandVectors.1 (q 0) (q i.succ))))
    (hslopex : pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) +
         BandVectors.2 (q 0) (q i.succ)))).1)
    (hslopey : pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) +
         BandVectors.2 (q 0) (q i.succ)))).2)
    (hadj : SubtileLatticeAdjacent C₀ Cᵢ T₀ Tᵢ h₀ hᵢ)
    (hx₀ : x ∈ h₀.domain) (hxᵢ : x ∈ hᵢ.domain)
    (hstar : ∀ y,
      y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h₀.domain ∨ y ∈ hᵢ.domain) :
    ∃ bundle :
        BandOrderedGeneralNormalizedOccurrenceBundle C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x,
      ∃ placement : BandOrderedGeneralSubtilePlacement
          bundle.normalizedPresentation bundle.configuration
          bundle.normalizedCircle bundle.normalizedFixedCircle
          bundle.normalizedRoot bundle.normalizedFixed
          bundle.normalizedRootFunction bundle.normalizedFixedFunction
          bundle.normalizedPoint bundle.pieces bundle.functions
          bundle.selectedSlot bundle.selectedSign bundle.routedDirection,
        bundle.placement = Sum.inr placement := by
-- BODY
  obtain ⟨normalization⟩ :=
    BandOrderedGeneralSubtileNormalizationCertificateExists
      C₀ Cᵢ q i s T₀ Tᵢ h₀ hᵢ x p₀ pᵢ horbit hq hq₀ hqᵢ
      hslope₀ hslopeᵢ hcentroid hslopex hslopey hadj hx₀ hxᵢ hstar
  obtain ⟨interface⟩ :=
    BandOrderedGeneralSubtileInterfaceCertificateExists normalization
  obtain ⟨routing⟩ :=
    BandOrderedGeneralSubtileRoutingCertificateExists interface
  let placement : BandOrderedGeneralSubtilePlacement
      normalization.normalizedPresentation normalization.configuration
      normalization.normalizedCircle normalization.normalizedFixedCircle
      normalization.normalizedRoot normalization.normalizedFixed
      normalization.normalizedRootFunction normalization.normalizedFixedFunction
      normalization.normalizedPoint normalization.pieces normalization.functions
      routing.selectedSlot routing.selectedSign routing.routedDirection :=
    { adjacency := normalization.adjacency
      layout := normalization.layout
      pieceIndex := normalization.pieceIndex
      piece_index_central := normalization.piece_index_central
      piece_layout_cells := normalization.piece_layout_cells
      piece_layout_empty_anchor := normalization.piece_layout_empty_anchor
      piece_layout_footprint := normalization.piece_layout_footprint
      piece_layout_domain := normalization.piece_layout_domain
      exteriorIndex := normalization.exteriorIndex
      centralIndex := routing.centralIndex
      exterior_index := normalization.exterior_index
      central_index := routing.central_index
      selected_central_index := routing.selected_central_index
      fixed_exterior_cells := normalization.fixed_exterior_cells
      fixed_exterior_empty_anchor := normalization.fixed_exterior_empty_anchor
      exterior_routed_cell := routing.exterior_routed_cell
      central_routed_cell := routing.central_routed_cell
      selected_star := routing.selected_star }
  let bundle : BandOrderedGeneralNormalizedOccurrenceBundle
      C₀ Cᵢ T₀ Tᵢ h₀ hᵢ x :=
    { presentation := q
      presentation_proper := normalization.presentation_proper
      presentation_child := normalization.presentation_child
      parentRotation := normalization.parentRotation
      symmetry := normalization.symmetry
      rotatedPresentation := normalization.rotatedPresentation
      rotated_presentation_eq := normalization.rotated_presentation_eq
      normalizedPresentation := normalization.normalizedPresentation
      normalized_presentation_eq := normalization.normalized_presentation_eq
      configuration := normalization.configuration
      normalizedCircle := normalization.normalizedCircle
      normalized_circle_eq := normalization.normalized_circle_eq
      normalizedFixedCircle := normalization.normalizedFixedCircle
      normalized_fixed_circle_eq := normalization.normalized_fixed_circle_eq
      normalizedRoot := normalization.normalizedRoot
      normalizedFixed := normalization.normalizedFixed
      normalizedRootFunction := normalization.normalizedRootFunction
      normalizedFixedFunction := normalization.normalizedFixedFunction
      normalizedPoint := normalization.normalizedPoint
      normalized_root_eq := normalization.normalized_root_eq
      normalized_fixed_eq := normalization.normalized_fixed_eq
      normalized_root_function_eq := normalization.normalized_root_function_eq
      normalized_fixed_function_eq := normalization.normalized_fixed_function_eq
      normalized_point_eq := normalization.normalized_point_eq
      normalized_root_odometer := normalization.normalized_root_odometer
      normalized_fixed_odometer := normalization.normalized_fixed_odometer
      normalizedRootSlope := normalization.normalizedRootSlope
      normalizedFixedSlope := normalization.normalizedFixedSlope
      normalized_root_slope := normalization.normalized_root_slope
      normalized_fixed_slope := normalization.normalized_fixed_slope
      pieces := normalization.pieces
      functions := normalization.functions
      root_band := normalization.root_band
      piece_odometer := normalization.piece_odometer
      piece_cell_cover := normalization.piece_cell_cover
      piece_footprint := normalization.piece_footprint
      piece_centroid := normalization.piece_centroid
      function_domain_cover := normalization.function_domain_cover
      function_restriction := normalization.function_restriction
      function_compatibility := normalization.function_compatibility
      piece_slope := normalization.piece_slope
      startCompanion := interface.startCompanion
      endCompanion := interface.endCompanion
      startData := interface.startData
      endData := interface.endData
      interface_endpoints := interface.interface_endpoints
      root_lattice := interface.root_lattice
      fixed_lattice := interface.fixed_lattice
      start_lattice := interface.start_lattice
      end_lattice := interface.end_lattice
      root_fixed_disjoint := interface.root_fixed_disjoint
      root_start_disjoint := interface.root_start_disjoint
      fixed_start_disjoint := interface.fixed_start_disjoint
      root_end_disjoint := interface.root_end_disjoint
      fixed_end_disjoint := interface.fixed_end_disjoint
      start_touching := interface.start_touching
      end_touching := interface.end_touching
      edgeAtPoint := routing.edgeAtPoint
      root_induced := routing.root_induced
      fixed_induced := routing.fixed_induced
      normalized_star := normalization.normalized_star
      routedDirection := routing.routedDirection
      routed_root_cell := routing.routed_root_cell
      routed_fixed_cell := routing.routed_fixed_cell
      selectedSlot := routing.selectedSlot
      selectedSign := routing.selectedSign
      selected_piece_cell := routing.selected_piece_cell
      placement := Sum.inr placement }
  exact ⟨bundle, placement, rfl⟩

end ApollonianSuperharmonic

end
