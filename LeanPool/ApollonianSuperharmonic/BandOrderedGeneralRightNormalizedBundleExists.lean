/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightInterfaceCertificateExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightNormalizationCertificateExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightRoutingCertificateExists

-- [TABLET NODE: BandOrderedGeneralRightNormalizedBundleExists]

/-!
# BandOrderedGeneralRightNormalizedBundleExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralRightNormalizedBundleExists
    (C : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (horbit :
      ¬ ((exists (g : BandPackingSymmetry) (P : FordFareyParameter),
              BandPackingSymmetryCircleAction g
                (FordCircleCoordinate P.p P.q) = C.1.1) \/
            (exists (g : BandPackingSymmetry) (K : DiamondParameter),
              BandPackingSymmetryCircleAction g
                (DiamondRecursiveQuadruple K 0) = C.1.1)))
    (hadj : RightLatticeAdjacent C T N h k)
    (hxT : x ∈ h.domain) (hxN : x ∈ k.domain)
    (hstar : forall y,
      y = x \/ y = x + 1 \/ y = x - 1 \/
        y = x + ⟨0, 1⟩ \/ y = x - ⟨0, 1⟩ ->
      y ∈ h.domain \/ y ∈ k.domain) :
    exists bundle :
        BandOrderedGeneralNormalizedOccurrenceBundle C C T N h k x,
      exists placement : BandOrderedGeneralRightPlacement
          bundle.normalizedPresentation bundle.configuration
          bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
          bundle.normalizedRootFunction bundle.normalizedFixedFunction
          bundle.normalizedPoint bundle.pieces bundle.functions
          bundle.selectedSlot bundle.selectedSign bundle.routedDirection,
        bundle.placement = Sum.inl placement := by
-- BODY
  obtain ⟨normalization⟩ :=
    BandOrderedGeneralRightNormalizationCertificateExists C T N h k x
      horbit hadj hxT hxN hstar
  obtain ⟨interface⟩ :=
    BandOrderedGeneralRightInterfaceCertificateExists normalization
  obtain ⟨routing⟩ :=
    BandOrderedGeneralRightRoutingCertificateExists interface
  let placement : BandOrderedGeneralRightPlacement
      normalization.normalizedPresentation normalization.configuration
      normalization.normalizedCircle normalization.normalizedRoot
      normalization.normalizedFixed normalization.normalizedRootFunction
      normalization.normalizedFixedFunction normalization.normalizedPoint
      normalization.pieces normalization.functions routing.selectedSlot
      routing.selectedSign routing.routedDirection :=
    { adjacency := normalization.adjacency
      layout := normalization.layout
      rightFirstSlot := normalization.rightFirstSlot
      rightSecondSlot := normalization.rightSecondSlot
      rightDirectionSlot := normalization.rightDirectionSlot
      right_slots_cyclic := normalization.right_slots_cyclic
      rightNeighborPositive := normalization.rightNeighborPositive
      rightRootSlope := normalization.normalizedRootSlope
      rightFixedSlope := normalization.normalizedFixedSlope
      right_root_slope := normalization.normalized_root_slope
      right_fixed_slope := normalization.normalized_fixed_slope
      right_adjacency_centroid := normalization.right_adjacency_centroid
      right_adjacency_slope_real := normalization.right_adjacency_slope_real
      right_adjacency_slope_imag := normalization.right_adjacency_slope_imag
      rightNeighborDisplacement := normalization.rightNeighborDisplacement
      right_neighbor_displacement := normalization.right_neighbor_displacement
      right_neighbor_cells := normalization.right_neighbor_cells
      right_neighbor_empty_anchor := normalization.right_neighbor_empty_anchor
      firstBoundarySign := normalization.firstBoundarySign
      secondBoundarySign := normalization.secondBoundarySign
      boundary_signs := normalization.boundary_signs
      first_boundary_cells := normalization.first_boundary_cells
      first_boundary_empty_anchor := normalization.first_boundary_empty_anchor
      first_boundary_footprint := normalization.first_boundary_footprint
      first_boundary_domain := normalization.first_boundary_domain
      second_boundary_cells := normalization.second_boundary_cells
      second_boundary_empty_anchor := normalization.second_boundary_empty_anchor
      second_boundary_footprint := normalization.second_boundary_footprint
      second_boundary_domain := normalization.second_boundary_domain
      selected_boundary_piece := routing.selected_boundary_piece
      exteriorIndex := routing.exteriorIndex
      centralIndex := routing.centralIndex
      exterior_index := routing.exterior_index
      central_index := routing.central_index
      selected_exterior_cells := routing.selected_exterior_cells
      selected_exterior_empty_anchor := routing.selected_exterior_empty_anchor
      selected_exterior_footprint := routing.selected_exterior_footprint
      selected_exterior_domain := routing.selected_exterior_domain
      exterior_routed_cell := routing.exterior_routed_cell
      central_routed_cell := routing.central_routed_cell
      selected_star := routing.selected_star }
  let bundle : BandOrderedGeneralNormalizedOccurrenceBundle C C T N h k x :=
    { presentation := normalization.presentation
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
      placement := Sum.inl placement }
  exact ⟨bundle, placement, rfl⟩

end ApollonianSuperharmonic

end
