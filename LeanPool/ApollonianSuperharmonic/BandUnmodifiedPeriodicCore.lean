/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandUnmodifiedCoreCertificate
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.P4677T2DrawingExists
public import LeanPool.ApollonianSuperharmonic.P4677T2IncidenceLedger
public import LeanPool.ApollonianSuperharmonic.P4677T2ThreeConnected
public import LeanPool.ApollonianSuperharmonic.P4677T2FacePoints
public import LeanPool.ApollonianSuperharmonic.P4677T2TouchingWalk
public import LeanPool.ApollonianSuperharmonic.P4677T2PrecursorWalk
public import LeanPool.ApollonianSuperharmonic.P4677T2PeriodicWalkAssembly
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.LatticeFundamentalSet
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: BandUnmodifiedPeriodicCore]

/-!
# BandUnmodifiedPeriodicCore

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandUnmodifiedPeriodicCore
    (P Q S : Fin 3 -> Bool -> ProtoTile) (u v : GaussianInt)
    (L : AddSubgroup GaussianInt) (R : Finset GaussianInt)
    (hu : u ∈ L) (hv : v ∈ L)
    (hfund : LatticeFundamentalSet L R)
    (hcoords : ∀ w : L, ∃! mn : Int × Int,
      ((mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v) =
        (w : GaussianInt))
    (hdisks : forall i s, LatticeTile (P i s))
    (hQcells : forall i s, (Q i s).cells ⊆ (P 0 true).cells)
    (hScells : forall i s, (S i s).cells ⊆ (P 0 false).cells)
    (hQfoot : forall i s,
      FootprintVertices (Q i s) ⊆ FootprintVertices (P 0 true))
    (hSfoot : forall i s,
      FootprintVertices (S i s) ⊆ FootprintVertices (P 0 false))
    (hcommon : (Q 0 false).cells = (S 0 true).cells)
    (hcommonAnchor : (Q 0 false).cells = ∅ ->
      (Q 0 false).anchor = (S 0 true).anchor)
    (hOdisk : (Q 0 false).cells.Nonempty -> LatticeTile (Q 0 false))
    (hprecursorFaces :
      TouchingTriple (Q 1 true) (S 2 false) (Q 0 false) ∧
      TouchingTriple (Q 2 true) (S 1 false) (Q 0 false))
    (hinner :
      TouchingTriple (Q 1 true) (S 2 false) (P 1 true) ∧
      TouchingTriple (Q 2 true) (S 1 false) (P 1 false) ∧
      TouchingTriple (Q 1 true) (P 1 true) (P 2 false) ∧
      TouchingTriple (S 1 false) (P 1 false) (P 2 true))
    (houter :
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) v)
          (TileTranslation (P 2 true) v) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) v)
          (P 2 false) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v))
          (TileTranslation (P 1 true) (u + v)) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v))
          (P 1 false) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 1 true) (u + v))
          (TileTranslation (P 2 true) v) ∧
      TouchingTriple (P 0 false) (TileTranslation (P 1 false) (-u - v))
          (TileTranslation (P 2 false) (-v)) ∧
      TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u))
          (TileTranslation (P 2 true) (-u)) ∧
      TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u))
          (P 2 false)) :
    ∃ K : BandUnmodifiedCoreCertificate P u v L,
      K.core.rho (K.faceEquiv.symm ⟨.I1, 0, 0⟩) ∈
          FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false) ∧
      K.core.rho (K.faceEquiv.symm ⟨.I2, 0, 0⟩) ∈
          FootprintVertices (Q 2 true) ∩ FootprintVertices (S 1 false) ∧
      K.core.rho (K.faceEquiv.symm ⟨.I3, 0, 0⟩) ∈
          FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) := by
-- BODY
  classical
  obtain ⟨D⟩ := P4677T2DrawingExists u v L hu hv hcoords
  obtain ⟨hsymm, hirrefl, hfinite, hdistinct, hedges, hfaces⟩ :=
    P4677T2IncidenceLedger
  obtain ⟨rho, hrho, hrhoper, hI1, hI2, hI3, hI4⟩ :=
    P4677T2FacePoints P Q S u v L D hQfoot hSfoot hinner houter
  have hAB := P4677T2PrecursorWalk
    (P 0 true) (P 0 false) (Q 1 true) (S 2 false)
    (Q 2 true) (S 1 false) (Q 0 false) (S 0 true)
    (rho ⟨.I1, 0, 0⟩) (rho ⟨.I2, 0, 0⟩)
    (hQcells 1 true) (hQcells 2 true) (hScells 2 false) (hScells 1 false)
    (hQcells 0 false) (hScells 0 true)
    (hQfoot 1 true) (hQfoot 2 true) (hSfoot 2 false) (hSfoot 1 false)
    (hQfoot 0 false) (hSfoot 0 true) hcommon hcommonAnchor hOdisk
    hprecursorFaces.1 hprecursorFaces.2 hI1 hI2
  obtain ⟨path, hreverse, hpathper, hpath⟩ :=
    P4677T2PeriodicWalkAssembly P Q S u v L D
      hQcells hScells hQfoot hSfoot hinner houter rho hrho hrhoper
      hI1 hI2 hI3 hI4 P4677T2TouchingWalk hAB
  have compose (T : ProtoTile) (a b : GaussianInt) :
      TileTranslation (TileTranslation T a) b = TileTranslation T (a + b) := by
    cases T
    simp only [TileTranslation, GaussianTranslation, Finset.image_image]
    congr 1
    · congr 1
      funext x
      exact add_assoc x a b
    · exact add_assoc _ a b
  have tile_periodic (w : L) (a : PeriodicSubtileIndex) :
      SubtileOccurrenceInterpretation P u v (D.shift w a) =
        TileTranslation (SubtileOccurrenceInterpretation P u v a) w := by
    rw [D.shift_eq]
    dsimp only [SubtileOccurrenceInterpretation]
    have hsum : ((a.first + (D.coordinates w).1 : Int) : GaussianInt) * u +
        ((a.second + (D.coordinates w).2 : Int) : GaussianInt) * v =
        (a.first : GaussianInt) * u + (a.second : GaussianInt) * v + w := by
      rw [← D.coordinates_spec w]
      push_cast
      ring
    rw [hsum, compose]
  have tile_disks (a : PeriodicSubtileIndex) :
      LatticeTile (SubtileOccurrenceInterpretation P u v a) := by
    rcases a with ⟨l, m, n⟩
    cases l <;> exact (TileDiskAreaCovariance _ _).1.mp (hdisks _ _)
  let plane : PlaneTriangulation PeriodicSubtileIndex := {
    adjacent := AllowedSubtileIncidence
    Face := PeriodicSubtileFaceIndex
    faceVertex := SixSubtileFaceVertices
    position := D.position
    edgeArc := D.edgeArc
    faceRegion := D.faceRegion
    adjacent_symmetric := hsymm
    adjacent_irreflexive := hirrefl
    locally_finite := hfinite
    three_connected := P4677T2ThreeConnected
    face_vertices_distinct := hdistinct
    face_edges := hedges
    every_edge_two_faces := hfaces
    position_injective := D.position_injective
    arc_symmetric := D.arc_symmetric
    arc_homeomorph := D.arc_homeomorph
    arc_intersections := D.arc_intersections
    region_open := D.region_open
    region_connected := D.region_connected
    region_disjoint := D.region_disjoint
    face_boundary := D.face_boundary
    plane_cover := D.plane_cover }
  let core : PeriodicTileCore PeriodicSubtileIndex := {
    plane := plane
    tile := SubtileOccurrenceInterpretation P u v
    lattice := L
    latticeReps := R
    vertexOrbitReps := D.vertexReps
    edgeOrbitReps := D.edgeReps
    faceOrbitReps := D.faceReps
    shift := D.shift
    faceShift := D.faceShift
    lattice_full_rank := hfund
    tiles_are_disks := tile_disks
    shift_zero := D.shift_zero
    shift_add := D.shift_add
    faceShift_zero := D.faceShift_zero
    faceShift_add := D.faceShift_add
    tile_periodic := tile_periodic
    edge_periodic := D.edge_periodic
    face_vertices_periodic := D.face_vertices_periodic
    position_periodic := D.position_periodic
    edgeArc_periodic := D.edgeArc_periodic
    faceRegion_periodic := D.faceRegion_periodic
    vertex_orbit_representatives := D.vertex_orbits
    edge_orbit_representatives := D.edge_orbits
    face_orbit_representatives := D.face_orbits
    rho := rho
    rho_common := hrho
    rho_periodic := hrhoper
    facePath := path
    facePath_reverse := hreverse
    facePath_periodic := hpathper
    facePath_spec := hpath }
  let K : BandUnmodifiedCoreCertificate P u v L := {
    core := core
    lattice_eq := rfl
    tile_eq := fun _ => rfl
    vertex_reps := D.vertex_reps
    adjacent_iff := fun _ _ => Iff.rfl
    faceEquiv := Equiv.refl _
    face_vertices := fun _ _ => rfl
    face_reps := D.face_reps
    latticeCoordinates := D.coordinates
    latticeCoordinates_spec := D.coordinates_spec
    face_shift := D.faceShift_eq }
  exact ⟨K, hI1, hI2, hI3⟩

end ApollonianSuperharmonic

end
