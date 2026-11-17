/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation

-- [TABLET NODE: BandUnmodifiedCoreCertificate]

/-!
# BandUnmodifiedCoreCertificate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A band unmodified-core certificate for six occurrences $S_i^\pm$, period
vectors $u,v$, and lattice $L$ is a `PeriodicTileCore` whose vertex
indexed at $(X,m,n)$ is exactly the occurrence prescribed by
`SubtileOccurrenceInterpretation`.  Its combinatorial adjacency
relation is exactly the fixed eighteen-edge ledger
`AllowedSubtileIncidence`; this field does not assert that every
pair having an isolated common footprint vertex is adjacent.  Its faces are equivariantly
identified with the translated twelve-face ledger of
`SixSubtileFaceVertices`.  The certificate also records integral
coordinates of every lattice translation and requires face translation to
add those coordinates to the complete face index.  Its selected vertex and
face orbit representatives are exactly the six and twelve indices with
translation coordinates $(0,0)$.  Consequently its face
orbits are exactly $I_1,\ldots,I_4,J_1,\ldots,J_8$ and its edge orbits are
exactly the eighteen unoriented rows generating allowed incidence.
Possible zero-dimensional contacts outside those rows are not additional
edges of this ledger.
-/
structure BandUnmodifiedCoreCertificate (S : Fin 3 -> Bool -> ProtoTile)
    (u v : GaussianInt) (L : AddSubgroup GaussianInt) where
-- BODY
  /-- The periodic core on the literal six-type occurrence indices. -/
  core : PeriodicTileCore PeriodicSubtileIndex
  lattice_eq : core.lattice = L
  tile_eq : forall o,
    core.tile o = SubtileOccurrenceInterpretation S u v o
  vertex_reps : forall o,
    o ∈ core.vertexOrbitReps <-> o.first = 0 ∧ o.second = 0
  adjacent_iff : forall a b,
    core.plane.adjacent a b <-> AllowedSubtileIncidence a b
  /-- Identify the core faces with the twelve translated face labels. -/
  faceEquiv : core.plane.Face ≃ PeriodicSubtileFaceIndex
  face_vertices : forall f i,
    core.plane.faceVertex f i = SixSubtileFaceVertices (faceEquiv f) i
  face_reps : forall f,
    f ∈ core.faceOrbitReps <->
      (faceEquiv f).first = 0 ∧ (faceEquiv f).second = 0
  /-- Integral coordinates of a period in the selected two-vector basis. -/
  latticeCoordinates : core.lattice -> Int × Int
  latticeCoordinates_spec : forall w,
    (latticeCoordinates w).1 * u + (latticeCoordinates w).2 * v =
      (w : GaussianInt)
  face_shift : forall w f,
    faceEquiv (core.faceShift w f) =
      { faceEquiv f with
        first := (faceEquiv f).first + (latticeCoordinates w).1
        second := (faceEquiv f).second + (latticeCoordinates w).2 }

end ApollonianSuperharmonic

end
