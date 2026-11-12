/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.LatticeFundamentalSet
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: PeriodicTileCore]

/-!
# PeriodicTileCore

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An area-free periodic tile core consists of a locally finite,
$3$-connected cellular plane triangulation whose vertices index
topological-disk lattice tiles, together with a full-rank sublattice
$L\subseteq\mathbb Z[i]$ and an $L$-action on vertices and faces.  It has
finite sets of representatives for lattice-cell cosets and for the edge and
face orbits, and exactly one selected representative for every vertex orbit.
Translation by $u\in L$ translates every indexed
tile by $u$, preserves adjacency, translates the embedded vertex positions,
edge arcs, and face regions by the real vector represented by $u$, and sends
the three vertices of each face to the three vertices of the translated
face.

For every face $F$ the core selects a lattice vertex $\rho(F)$ common to
the footprints of its three tiles.  These selections are $L$-equivariant.
For each ordered pair $F,F'$ of distinct faces incident to one graph edge
$\{a,b\}$, it selects a possibly constant lattice-edge path from $\rho(F)$
to $\rho(F')$ whose vertices and actual footprint edges lie in the ordinary
intersection of the footprint graphs of the tiles indexed by $a$ and $b$.
The selected path for the reverse ordering is the reversed path, and all
selected paths are $L$-equivariant under termwise translation.
-/
structure PeriodicTileCore (ι : Type) where
-- BODY
  /-- The fixed locally finite cellular plane triangulation. -/
  plane : PlaneTriangulation ι
  /-- The literal lattice tile assigned to each graph vertex. -/
  tile : ι → ProtoTile
  /-- The full-rank additive lattice of tile periods. -/
  lattice : AddSubgroup GaussianInt
  /-- A complete finite set of lattice-cell coset representatives. -/
  latticeReps : Finset GaussianInt
  /-- Exactly one representative from each vertex translation orbit. -/
  vertexOrbitReps : Finset ι
  /-- A finite family representing every ordered graph edge under translation. -/
  edgeOrbitReps : Finset (ι × ι)
  /-- A finite family representing every face under translation. -/
  faceOrbitReps : Finset plane.Face
  /-- The action of a period on graph vertices. -/
  shift : lattice → ι → ι
  /-- The compatible action of a period on entire faces. -/
  faceShift : lattice → plane.Face → plane.Face
  lattice_full_rank : LatticeFundamentalSet lattice latticeReps
  tiles_are_disks : ∀ a, LatticeTile (tile a)
  shift_zero : ∀ a, shift 0 a = a
  shift_add : ∀ u v a, shift (u + v) a = shift u (shift v a)
  faceShift_zero : ∀ f, faceShift 0 f = f
  faceShift_add : ∀ u v f,
    faceShift (u + v) f = faceShift u (faceShift v f)
  tile_periodic : ∀ u : lattice, ∀ a,
    tile (shift u a) = TileTranslation (tile a) u
  edge_periodic : ∀ u : lattice, ∀ a b,
    plane.adjacent (shift u a) (shift u b) ↔ plane.adjacent a b
  face_vertices_periodic : ∀ u f i,
    plane.faceVertex (faceShift u f) i = shift u (plane.faceVertex f i)
  position_periodic : ∀ u : lattice, ∀ a,
    plane.position (shift u a) = plane.position a + GaussianRealPoint u
  edgeArc_periodic : ∀ u : lattice, ∀ a b,
    plane.edgeArc (shift u a) (shift u b) =
      (fun p => p + GaussianRealPoint u) '' plane.edgeArc a b
  faceRegion_periodic : ∀ u : lattice, ∀ f,
    plane.faceRegion (faceShift u f) =
      (fun p => p + GaussianRealPoint u) '' plane.faceRegion f
  vertex_orbit_representatives : ∀ a, ∃! r : ι,
    r ∈ vertexOrbitReps ∧ ∃ u : lattice, a = shift u r
  edge_orbit_representatives : ∀ a b, plane.adjacent a b →
    ∃ r ∈ edgeOrbitReps, ∃ u : lattice,
      a = shift u r.1 ∧ b = shift u r.2
  face_orbit_representatives : ∀ f, ∃ r ∈ faceOrbitReps,
    ∃ u : lattice, f = faceShift u r
  /-- The selected common footprint vertex of the three tiles at each face. -/
  rho : plane.Face → GaussianInt
  rho_common : ∀ f i,
    rho f ∈ FootprintVertices (tile (plane.faceVertex f i))
  rho_periodic : ∀ u : lattice, ∀ f,
    rho (faceShift u f) = rho f + u
  /--
  The contained lattice walk joining the selected points of two faces across their common
  edge.
  -/
  facePath : plane.Face → plane.Face → List GaussianInt
  facePath_reverse : ∀ f g, facePath g f = (facePath f g).reverse
  facePath_periodic : ∀ u : lattice, ∀ f g,
    facePath (faceShift u f) (faceShift u g) =
      (facePath f g).map (fun x => x + (u : GaussianInt))
  facePath_spec : ∀ a b, plane.adjacent a b →
    ∀ f g, f ≠ g →
      (∃ i, plane.faceVertex f i = a) →
      (∃ i, plane.faceVertex f i = b) →
      (∃ i, plane.faceVertex g i = a) →
      (∃ i, plane.faceVertex g i = b) →
      (facePath f g).head? = some (rho f) ∧
        (facePath f g).getLast? = some (rho g) ∧
        (∀ x ∈ facePath f g,
          x ∈ FootprintVertices (tile a) ∩ FootprintVertices (tile b)) ∧
        ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
          facePath f g = l₁ ++ x :: y :: l₂ →
          {x, y} ∈ FootprintEdges (tile a) ∩ FootprintEdges (tile b)

end ApollonianSuperharmonic

end
