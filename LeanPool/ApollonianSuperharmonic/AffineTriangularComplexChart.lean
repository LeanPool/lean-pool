/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent

-- [TABLET NODE: AffineTriangularComplexChart]

/-!
# AffineTriangularComplexChart

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $P$ be a periodic tile complex and let
$\operatorname{tileAt}:\mathbb Z^2\to\mathcal T$ be a coordinate-indexed
family of prototiles.  An affine triangular complex chart for
$(P,\operatorname{tileAt})$ consists of a bijection
$\kappa:\mathbb Z^2\to V(P)$ and two face maps
$U,D:\mathbb Z^2\to F(P)$ with the following properties.  In chart
coordinates, adjacency is exactly `TriangularLatticeAdjacent`.
Both $U$ and $D$ are injective, their images are disjoint, and every face is
in exactly one of their images.  Writing $e_1=(1,0)$ and $e_2=(0,1)$, the
ordered incident vertices are exactly
$$
 U_x=(\kappa(x),\kappa(x+e_1),\kappa(x-e_2)),\qquad
 D_x=(\kappa(x),\kappa(x-e_1),\kappa(x+e_2)).
$$
Finally, the tile indexed by $\kappa(x)$ in $P$ is
$\operatorname{tileAt}(x)$ for every $x\in\mathbb Z^2$.
-/
structure AffineTriangularComplexChart {ι : Type}
    (P : PeriodicTileComplex ι) (tileAt : (Int × Int) → ProtoTile) where
-- BODY
  /-- Identify integer coordinate pairs with the vertices of the periodic complex. -/
  vertexEquiv : (Int × Int) ≃ ι
  adjacent_iff : ∀ x y,
    P.plane.adjacent (vertexEquiv x) (vertexEquiv y) ↔
      TriangularLatticeAdjacent x y
  /-- The upward face based at each integer coordinate pair. -/
  up : (Int × Int) → P.plane.Face
  /-- The downward face based at each integer coordinate pair. -/
  down : (Int × Int) → P.plane.Face
  up_injective : Function.Injective up
  down_injective : Function.Injective down
  up_ne_down : ∀ x y, up x ≠ down y
  face_exhaustive : ∀ f, (∃ x, f = up x) ∨ ∃ x, f = down x
  up_vertices : ∀ x,
    P.plane.faceVertex (up x) 0 = vertexEquiv x ∧
    P.plane.faceVertex (up x) 1 =
      vertexEquiv (x + ((1, 0) : Int × Int)) ∧
    P.plane.faceVertex (up x) 2 =
      vertexEquiv (x - ((0, 1) : Int × Int))
  down_vertices : ∀ x,
    P.plane.faceVertex (down x) 0 = vertexEquiv x ∧
    P.plane.faceVertex (down x) 1 =
      vertexEquiv (x - ((1, 0) : Int × Int)) ∧
    P.plane.faceVertex (down x) 2 =
      vertexEquiv (x + ((0, 1) : Int × Int))
  tile_eq : ∀ x, P.tile (vertexEquiv x) = tileAt x

end ApollonianSuperharmonic

end
