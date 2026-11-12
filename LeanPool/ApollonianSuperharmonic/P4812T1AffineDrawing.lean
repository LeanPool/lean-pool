/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent

-- [TABLET NODE: P4812T1AffineDrawing]

/-!
# P4812T1AffineDrawing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Gaussian-integer subgroup $L$ and additive equivalence
$\kappa:\mathbb Z^2\simeq L$, a periodic triangular drawing consists of
a `PlaneTriangulation` $P$ on $L$ and a bijection from
$L\sqcup L$ to its faces, written $U_x,D_x$.  Adjacency in
$\kappa$-coordinates is `TriangularLatticeAdjacent`.  Its
ordered face vertices are
$$
 U_x=(x,x+\kappa(1,0),x-\kappa(0,1)),\qquad
 D_x=(x,x-\kappa(1,0),x+\kappa(0,1)).
$$
The position of $x$ is $[x]$.  For every $u,x,y\in L$, the arc on
$(u+x,u+y)$ is the translate by $[u]$ of the arc on $(x,y)$.
The regions of $U_{u+x}$ and $D_{u+x}$ are the translates by $[u]$
of the regions of $U_x$ and $D_x$, respectively.  These requirements
concern all pairs, not only adjacent pairs.  This is purely geometric
data; no tiles, contact points, or contained walks are part of it.
-/
structure P4812T1AffineDrawing (L : AddSubgroup GaussianInt)
    (k : (Int × Int) ≃+ L) where
-- BODY
  /-- The cellular plane triangulation on the period lattice. -/
  plane : PlaneTriangulation L
  /-- Identify the two labelled face families with the faces of the drawing. -/
  faces : Sum L L ≃ plane.Face
  adjacent_iff : ∀ x y, plane.adjacent x y ↔
    TriangularLatticeAdjacent (k.symm x) (k.symm y)
  up_vertices : ∀ x,
    plane.faceVertex (faces (.inl x)) 0 = x ∧
    plane.faceVertex (faces (.inl x)) 1 = x + k (1, 0) ∧
    plane.faceVertex (faces (.inl x)) 2 = x - k (0, 1)
  down_vertices : ∀ x,
    plane.faceVertex (faces (.inr x)) 0 = x ∧
    plane.faceVertex (faces (.inr x)) 1 = x - k (1, 0) ∧
    plane.faceVertex (faces (.inr x)) 2 = x + k (0, 1)
  position_eq : ∀ x, plane.position x = GaussianRealPoint (x : GaussianInt)
  edgeArc_periodic : ∀ (u x y : L),
    plane.edgeArc (u + x) (u + y) =
      (fun p => p + GaussianRealPoint (u : GaussianInt)) '' plane.edgeArc x y
  faceRegion_periodic : ∀ (u : L) (f : Sum L L),
    plane.faceRegion (faces (Sum.map (u + ·) (u + ·) f)) =
      (fun p => p + GaussianRealPoint (u : GaussianInt)) ''
        plane.faceRegion (faces f)

end ApollonianSuperharmonic

end
