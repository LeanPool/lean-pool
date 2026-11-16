/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Finset.Card

public import LeanPool.ApollonianSuperharmonic.AffineTriangularFace

-- [TABLET NODE: AffineTriangularFaceVertices]

/-!
# AffineTriangularFaceVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The vertex set of the tagged affine triangular face based at
$z\in\mathbb Z^2$ is
$$
 V(U_z)=\{z,z+(1,0),z-(0,1)\},\qquad
 V(D_z)=\{z,z-(1,0),z+(0,1)\}.
$$
Thus each tagged face records exactly one elementary triangle in the
six-neighbor affine triangular lattice.
-/
def AffineTriangularFaceVertices
    (f : AffineTriangularFace) : Finset (Int × Int) :=
-- BODY
  match f with
  | .up z => {z, z + ((1, 0) : Int × Int), z - ((0, 1) : Int × Int)}
  | .down z => {z, z - ((1, 0) : Int × Int), z + ((0, 1) : Int × Int)}

end ApollonianSuperharmonic

end
