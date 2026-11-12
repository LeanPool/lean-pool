/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.RecursiveVectorsExistUnique

-- [TABLET NODE: BandVectors]

/-!
# BandVectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Define $(v,a)$ to be the unique recursive vector system supplied by
`RecursiveVectorsExistUnique`.  For every ordered
pair of raw curvature coordinates, $v(C,C')$ and $a(C,C')$ are its two
Gaussian-integer components.  On ordered tangent pairs they are called the
lattice vector and slope vector; on non-tangent pairs they are zero.  The
unique orientation of `PrimitiveVectorOrientation` and uniqueness
of the recursive system make these functions depend on coordinate pairs,
not on a chosen derivation of a semi-proper quadruple.
-/
noncomputable def BandVectors :
    (CircleCoordinates → CircleCoordinates → GaussianInt) ×
      (CircleCoordinates → CircleCoordinates → GaussianInt) :=
-- BODY
  Classical.choose RecursiveVectorsExistUnique

end ApollonianSuperharmonic

end
