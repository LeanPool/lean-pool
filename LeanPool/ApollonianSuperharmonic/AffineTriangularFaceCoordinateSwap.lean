/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineTriangularFace

-- [TABLET NODE: AffineTriangularFaceCoordinateSwap]

/-!
# AffineTriangularFaceCoordinateSwap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Coordinate swap acts on a tagged affine triangular face by swapping its base
coordinates and exchanging its tag:
$$
 U_z^\sigma=D_{\sigma(z)},\qquad
 D_z^\sigma=U_{\sigma(z)},
$$
where $\sigma:\mathbb Z^2\to\mathbb Z^2$ is the coordinate swap
$\sigma(m,n)=(n,m)$.
This names the canonical face corresponding to a source face when a
$(b,a)$-indexed source family is aligned with an $(a,b)$-indexed canonical
chart.  The tag exchange records the reflection of the two triangular
chambers.  It is intended to identify their unordered vertex incidences;
it does not assert equality of their ordered vertex triples.
-/
def AffineTriangularFaceCoordinateSwap
    (f : AffineTriangularFace) : AffineTriangularFace :=
-- BODY
  match f with
  | .up z => .down ((Prod.swap : Int × Int → Int × Int) z)
  | .down z => .up ((Prod.swap : Int × Int → Int × Int) z)

end ApollonianSuperharmonic

end
