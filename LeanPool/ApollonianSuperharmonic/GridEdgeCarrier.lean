/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint

-- [TABLET NODE: GridEdgeCarrier]

/-!
# GridEdgeCarrier

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a finite set $e$ of Gaussian lattice points, its
*grid-edge carrier* $\operatorname{GridEdgeCarrier}(e)$ is
$$
 \bigcup_{a\in e}\ \bigcup_{b\in e}
 [\operatorname{GaussianRealPoint}(a),\operatorname{GaussianRealPoint}(b)]_{\rm ord},
$$
where $[r,s]_{\rm ord}$ is the unordered coordinate interval between two
points of $\mathbb R^2$.  For the endpoints of a horizontal or vertical unit
grid edge, this is precisely the corresponding closed unit segment.
-/
def GridEdgeCarrier (e : Finset GaussianInt) : Set (Real × Real) :=
-- BODY
  ⋃ x ∈ e, ⋃ y ∈ e, Set.uIcc (GaussianRealPoint x) (GaussianRealPoint y)

end ApollonianSuperharmonic

end
