/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TriangularBoundaryStrip
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent

-- [TABLET NODE: TriangularStripSegment]

/-!
# TriangularStripSegment

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The triangular strip segment from $x$ to $y$ is a finite list beginning at
$x$ and ending at $y$, with no repeated vertex, all of whose vertices lie
in `TriangularBoundaryStrip` $\mathcal B(x,y)$ and whose successive
vertices are `TriangularLatticeAdjacent`.  When $x=y$, it is by
definition the singleton list $[x]$; the empty height window in that case
is not imposed on the singleton.
-/
def TriangularStripSegment (x y : Int × Int)
    (path : List (Int × Int)) : Prop :=
-- BODY
  if x = y then
    path = [x]
  else
    path.head? = some x ∧
    path.getLast? = some y ∧
    path.Nodup ∧
    (∀ z ∈ path, TriangularBoundaryStrip x y z) ∧
    path.IsChain TriangularLatticeAdjacent

end ApollonianSuperharmonic

end
