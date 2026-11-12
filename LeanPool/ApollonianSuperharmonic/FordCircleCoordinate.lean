/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: FordCircleCoordinate]

/-!
# FordCircleCoordinate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $p\in\mathbb Z$ and $q\in\mathbb N$, the raw Ford curvature coordinate is
$$
 C_{p,q}:=(q^2,\,1+2pq\,i).
$$
Only positive $q$ are used as circles; the formal pair $(1,0)$ in the
Farey-parent convention is interpreted separately as a line.
-/
def FordCircleCoordinate (p : Int) (q : Nat) : CircleCoordinates :=
-- BODY
  ((q * q : Nat), ⟨1, 2 * p * (q : Int)⟩)

end ApollonianSuperharmonic

end
