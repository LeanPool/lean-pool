/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1Position
public import LeanPool.ApollonianSuperharmonic.P4715T1BoundaryCycle
public import Mathlib.Analysis.Convex.Hull

-- [TABLET NODE: P4715T1Hexagon]

/-!
# P4715T1Hexagon

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $H$ be the real convex hull of the positions
of the six indices in `P4715T1BoundaryCycle`, using
`P4715T1Position`.
-/
def P4715T1Hexagon : Set (Real × Real) :=
-- BODY
  convexHull Real (Set.range (P4715T1Position ∘ P4715T1BoundaryCycle))

end ApollonianSuperharmonic

end
