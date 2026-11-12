/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple

-- [TABLET NODE: ProperBandQuadruple]

/-!
# ProperBandQuadruple

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A semi-proper coordinate quadruple
$(C_0,C_1,C_2,C_3)$ is proper when the curvature of its child is strictly
larger than the curvature of each parent:
$$
 c_j<c_0\qquad(j=1,2,3).
$$
The clockwise ordering is already part of its presentation in the directed
semi-proper forest.  Thus the displayed strict inequalities distinguish the
proper nodes from the curvature-one root overlaps.
-/
def ProperBandQuadruple (q : Fin 4 → CircleCoordinates) : Prop :=
-- BODY
  SemiProperQuadruple q ∧
    ∀ j : Fin 3, (q j.succ).1 < (q 0).1

end ApollonianSuperharmonic

end
