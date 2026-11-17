/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: P4828T1Step]

/-!
# P4828T1Step

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The coordinate successor of $q=(C_0,C_1,C_2,C_3)$ is
$S(q)=(2(C_0+C_2+C_3)-C_1,C_0,C_2,C_3)$, with the arithmetic
performed separately in the integer curvature and Gaussian numerator.
It is denoted by `P4828T1Step`.
-/
def P4828T1Step (q : Fin 4 → CircleCoordinates) :
    Fin 4 → CircleCoordinates :=
-- BODY
  ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
      2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
    q 0, q 2, q 3]

end ApollonianSuperharmonic

end
