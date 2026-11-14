/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: P4981T1EdgeRank]

/-!
# P4981T1EdgeRank

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The rank of an ordered coordinate edge $(C,D)$ is
$\max\{\max(c_C,0),\max(c_D,0)\}$, regarded as a natural number.
In particular its rank does not depend on its direction.
-/
def P4981T1EdgeRank (e : CircleCoordinates × CircleCoordinates) : ℕ :=
-- BODY
  max e.1.1.toNat e.2.1.toNat

end ApollonianSuperharmonic

end
