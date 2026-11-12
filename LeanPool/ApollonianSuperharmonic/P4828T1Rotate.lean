/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: P4828T1Rotate]

/-!
# P4828T1Rotate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a coordinate quadruple $q$ and $r\in\mathbb Z/3\mathbb Z$, let
$R_rq$ fix the child and send parent slot $j$ to the old parent slot $j+r$.
Here parent slots are numbered $0,1,2$, independently of the child slot.
This operation is denoted by `P4828T1Rotate`.
-/
def P4828T1Rotate (q : Fin 4 → CircleCoordinates) (r : Fin 3) :
    Fin 4 → CircleCoordinates :=
-- BODY
  Fin.cases (q 0) (fun j => q ((j + r).succ))

end ApollonianSuperharmonic

end
