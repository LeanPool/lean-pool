/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicSubtileIndex

-- [TABLET NODE: P4715T1BoundaryCycle]

/-!
# P4715T1BoundaryCycle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The cyclic list of corner indices is
$(A_{0,0},B_{0,0},A_{-1,-1},B_{-1,0},A_{-1,0},B_{0,1})$,
with indices as in `PeriodicSubtileIndex`.
-/
def P4715T1BoundaryCycle : Fin 6 → PeriodicSubtileIndex :=
-- BODY
  ![⟨.A, 0, 0⟩, ⟨.B, 0, 0⟩, ⟨.A, -1, -1⟩,
    ⟨.B, -1, 0⟩, ⟨.A, -1, 0⟩, ⟨.B, 0, 1⟩]

end ApollonianSuperharmonic

end
