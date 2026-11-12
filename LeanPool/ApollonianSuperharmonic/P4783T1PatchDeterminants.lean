/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4783T1PatchCoordinates

-- [TABLET NODE: P4783T1PatchDeterminants]

/-!
# P4783T1PatchDeterminants

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4783T1PatchDeterminants (j : Fin 12) :
    let p := P4715T1Position ∘ SixSubtileFaceVertices (P4715T1PatchFaces j)
    (p 1).1 * (p 2).2 - (p 1).1 * (p 0).2 -
      (p 0).1 * (p 2).2 - (p 1).2 * (p 2).1 +
      (p 1).2 * (p 0).1 + (p 0).2 * (p 2).1 ≠ 0 := by
-- BODY
  dsimp only
  rw [P4783T1PatchCoordinates]
  fin_cases j <;> norm_num [Matrix.cons_val_two]

end ApollonianSuperharmonic

end
