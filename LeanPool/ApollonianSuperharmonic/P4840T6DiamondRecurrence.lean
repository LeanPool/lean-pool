/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple

-- [TABLET NODE: P4840T6DiamondRecurrence]

/-!
# P4840T6DiamondRecurrence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4840T6DiamondRecurrence (K : DiamondParameter) :
    let R := fun x : Fin 4 → CircleCoordinates => ![x 0, x 2, x 3, x 1]
    let S := fun x : Fin 4 → CircleCoordinates =>
      ![(2 * (x 0).1 + 2 * (x 2).1 + 2 * (x 3).1 - (x 1).1,
          2 * (x 0).2 + 2 * (x 2).2 + 2 * (x 3).2 - (x 1).2),
        x 0, x 2, x 3]
    R (S (R (R (DiamondRecursiveQuadruple K)))) =
      DiamondRecursiveQuadruple ⟨K.1 + 1, by omega⟩ := by
  have hk : 1 ≤ K.1 := K.2
  funext j
  fin_cases j <;> apply Prod.ext
  all_goals try apply Zsqrtd.ext
  all_goals simp [DiamondRecursiveQuadruple, Nat.cast_sub hk]
  all_goals ring

end ApollonianSuperharmonic

end
