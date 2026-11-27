/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 1 of type (2, 0). -/

@[expose] public section

namespace RACert.S2N0.C1

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 2
  n := 0
  perm := [0, 2, 1]
  pinv := [0, 2, 1]
  V := 2
  cls := [[[1, 0, 0], [0, 1, 0], [0, 0, 1]],
    [[0, 1, 0], [1, 2, 3], [0, 3, 3]],
    [[0, 0, 1], [0, 3, 3], [1, 3, 2]]]
  reps := [13, 14]
  path := [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 1, 19]],
    [[0, 0, 0], [0, 2, 11], [0, 3, 3]]]
  quads := [40, 41, 44, 50]
  wit := [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 0, 0]]],
    [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 6, 0]],
    [[0, 0, 0], [0, 5, 0], [0, 7, 7]]],
    [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 1, 1], [0, 1, 23]],
    [[0, 0, 0], [0, 3, 27], [0, 3, 3]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem total : P.sumLeaves 2 0 1 = 2 := by decide +kernel

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 2 0 [0, 2, 1] = 2 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S2N0.C1
