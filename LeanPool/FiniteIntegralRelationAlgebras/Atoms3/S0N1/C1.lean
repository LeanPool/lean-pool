/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 1 of type (0, 1). -/

@[expose] public section

namespace RACert.S0N1.C1

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 0
  n := 1
  perm := [0, 2, 1]
  pinv := [0, 2, 1]
  V := 2
  cls := [[[1, 0, 0], [0, 1, 0], [0, 0, 1]],
    [[0, 1, 0], [0, 2, 3], [1, 2, 2]],
    [[0, 0, 1], [1, 2, 2], [0, 3, 2]]]
  reps := [13, 14]
  path := [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 2, 10]],
    [[0, 0, 0], [0, 1, 17], [0, 1, 3]]]
  quads := [40, 41, 43, 49]
  wit := [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 0, 0]]],
    [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 0, 21]],
    [[0, 0, 0], [0, 0, 5], [0, 7, 2]]],
    [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 1, 1], [0, 22, 1]],
    [[0, 0, 0], [0, 6, 3], [0, 2, 2]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem total : P.sumLeaves 2 0 1 = 3 := by decide +kernel

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 0 1 [0, 2, 1] = 3 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S0N1.C1
