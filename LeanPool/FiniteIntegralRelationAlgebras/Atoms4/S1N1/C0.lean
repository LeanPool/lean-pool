/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 0 of type (1, 1). -/

@[expose] public section

namespace RACert.S1N1.C0

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 1
  n := 1
  perm := [0, 1, 2, 3]
  pinv := [0, 1, 2, 3]
  V := 7
  cls := [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
    [[0, 1, 0, 0], [1, 2, 3, 3], [0, 3, 4, 5], [0, 3, 5, 6]],
    [[0, 0, 1, 0], [0, 3, 6, 5], [0, 5, 7, 8], [1, 4, 7, 7]],
    [[0, 0, 0, 1], [0, 3, 5, 4], [1, 6, 7, 7], [0, 5, 8, 7]]]
  reps := [21, 22, 26, 27, 31, 42, 43]
  path := [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 81], [0, 1, 0, 0], [0, 10, 1, 0]],
    [[0, 0, 0, 0], [0, 2, 17, 17], [0, 10, 0, 0], [0, 2, 2, 10]],
    [[0, 0, 0, 0], [0, 17, 81, 17], [0, 2, 1, 17], [0, 2, 1, 81]]]
  quads := [85, 86, 90, 91, 95, 102, 103, 106, 107, 111, 123, 170, 171, 174, 186]
  wit := [[[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 2], [0, 6, 0, 0], [0, 21, 6, 0]],
    [[0, 0, 0, 0], [0, 22, 0, 0], [0, 21, 0, 0], [0, 21, 22, 0]],
    [[0, 0, 0, 0], [0, 5, 2, 2], [0, 21, 22, 0], [0, 22, 22, 22]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 9, 1, 1], [0, 1, 1, 1], [0, 9, 6, 1]],
    [[0, 0, 0, 0], [0, 5, 5, 5], [0, 21, 0, 0], [0, 21, 0, 21]],
    [[0, 0, 0, 0], [0, 5, 2, 5], [0, 21, 0, 5], [0, 9, 9, 2]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 1, 2, 1], [0, 1, 6, 1], [0, 6, 6, 6]],
    [[0, 0, 0, 0], [0, 5, 2, 5], [0, 21, 1, 1], [0, 9, 22, 1]],
    [[0, 0, 0, 0], [0, 9, 2, 2], [0, 9, 6, 5], [0, 9, 2, 2]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem total : P.sumLeaves 7 0 1 = 42 := by decide +kernel

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 1 1 [0, 1, 2, 3] = 42 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S1N1.C0
