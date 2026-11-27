/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 1 of type (1, 1). -/

@[expose] public section

namespace RACert.S1N1.C1

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 1
  n := 1
  perm := [0, 1, 3, 2]
  pinv := [0, 1, 3, 2]
  V := 6
  cls := [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
    [[0, 1, 0, 0], [1, 2, 3, 3], [0, 3, 4, 5], [0, 3, 5, 4]],
    [[0, 0, 1, 0], [0, 3, 4, 5], [0, 5, 6, 7], [1, 4, 6, 6]],
    [[0, 0, 0, 1], [0, 3, 5, 4], [1, 4, 6, 6], [0, 5, 7, 6]]]
  reps := [21, 22, 26, 27, 42, 43]
  path := [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 3], [0, 1, 0, 0], [0, 10, 1, 3]],
    [[0, 0, 0, 0], [0, 2, 139, 17], [0, 10, 0, 0], [0, 2, 2, 10]],
    [[0, 0, 0, 0], [0, 17, 81, 17], [0, 19, 1, 17], [0, 2, 1, 3]]]
  quads := [85, 86, 90, 91, 102, 103, 106, 107, 111, 170, 171, 174, 186]
  wit := [[[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 2], [0, 6, 0, 0], [0, 21, 3, 3]],
    [[0, 0, 0, 0], [0, 22, 0, 0], [0, 21, 0, 0], [0, 21, 22, 0]],
    [[0, 0, 0, 0], [0, 5, 2, 2], [0, 87, 3, 91], [0, 22, 3, 3]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 7, 7, 1], [0, 1, 1, 1], [0, 7, 7, 27]],
    [[0, 0, 0, 0], [0, 5, 11, 5], [0, 21, 0, 0], [0, 21, 0, 21]],
    [[0, 0, 0, 0], [0, 5, 2, 5], [0, 21, 0, 5], [0, 9, 7, 2]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 1, 2, 1], [0, 1, 6, 1], [0, 6, 6, 6]],
    [[0, 0, 0, 0], [0, 23, 23, 5], [0, 39, 1, 1], [0, 9, 22, 1]],
    [[0, 0, 0, 0], [0, 9, 2, 2], [0, 87, 6, 3], [0, 9, 2, 2]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem total : P.sumLeaves 6 0 1 = 32 := by decide +kernel

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 1 1 [0, 1, 3, 2] = 32 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S1N1.C1
