/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 0 of type (3, 0). -/

@[expose] public section

namespace RACert.S3N0.C0

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 3
  n := 0
  perm := [0, 1, 2, 3]
  pinv := [0, 1, 2, 3]
  V := 10
  cls := [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
    [[0, 1, 0, 0], [1, 2, 3, 4], [0, 3, 5, 6], [0, 4, 6, 7]],
    [[0, 0, 1, 0], [0, 3, 5, 6], [1, 5, 8, 9], [0, 6, 9, 10]],
    [[0, 0, 0, 1], [0, 4, 6, 7], [0, 6, 9, 10], [1, 7, 10, 11]]]
  reps := [21, 22, 23, 26, 27, 31, 42, 43, 47, 63]
  path := [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 1, 1, 0]],
    [[0, 0, 0, 0], [0, 2, 17, 81], [0, 2, 0, 0], [0, 10, 1, 0]],
    [[0, 0, 0, 0], [0, 2, 17, 17], [0, 2, 2, 17], [0, 2, 2, 0]]]
  quads := [85, 86, 87, 90, 91, 95, 102, 103, 106, 107, 110, 111, 119, 123, 127, 170, 171, 175, 187,
    191, 255]
  wit := [[[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 6, 0, 0], [0, 6, 6, 0]],
    [[0, 0, 0, 0], [0, 5, 0, 0], [0, 21, 0, 0], [0, 21, 0, 0]],
    [[0, 0, 0, 0], [0, 5, 5, 0], [0, 22, 22, 0], [0, 21, 22, 0]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 1, 1, 2], [0, 1, 1, 1], [0, 6, 6, 6]],
    [[0, 0, 0, 0], [0, 5, 2, 2], [0, 9, 0, 0], [0, 21, 6, 0]],
    [[0, 0, 0, 0], [0, 5, 5, 2], [0, 9, 5, 0], [0, 21, 21, 0]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 1, 1, 1], [0, 1, 1, 1], [0, 1, 1, 1]],
    [[0, 0, 0, 0], [0, 9, 2, 2], [0, 9, 1, 1], [0, 9, 1, 1]],
    [[0, 0, 0, 0], [0, 5, 5, 2], [0, 9, 5, 2], [0, 9, 9, 0]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem c0 : P.sumLeaves 10 0 1 = 294 := by decide +kernel

theorem total : P.sumLeaves 10 0 1 = 294 :=
  sumLeaves_of_chunks (cs := [(1, 294)])
    (.cons c0 (.nil))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 3 0 [0, 1, 2, 3] = 294 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S3N0.C0
