/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 2 of type (3, 0). -/

@[expose] public section

namespace RACert.S3N0.C2

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 3
  n := 0
  perm := [0, 2, 3, 1]
  pinv := [0, 3, 1, 2]
  V := 4
  cls := [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
    [[0, 1, 0, 0], [1, 2, 3, 4], [0, 3, 4, 5], [0, 4, 5, 3]],
    [[0, 0, 1, 0], [0, 3, 4, 5], [1, 4, 2, 3], [0, 5, 3, 4]],
    [[0, 0, 0, 1], [0, 4, 5, 3], [0, 5, 3, 4], [1, 3, 4, 2]]]
  reps := [21, 22, 23, 27]
  path := [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 20, 0], [0, 1, 1, 19]],
    [[0, 0, 0, 0], [0, 2, 12, 12], [0, 4, 4, 4], [0, 4, 12, 19]],
    [[0, 0, 0, 0], [0, 2, 3, 11], [0, 2, 20, 11], [0, 3, 3, 3]]]
  quads := [85, 86, 87, 90, 91, 102, 103]
  wit := [[[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 0], [0, 6, 0, 0], [0, 6, 6, 23]],
    [[0, 0, 0, 0], [0, 5, 0, 0], [0, 21, 31, 31], [0, 21, 31, 23]],
    [[0, 0, 0, 0], [0, 5, 5, 7], [0, 22, 159, 27], [0, 7, 11, 7]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 1, 1, 2], [0, 1, 95, 95], [0, 6, 367, 39]],
    [[0, 0, 0, 0], [0, 5, 111, 111], [0, 15, 15, 15], [0, 15, 111, 15]],
    [[0, 0, 0, 0], [0, 5, 351, 7], [0, 15, 95, 15], [0, 7, 351, 7]]],
    [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    [[0, 0, 0, 0], [0, 1, 1, 87], [0, 1, 95, 87], [0, 3, 3, 23]],
    [[0, 0, 0, 0], [0, 9, 111, 91], [0, 47, 31, 31], [0, 23, 31, 23]],
    [[0, 0, 0, 0], [0, 3, 3, 27], [0, 27, 95, 27], [0, 3, 3, 3]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem c0 : P.sumLeaves 4 0 1 = 9 := by decide +kernel

theorem total : P.sumLeaves 4 0 1 = 9 :=
  sumLeaves_of_chunks (cs := [(1, 9)])
    (.cons c0 (.nil))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 3 0 [0, 2, 3, 1] = 9 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S3N0.C2
