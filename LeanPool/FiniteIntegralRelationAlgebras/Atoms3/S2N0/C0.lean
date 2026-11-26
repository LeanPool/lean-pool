/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 0 of type (2, 0). -/

@[expose] public section

namespace RACert.S2N0.C0

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 2
  n := 0
  perm := [0, 1, 2]
  pinv := [0, 1, 2]
  V := 4
  cls := [[[1, 0, 0], [0, 1, 0], [0, 0, 1]],
    [[0, 1, 0], [1, 2, 3], [0, 3, 4]],
    [[0, 0, 1], [0, 3, 4], [1, 4, 5]]]
  reps := [13, 14, 17, 26]
  path := [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 1, 0]],
    [[0, 0, 0], [0, 2, 17], [0, 2, 0]]]
  quads := [40, 41, 44, 50, 53, 80]
  wit := [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 0, 0]]],
    [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 0, 0], [0, 6, 0]],
    [[0, 0, 0], [0, 5, 0], [0, 21, 0]]],
    [[[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    [[0, 0, 0], [0, 1, 1], [0, 1, 1]],
    [[0, 0, 0], [0, 5, 2], [0, 9, 0]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem c0 : P.sumLeaves 4 0 1 = 12 := by decide +kernel

theorem total : P.sumLeaves 4 0 1 = 12 :=
  sumLeaves_of_chunks (cs := [(1, 12)])
    (.cons c0 (.nil))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 2 0 [0, 1, 2] = 12 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S2N0.C0
