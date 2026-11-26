/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 0 of type (1, 0). -/

@[expose] public section

namespace RACert.S1N0.C0

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 1
  n := 0
  perm := [0, 1]
  pinv := [0, 1]
  V := 1
  cls := [[[1, 0], [0, 1]],
    [[0, 1], [1, 2]]]
  reps := [7]
  path := [[[0, 0], [0, 0]],
    [[0, 0], [0, 0]]]
  quads := [15]
  wit := [[[[0, 0], [0, 0]],
    [[0, 0], [0, 0]]],
    [[[0, 0], [0, 0]],
    [[0, 0], [0, 0]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem c0 : P.sumLeaves 1 0 1 = 2 := by decide +kernel

theorem total : P.sumLeaves 1 0 1 = 2 :=
  sumLeaves_of_chunks (cs := [(1, 2)])
    (.cons c0 (.nil))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 1 0 [0, 1] = 2 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S1N0.C0
