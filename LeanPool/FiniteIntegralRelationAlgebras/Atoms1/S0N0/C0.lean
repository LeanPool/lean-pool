/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Eval

/-! Generated certificate (see `certgen`): symmetry class 0 of type (0, 0). -/

@[expose] public section

namespace RACert.S0N0.C0

open RACert RACert.Problem

/-- The counting problem of this class. -/
def P : Problem where
  s := 0
  n := 0
  perm := [0]
  pinv := [0]
  V := 0
  cls := [[[1]]]
  reps := []
  path := [[[0]]]
  quads := []
  wit := [[[[0]]]]

theorem check : P.check = true := by decide +kernel

theorem rows : P.checkRows = true := by decide +kernel

theorem total : P.sumLeaves 0 0 1 = 1 := by decide +kernel

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 0 0 [0] = 1 :=
  fixCountL_of_total (P := P) check rows (by decide +kernel) (by decide +kernel) total

end RACert.S0N0.C0
