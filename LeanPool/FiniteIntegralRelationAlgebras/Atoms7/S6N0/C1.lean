/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C1.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C1.S0

/-! Generated certificate (see `certgen`): symmetry class 1 of type (6, 0). -/

@[expose] public section

namespace RACert.S6N0.C1

open RACert RACert.Problem

theorem total : OrbitSeg 15 perms (P.leaf (20 + 5)) 0 32768 32768 10655990948 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 6 0 [0, 1, 2, 3, 4, 6, 5] = 10655990948 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S6N0.C1
