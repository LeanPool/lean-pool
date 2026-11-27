/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C2.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C2.S0

/-! Generated certificate (see `certgen`): symmetry class 2 of type (0, 3). -/

@[expose] public section

namespace RACert.S0N3.C2

open RACert RACert.Problem

theorem total : OrbitSeg 6 perms (P.leaf (19 + 1)) 0 64 64 1083289 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 0 3 [0, 1, 2, 4, 3, 6, 5] = 1083289 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S0N3.C2
