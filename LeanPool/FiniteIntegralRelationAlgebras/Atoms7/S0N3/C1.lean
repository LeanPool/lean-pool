/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C1.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C1.S0

/-! Generated certificate (see `certgen`): symmetry class 1 of type (0, 3). -/

@[expose] public section

namespace RACert.S0N3.C1

open RACert RACert.Problem

theorem total : OrbitSeg 8 perms (P.leaf (19 + 1)) 0 256 256 1363629 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 0 3 [0, 1, 2, 3, 4, 6, 5] = 1363629 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S0N3.C1
