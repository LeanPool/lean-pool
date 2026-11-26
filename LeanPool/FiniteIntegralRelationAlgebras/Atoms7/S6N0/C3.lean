/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C3.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C3.S0

/-! Generated certificate (see `certgen`): symmetry class 3 of type (6, 0). -/

@[expose] public section

namespace RACert.S6N0.C3

open RACert RACert.Problem

theorem total : OrbitSeg 8 perms (P.leaf (20 + 4)) 0 256 256 93632936 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 6 0 [0, 1, 2, 4, 3, 6, 5] = 93632936 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S6N0.C3
