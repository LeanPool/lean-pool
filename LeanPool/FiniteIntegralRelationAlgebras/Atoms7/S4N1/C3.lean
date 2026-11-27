/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C3.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C3.S0

/-! Generated certificate (see `certgen`): symmetry class 3 of type (4, 1). -/

@[expose] public section

namespace RACert.S4N1.C3

open RACert RACert.Problem

theorem total : OrbitSeg 9 perms (P.leaf (20 + 3)) 0 512 512 91277262 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 4 1 [0, 1, 2, 4, 3, 6, 5] = 91277262 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S4N1.C3
