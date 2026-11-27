/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C6.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C6.S0

/-! Generated certificate (see `certgen`): symmetry class 6 of type (4, 1). -/

@[expose] public section

namespace RACert.S4N1.C6

open RACert RACert.Problem

theorem total : OrbitSeg 4 perms (P.leaf (20 + 2)) 0 16 16 761050 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 4 1 [0, 2, 1, 4, 3, 5, 6] = 761050 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S4N1.C6
