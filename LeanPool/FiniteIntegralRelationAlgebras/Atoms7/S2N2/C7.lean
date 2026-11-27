/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C7.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C7.S0

/-! Generated certificate (see `certgen`): symmetry class 7 of type (2, 2). -/

@[expose] public section

namespace RACert.S2N2.C7

open RACert RACert.Problem

theorem total : OrbitSeg 7 perms (P.leaf (20 + 1)) 0 128 128 3604496 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 2 2 [0, 2, 1, 4, 3, 6, 5] = 3604496 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S2N2.C7
