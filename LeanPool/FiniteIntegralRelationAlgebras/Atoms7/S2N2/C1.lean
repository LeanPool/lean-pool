/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C1.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C1.S0

/-! Generated certificate (see `certgen`): symmetry class 1 of type (2, 2). -/

@[expose] public section

namespace RACert.S2N2.C1

open RACert RACert.Problem

theorem total : OrbitSeg 12 perms (P.leaf (20 + 2)) 0 4096 4096 129381732 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 2 2 [0, 1, 2, 3, 4, 6, 5] = 129381732 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S2N2.C1
