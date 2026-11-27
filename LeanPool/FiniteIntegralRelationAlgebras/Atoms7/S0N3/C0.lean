/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C0.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C0.S0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C0.S1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C0.S2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C0.S3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C0.S4

/-! Generated certificate (see `certgen`): symmetry class 0 of type (0, 3). -/

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

theorem total : OrbitSeg 20 perms (P.leaf (18 + 0)) 0 1048576 1048576 203664497 :=
  OrbitSeg.cast ((S0.total).append ((S1.total).append ((S2.total).append ((S3.total).append
    (S4.total)))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 0 3 [0, 1, 2, 3, 4, 5, 6] = 203664497 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S0N3.C0
