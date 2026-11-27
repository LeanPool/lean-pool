/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C0.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C0.S0

/-! Generated certificate (see `certgen`): symmetry class 0 of type (3, 1). -/

@[expose] public section

namespace RACert.S3N1.C0

open RACert RACert.Problem

theorem total : OrbitSeg 7 perms (P.leaf (20 + 3)) 0 128 128 11044515 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 3 1 [0, 1, 2, 3, 4, 5] = 11044515 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S3N1.C0
