/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S5N0.C0.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S5N0.C0.S0

/-! Generated certificate (see `certgen`): symmetry class 0 of type (5, 0). -/

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

theorem total : OrbitSeg 10 perms (P.leaf (20 + 5)) 0 1024 1024 454897503 :=
  OrbitSeg.cast (S0.total)
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 5 0 [0, 1, 2, 3, 4, 5] = 454897503 :=
  fixCountL_of_orbitGenerators (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S5N0.C0
