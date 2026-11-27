/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x4
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x5
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x6
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x7
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x8
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x9
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x10
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x11
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C0.G0x12

/-! Generated certificate (see `certgen`): symmetry class 0 of type (6, 0). -/

@[expose] public section

namespace RACert.S6N0.C0

open RACert RACert.Problem

theorem total : OrbitSeg 30 perms (P.leaf (20 + 6)) 0 1073741824 1073741824 210329506874380 :=
  OrbitSeg.cast ((G0x0.total).append ((G0x1.total).append ((G0x2.total).append ((G0x3.total).append
    ((G0x4.total).append ((G0x5.total).append ((G0x6.total).append ((G0x7.total).append
    ((G0x8.total).append ((G0x9.total).append ((G0x10.total).append ((G0x11.total).append
    (G0x12.total)))))))))))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 6 0 [0, 1, 2, 3, 4, 5, 6] = 210329506874380 :=
  fixCountL_of_orbitGenerators (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S6N0.C0
