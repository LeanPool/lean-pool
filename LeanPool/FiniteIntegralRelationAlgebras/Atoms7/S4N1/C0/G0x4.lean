/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.S256
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.S257
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.S258
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.S259
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.S260
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.S261
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0.S262

/-! Generated certificate; see `certgen`. -/

@[expose] public section

namespace RACert.S4N1.C0

open RACert RACert.Problem

namespace G0x4

theorem total : OrbitSeg 26 perms (P.leaf (20 + 4)) 25156815 67108864 1562928 779037091171 :=
  OrbitSeg.cast ((S256.total).append ((S257.total).append ((S258.total).append ((S259.total).append
    ((S260.total).append ((S261.total).append (S262.total)))))))
    (by decide +kernel) (by decide +kernel)

end G0x4

end RACert.S4N1.C0
