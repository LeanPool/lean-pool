/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: P4828T1Root]

/-!
# P4828T1Root

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Put $U_z=(1,1+2z)$. The first proper left and right root presentations are
$$
 F(z,-)=((4,1+8z+4i),U_z,(0,-1),U_{z+i}),\qquad
 F(z,+)=((4,7+8z+4i),U_z,U_{z+i},(0,1)).
$$
The Boolean values false and true denote $-$ and $+$, respectively.
These presentations are denoted by `P4828T1Root`.
-/
def P4828T1Root (z : GaussianInt) (side : Bool) :
    Fin 4 → CircleCoordinates :=
-- BODY
  if side then
    ![(4, 7 + 8 * z + 4 * ⟨0, 1⟩), (1, 1 + 2 * z),
      (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (0, 1)]
  else
    ![(4, 1 + 8 * z + 4 * ⟨0, 1⟩), (1, 1 + 2 * z),
      (0, -1), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)]

end ApollonianSuperharmonic

end
