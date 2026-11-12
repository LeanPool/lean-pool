/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates
public import LeanPool.ApollonianSuperharmonic.DiamondParameter

-- [TABLET NODE: DiamondRecursiveQuadruple]

/-!
# DiamondRecursiveQuadruple

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a positive integer $k$, the ordered diamond recursive quadruple is
$$
 \bigl(C_k,(1,1+2i),(1,1),C_{k-1}\bigr),
$$
where
$$
 C_k=(2k(k+1),\,2k^2-1+2k(k+1)i).
$$
At $k=1$, the last coordinate is $(0,-1)$, so it is an oriented line in
the general-circle recursion rather than a band circle.
-/
def DiamondRecursiveQuadruple (K : DiamondParameter) :
    Fin 4 → CircleCoordinates :=
-- BODY
  let k := K.1
  ![((2 * k * (k + 1) : Nat),
      ⟨2 * (k : Int) ^ 2 - 1, 2 * (k : Int) * (k + 1)⟩),
    (1, ⟨1, 2⟩),
    (1, 1),
    ((2 * (k - 1) * k : Nat),
      ⟨2 * ((k - 1 : Nat) : Int) ^ 2 - 1,
        2 * ((k - 1 : Nat) : Int) * k⟩)]

end ApollonianSuperharmonic

end
