/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: FordRecursiveVertexDomains]

/-!
# FordRecursiveVertexDomains

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford--Farey parameter, the four closed recursive vertex domains are
$$
 E_1=[0,q_1]^2,\quad E_2=[q_2,q]^2,\quad
 E_3=[q_1,q]\times[0,q_2],\quad
 E_4=[0,q_2]\times[q_1,q].
$$
Their half-open cell interiors are precisely the four nonempty recursive
pieces identified in `FordTileRecursiveIdentification`.
-/
def FordRecursiveVertexDomains (P : FordFareyParameter) : Fin 4 -> Set GaussianInt :=
-- BODY
  ![{x | 0 <= x.re ∧ x.re <= (P.q₁ : Int) ∧
          0 <= x.im ∧ x.im <= (P.q₁ : Int)},
    {x | (P.q₂ : Int) <= x.re ∧ x.re <= (P.q : Int) ∧
          (P.q₂ : Int) <= x.im ∧ x.im <= (P.q : Int)},
    {x | (P.q₁ : Int) <= x.re ∧ x.re <= (P.q : Int) ∧
          0 <= x.im ∧ x.im <= (P.q₂ : Int)},
    {x | 0 <= x.re ∧ x.re <= (P.q₂ : Int) ∧
          (P.q₁ : Int) <= x.im ∧ x.im <= (P.q : Int)}]

end ApollonianSuperharmonic

end
