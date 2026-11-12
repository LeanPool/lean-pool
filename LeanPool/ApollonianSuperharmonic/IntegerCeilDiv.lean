/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: IntegerCeilDiv]

/-!
# IntegerCeilDiv

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For integers $a$ and nonzero $b$, write
$$
  \operatorname{cdiv}(a,b)=-\bigl((-a)\mathbin{\mathrm{div}}b\bigr).
$$
When $b>0$, this is the integer ceiling $\lceil a/b\rceil$.
-/
def IntegerCeilDiv (a b : Int) (_hb : b ≠ 0) : Int :=
-- BODY
  -((-a) / b)

end ApollonianSuperharmonic

end
