/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: P4207T1DiamondFormula]

/-!
# P4207T1DiamondFormula

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The integer function $F=\operatorname{P4207\_T1\_DiamondFormula}$ on the Gaussian
lattice is
$$
 F(a,b)=\frac{|a|(|a|-1)}2-\left\lfloor\frac{(a-b)^2}{4}\right\rfloor.
$$
The first quotient is integral. This is the displayed formula on the
canonical domain in the paper's diamond odometer lemma, considered as a
parameter-independent function on the whole lattice, not as a periodic
extension.
-/
def P4207T1DiamondFormula : IntegerLatticeFunction :=
-- BODY
  fun x => (Int.natAbs x.re : Int) * ((Int.natAbs x.re : Int) - 1) / 2 -
    (x.re - x.im) ^ 2 / 4

end ApollonianSuperharmonic

end
