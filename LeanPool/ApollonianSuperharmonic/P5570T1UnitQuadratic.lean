/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: P5570T1UnitQuadratic]

/-!
# P5570T1UnitQuadratic

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $z=a+bi\in\mathbb Z[i]$, define the integer quadratic
$$
 Q_z(r+ti)=(1+a)\frac{r(r-1)}2-a\frac{t(t-1)}2+brt.
$$
The divisions are integer divisions; both numerators are even, including
for negative integer arguments.
-/
def P5570T1UnitQuadratic (z : GaussianInt) : IntegerLatticeFunction :=
-- BODY
  fun x => (1 + z.re) * (x.re * (x.re - 1) / 2) -
    z.re * (x.im * (x.im - 1) / 2) + z.im * x.re * x.im

end ApollonianSuperharmonic

end
