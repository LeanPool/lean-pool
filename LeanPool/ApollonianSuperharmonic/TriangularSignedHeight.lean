/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: TriangularSignedHeight]

/-!
# TriangularSignedHeight

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $x,y,z\in\mathbb Z^2$, the integral signed height of $z$ above the
oriented line from $x$ to $y$ is
$$
 \Phi_{x,y}(z)=
 (y_1-x_1)(z_2-x_2)-(y_2-x_2)(z_1-x_1).
$$
Thus the chosen closed side is $\Phi_{x,y}\geq0$, and no division by the
length or primitivity of $y-x$ is involved.
-/
def TriangularSignedHeight (x y z : Int × Int) : Int :=
-- BODY
  (y.1 - x.1) * (z.2 - x.2) - (y.2 - x.2) * (z.1 - x.1)

end ApollonianSuperharmonic

end
