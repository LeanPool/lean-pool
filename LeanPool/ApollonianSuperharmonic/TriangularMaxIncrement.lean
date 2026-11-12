/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Ring.Int


-- [TABLET NODE: TriangularMaxIncrement]

/-!
# TriangularMaxIncrement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an oriented pair $x,y\in\mathbb Z^2$, put
$$
 M_{x,y}=\max\bigl\{|y_1-x_1|,|y_2-x_2|,
 |(y_1-x_1)-(y_2-x_2)|\bigr\}.
$$
Equivalently, $M_{x,y}$ is the largest signed-height increase along one
of the six triangular-lattice steps.
-/
def TriangularMaxIncrement (x y : Int × Int) : Int :=
-- BODY
  max |y.1 - x.1|
    (max |y.2 - x.2| |(y.1 - x.1) - (y.2 - x.2)|)

end ApollonianSuperharmonic

end
