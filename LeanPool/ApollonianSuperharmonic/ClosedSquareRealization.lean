/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeCell

-- [TABLET NODE: ClosedSquareRealization]

/-!
# ClosedSquareRealization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For the cell $s_x$, its closed-square realization is
$$
 \overline s_x=[\Re x,\Re x+1]\times[\Im x,\Im x+1]\subset\mathbb R^2.
$$
In particular, adjacent cells retain their common boundary in the real
realization.
-/
def ClosedSquareRealization (x : LatticeCell) : Set (Real × Real) :=
-- BODY
  Set.Icc ((((x.re : Int) : Real)), (((x.im : Int) : Real)))
    (((((x.re : Int) : Real)) + 1), ((((x.im : Int) : Real)) + 1))

end ApollonianSuperharmonic

end
