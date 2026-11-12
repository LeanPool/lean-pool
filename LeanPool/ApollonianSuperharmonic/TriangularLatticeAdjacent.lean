/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: TriangularLatticeAdjacent]

/-!
# TriangularLatticeAdjacent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two points of $\mathbb Z^2$ are *triangular-lattice adjacent* when
their difference is one of
$$
 \pm(1,0),\qquad \pm(0,1),\qquad \pm(-1,-1).
$$
This is the standard six-step affine triangular graph, considered here
without any band-circle or tile data.
-/
def TriangularLatticeAdjacent (x y : Int × Int) : Prop :=
-- BODY
  y - x = ((1, 0) : Int × Int) ∨
  y - x = ((0, 1) : Int × Int) ∨
  y - x = ((-1, -1) : Int × Int) ∨
  y - x = ((-1, 0) : Int × Int) ∨
  y - x = ((0, -1) : Int × Int) ∨
  y - x = ((1, 1) : Int × Int)

end ApollonianSuperharmonic

end
