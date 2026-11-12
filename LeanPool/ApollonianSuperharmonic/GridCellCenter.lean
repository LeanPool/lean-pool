/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeCell

-- [TABLET NODE: GridCellCenter]

/-!
# GridCellCenter

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a lattice cell $q=(q_1,q_2)$, its center, viewed as a complex point,
is
$$
q^*=q_1+\frac12+i\left(q_2+\frac12\right).
$$
-/
noncomputable def GridCellCenter (q : LatticeCell) : ℂ :=
-- BODY
  (((q.re : Int) : Real) + (1 / 2 : Real) : ℂ) +
    (((q.im : Int) : Real) + (1 / 2 : Real) : ℂ) * Complex.I

end ApollonianSuperharmonic

end
