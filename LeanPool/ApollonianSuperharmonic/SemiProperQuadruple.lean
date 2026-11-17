/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: SemiProperQuadruple]

/-!
# SemiProperQuadruple

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A semi-proper Descartes quadruple is a coordinate quadruple in the directed
forest generated as follows.  For every $z\in\mathbb Z[i]$ the clockwise
base quadruple is
$$
 ((1,1+2z),(1,1+2z+2i),(0,1),(0,-1)).
$$
The class is closed under parent rotation
$(C_0,C_1,C_2,C_3)\mapsto(C_0,C_2,C_3,C_1)$ and under the successor operation
$$
 (C_0,C_1,C_2,C_3)\mapsto
 (2(C_0+C_2+C_3)-C_1,C_0,C_2,C_3),
$$
where both components of curvature coordinates are combined linearly.
Thus this is a predicate on coordinate quadruples, rather than a type of
derivation codes.
-/
inductive SemiProperQuadruple : (Fin 4 → CircleCoordinates) → Prop where
-- BODY
  | base (z : GaussianInt) :
      SemiProperQuadruple ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
        (0, 1), (0, -1)]
  | rotate {q : Fin 4 → CircleCoordinates} (hq : SemiProperQuadruple q) :
      SemiProperQuadruple ![q 0, q 2, q 3, q 1]
  | successor {q : Fin 4 → CircleCoordinates} (hq : SemiProperQuadruple q) :
      SemiProperQuadruple
        ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
            2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
          q 0, q 2, q 3]

end ApollonianSuperharmonic

end
