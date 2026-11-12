/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple

-- [TABLET NODE: PrimitiveVectorOrientation]

/-!
# PrimitiveVectorOrientation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The primitive orientation of an unoriented band-tangent edge is chosen from
the stage where that edge enters the directed semi-proper genealogy.  At a
proper quadruple
$(C_0,C_1,C_2,C_3)$ it points from each parent to the child,
$C_j\longrightarrow C_0$ for $j=1,2,3$.  At a root
$$
 ((1,1+2z),(1,1+2z+2i),(0,1),(0,-1))
$$
the four primitive root orientations are
$$
 C_3\longrightarrow C_2,\qquad C_2\longrightarrow C_1,\qquad
 C_3\longrightarrow C_1,\qquad C_1\longrightarrow C_0.
$$
For the first two, the manuscript gives the primitive base value directly.
For $C_3\to C_1$ it gives the opposite value $v_{13},a_{13}$, from which the
primitive value is recovered by the single quarter-turn rule.  The fourth is
the remaining edge between adjacent unit circles; its values are obtained by
applying the successor formulas to a parent rotation of the root.  Parameter
shifts identify the other two child--line edges with the displayed root
families.  These choices make the reverse rule have the same sign on every
root and proper parent--child edge.  This is a relation on curvature
coordinates, not on derivation codes.
-/
inductive PrimitiveVectorOrientation :
    CircleCoordinates → CircleCoordinates → Prop where
-- BODY
  | base32 (z : GaussianInt) :
      PrimitiveVectorOrientation (0, -1) (0, 1)
  | base21 (z : GaussianInt) :
      PrimitiveVectorOrientation (0, 1)
        (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt))
  | base31 (z : GaussianInt) :
      PrimitiveVectorOrientation
        (0, -1) (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt))
  | base10 (z : GaussianInt) :
      PrimitiveVectorOrientation
        (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt))
        (1, 1 + 2 * z)
  | parentChild {q : Fin 4 → CircleCoordinates}
      (hq : ProperBandQuadruple q) (j : Fin 3) :
      PrimitiveVectorOrientation (q j.succ) (q 0)

end ApollonianSuperharmonic

end
