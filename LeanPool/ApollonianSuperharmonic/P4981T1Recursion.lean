/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: P4981T1Recursion]

/-!
# P4981T1Recursion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an edge-value function
$F=(v,a):(\mathbb Z\times\mathbb Z[i])^2\to\mathbb Z[i]^2$
and a coordinate tuple $q$, its local
successor equations mean the four equalities
$$
 v_{20}=v_{21}-i v_{32},\qquad v_{03}=v_{13}+i v_{32},\qquad
 a_{20}=a_{21}+i a_{32},\qquad a_{03}=a_{13}-i a_{32},
$$
where $v_{jk},a_{jk}$ are the components of $F(q_j,q_k)$.
-/
def P4981T1Recursion
    (F : CircleCoordinates × CircleCoordinates → GaussianInt × GaussianInt)
    (q : Fin 4 → CircleCoordinates) : Prop :=
-- BODY
  let ii : GaussianInt := ⟨0, 1⟩
  (F (q 2, q 0)).1 = (F (q 2, q 1)).1 - ii * (F (q 3, q 2)).1 ∧
  (F (q 0, q 3)).1 = (F (q 1, q 3)).1 + ii * (F (q 3, q 2)).1 ∧
  (F (q 2, q 0)).2 = (F (q 2, q 1)).2 + ii * (F (q 3, q 2)).2 ∧
  (F (q 0, q 3)).2 = (F (q 1, q 3)).2 - ii * (F (q 3, q 2)).2

end ApollonianSuperharmonic

end
