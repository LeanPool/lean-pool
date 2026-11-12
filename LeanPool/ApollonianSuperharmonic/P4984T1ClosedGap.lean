/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4909T1ParentPolygon

-- [TABLET NODE: P4984T1ClosedGap]

/-!
# P4984T1ClosedGap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a real supporting offset $L$ and a coordinate quadruple $q$, put
$p_i=w_i/c_i$ and $r_i=1/c_i$ whenever $q_i=(c_i,w_i)$ has $c_i>0$.
The closed analytic gap is
$$
 H_L(q)=P_L(q)\cap\bigcap_{j\in\{1,2,3\},\ c_j>0}
             \{z:|z-p_j|\geq r_j\},
$$
where $P_L(q)$ is the parent polygon of
`P4909T1ParentPolygon`. Zero-curvature entries contribute
their signed supporting line to that polygon, not a circle of radius
$1/0$.
-/
def P4984T1ClosedGap (L : Real) (q : Fin 4 → CircleCoordinates) : Set Complex :=
-- BODY
  {p | p ∈ P4909T1ParentPolygon L q ∧
    ∀ j : Fin 3, 0 < (q j.succ).1 →
      (1 / ((q j.succ).1 : Real)) ≤
        dist p ((q j.succ).2 / ((q j.succ).1 : Real))}

end ApollonianSuperharmonic

end
