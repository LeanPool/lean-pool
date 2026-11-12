/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: P3381T1TriangleDeterminant]

/-!
# P3381T1TriangleDeterminant

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For three plane points $p_0,p_1,p_2$, put
$$
 d(p)= (p_1-p_0)_1(p_2-p_0)_2-(p_2-p_0)_1(p_1-p_0)_2.
$$
Thus $d(p)\ne0$ means that the triangle is nondegenerate; its unsigned
area is $|d(p)|/2$.
-/
def P3381T1TriangleDeterminant (p : Fin 3 → Real × Real) : Real :=
-- BODY
  (p 1 - p 0).1 * (p 2 - p 0).2 -
    (p 2 - p 0).1 * (p 1 - p 0).2

end ApollonianSuperharmonic

end
