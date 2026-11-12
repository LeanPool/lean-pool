/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P4793T1FacetForms]

/-!
# P4793T1FacetForms

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
In the cyclic side order of the coefficient hexagon, let $F_l$,
$l=0,\ldots,5$, be the following real-valued affine maps on the real plane:
$$
F_0(s,t)=-2s+t,\quad F_1(s,t)=-s+2t+1,\quad
F_2(s,t)=s+t+2,\quad F_3(s,t)=2s-t+2,\quad
F_4(s,t)=s-2t+1,\quad F_5(s,t)=-s-t.
$$
-/
def P4793T1FacetForms (l : Fin 6) : (Real × Real) →ᵃ[Real] Real :=
-- BODY
  let t : Real × Real × Real :=
    ![(-2,1,0),(-1,2,1),(1,1,2),(2,-1,2),(1,-2,1),(-1,-1,0)] l
  { toFun := fun z => t.1*z.1+t.2.1*z.2+t.2.2
    linear :=
      { toFun := fun z => t.1*z.1+t.2.1*z.2
        map_add' := by intros; simp; ring
        map_smul' := by intros; simp; ring }
    map_vadd' := by intros; simp; ring }

end ApollonianSuperharmonic

end
