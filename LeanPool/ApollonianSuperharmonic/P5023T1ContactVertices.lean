/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Real.Sqrt

-- [TABLET NODE: P5023T1ContactVertices]

/-!
# P5023T1ContactVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For arbitrary $L\in\mathbb R$ and $q$, index the parents by
$i\in\mathbb Z/3\mathbb Z$, so that $q_{i+1}=(c_i,w_i)$, and put
$p_i=w_i/c_i$. For distinct parent indices define the total expression
$$
 d_{ij}=\begin{cases}
 (h_i,\operatorname{Im}p_j),&c_i=0,\\
 (h_j,\operatorname{Im}p_i),&c_i\ne0,\ c_j=0,\\
 (w_i+w_j)/(c_i+c_j),&c_i\ne0,\ c_j\ne0,
 \end{cases}\qquad
 h_i=\begin{cases}L,&w_i=-1,\\ L+2,&w_i\ne-1.\end{cases}
$$
Set $v_k=d_{k+1,k+2}$, with the subscripts on $d$ taken modulo three.
This function is `P5023T1ContactVertices`.
The conventions for $h_i$ agree with
`P4909T1ParentPolygon`. As usual, field division by zero
is interpreted by its total field definition; no geometric meaning
is asserted for arbitrary raw inputs.
When the parents are externally tangent positive circles, or two
positive circles tangent from the inward side to one signed band line,
these are their three pairwise contacts. In particular $v_{i+1}$ and
$v_{i+2}$ are the two contacts on parent $i$, also when that parent is
the line. This last description is conditional, not an additional
assumption in the total definition.
-/
noncomputable def P5023T1ContactVertices (L : ℝ)
    (q : Fin 4 → CircleCoordinates) : Fin 3 → ℂ :=
-- BODY
  let contact (i j : Fin 3) : ℂ :=
    if (q i.succ).1 = 0 then
      ⟨if (q i.succ).2 = -1 then L else L + 2,
        ((q j.succ).2 / ((q j.succ).1 : ℝ) : ℂ).im⟩
    else if (q j.succ).1 = 0 then
      ⟨if (q j.succ).2 = -1 then L else L + 2,
        ((q i.succ).2 / ((q i.succ).1 : ℝ) : ℂ).im⟩
    else
      ((q i.succ).2 + (q j.succ).2 : ℂ) /
        (((q i.succ).1 : ℝ) + ((q j.succ).1 : ℝ))
  fun k => contact (k + 1) (k + 2)

end ApollonianSuperharmonic

end
