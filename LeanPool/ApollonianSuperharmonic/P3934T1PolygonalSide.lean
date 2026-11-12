/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3934T1LocalSide
public import LeanPool.ApollonianSuperharmonic.P3723T1PolygonalParameterization

-- [TABLET NODE: P3934T1PolygonalSide]

/-!
# P3934T1PolygonalSide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $s$ be a `P3723T1PolygonalParameterization` of $g$,
with strictly increasing subdivision times $t_i$.
The predicate $\operatorname{PolySide}(U,g,s,e)$ means that for every
piece $i$ there are $A_i,B_i\in\mathbb R^2$ with $B_i\ne0$ such that
$g(t)=A_i+tB_i$ throughout $[t_i,t_{i+1}]$, and
$\operatorname{Side}(U,g(t),B_i,e)$ for every $t_i<t<t_{i+1}$.
The local-side predicate is `P3934T1LocalSide`.
-/
def P3934T1PolygonalSide (U : Set (Real × Real))
    (g : Set.Icc (0 : Real) 1 → Real × Real)
    (s : P3723T1PolygonalParameterization g) (e : Bool) : Prop :=
-- BODY
  ∀ i : Fin s.count, ∃ A B : Real × Real, B ≠ 0 ∧
    (∀ t : Set.Icc (0 : Real) 1,
      s.time i.castSucc ≤ (t : Real) → (t : Real) ≤ s.time i.succ →
        g t = A + (t : Real) • B) ∧
    ∀ t : Set.Icc (0 : Real) 1,
      s.time i.castSucc < (t : Real) → (t : Real) < s.time i.succ →
        P3934T1LocalSide U (g t) B e

end ApollonianSuperharmonic

end
