/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3934T1PolygonalSide

-- [TABLET NODE: P3934T1ArcSide]

/-!
# P3934T1ArcSide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The predicate $\operatorname{ArcSide}(U,S,a,b,e)$ means that there
exists a continuous injective map $g:[0,1]\to\mathbb R^2$ with image
$S$, $g(0)=a$, $g(1)=b$, and a
`P3723T1PolygonalParameterization` $s$ of $g$ for which
$\operatorname{PolySide}(U,g,s,e)$ holds in the sense of
`P3934T1PolygonalSide`.
-/
def P3934T1ArcSide (U S : Set (Real × Real)) (a b : Real × Real)
    (e : Bool) : Prop :=
-- BODY
  ∃ g : Set.Icc (0 : Real) 1 → Real × Real,
    Continuous g ∧ Function.Injective g ∧ Set.range g = S ∧
      g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
      ∃ s : P3723T1PolygonalParameterization g,
        P3934T1PolygonalSide U g s e

end ApollonianSuperharmonic

end
