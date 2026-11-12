/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: P4828T1LineSupport]

/-!
# P4828T1LineSupport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A signed line-support certificate at offset $L$ for $q$ says that every
zero-curvature entry has numerator $n=-1$ or $1$, and for every such entry
and every positive entry $(c,w)$,
$$
 n\operatorname{Re}w-c h_n=-1,\qquad h_{-1}=-L,\quad h_1=L+2.
$$
It is denoted by `P4828T1LineSupport`. Equivalently the circle is
tangent from inside the strip to the contextual supporting line
$nX=h_n$. This records the side and offset, not merely unsigned tangency.
-/
structure P4828T1LineSupport (L : Real)
    (q : Fin 4 → CircleCoordinates) : Prop where
-- BODY
  normals : ∀ k : Fin 4, (q k).1 = 0 → (q k).2 = -1 ∨ (q k).2 = 1
  signed : ∀ k j : Fin 4, (q k).1 = 0 → 0 < (q j).1 →
    ((q k).2.re : Real) * ((q j).2.re : Real) - (q j).1 *
      (if (q k).2 = -1 then -L else L + 2) = -1

end ApollonianSuperharmonic

end
