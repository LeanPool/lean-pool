/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary

-- [TABLET NODE: P3544T1BoundaryCarrier]

/-!
# P3544T1BoundaryCarrier

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For every integer $n\ge0$ and every
$p\in\operatorname{PolygonBoundary}(n)$ as defined in
`P3381T1PolygonBoundary`, write $p_i$ for the vertex at index
$i\in\operatorname{Fin}(n+3)=\{0,\ldots,n+2\}$.  Here $i+1$ denotes
the cyclic successor modulo $n+3$.  The geometric carrier of $p$ is
$$
 C_p:=\bigcup_{i\in\operatorname{Fin}(n+3)}[p_i,p_{i+1}]
       \subseteq\mathbb R^2,
$$
where each $[p_i,p_{i+1}]$ is the closed real line segment between its
endpoints.  All indexed vertices, including straight vertices, are
retained.  This carrier is not a filled region; no interior region or
disk model is supplied.
-/
def P3544T1BoundaryCarrier {n : Nat} (p : P3381T1PolygonBoundary n) :
    Set (Real × Real) :=
-- BODY
  ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1))

end ApollonianSuperharmonic

end
