/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant

-- [TABLET NODE: P3511T1ConvexRealization]

/-!
# P3511T1ConvexRealization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For triples $f_k$ on $m=n+3$ indices and a plane set $K$, a convex
realization consists of target points $q_i=(i,i^2)$ and the following
certificates.  The target points are distinct, and different cyclic
boundary segments intersect exactly in their common endpoints, as in
`P3381T1PolygonBoundary`.  Every target triangle has nonzero
`P3381T1TriangleDeterminant`.  For
$\Delta'_k=\operatorname{conv}\{q_{f_k(j)}:0\le j<3\}$ one has
$$
 K=\bigcup_k\Delta'_k,\qquad
 \Delta'_k\cap\Delta'_l=
 \operatorname{conv}\{q_i:i\in\operatorname{range}f_k
                         \cap\operatorname{range}f_l\}.
$$
Moreover $K=\operatorname{conv}\{q_i:0\le i<m\}$; $K$ is convex,
closed and bounded, has nonempty ambient interior, and its actual
ambient frontier is $\bigcup_i[q_i,q_{i+1}]$, with indices taken
cyclically.  These certificates concern the given indexed faces, not
an independently chosen triangulation of the hull.
-/
structure P3511T1ConvexRealization {n count : Nat}
    (face : Fin count → Fin 3 → Fin (n + 3)) (K : Set (Real × Real)) where
-- BODY
  /-- The comparison positions on the parabola, one for each original boundary label. -/
  target : Fin (n + 3) → Real × Real
  parabola : ∀ i, target i = ((i.val : Real), (i.val : Real) ^ 2)
  target_injective : Function.Injective target
  target_edge_intersection : ∀ i j : Fin (n + 3), i ≠ j →
    segment Real (target i) (target (i + 1)) ∩
      segment Real (target j) (target (j + 1)) =
      {x | (x = target i ∨ x = target (i + 1)) ∧
        (x = target j ∨ x = target (j + 1))}
  target_nondegenerate : ∀ k,
    P3381T1TriangleDeterminant (target ∘ face k) ≠ 0
  target_cover : K = ⋃ k, convexHull Real (Set.range (target ∘ face k))
  target_intersection : ∀ k l,
    convexHull Real (Set.range (target ∘ face k)) ∩
      convexHull Real (Set.range (target ∘ face l)) =
      convexHull Real (target '' (Set.range (face k) ∩ Set.range (face l)))
  target_hull : K = convexHull Real (Set.range target)
  target_convex : Convex Real K
  target_closed : IsClosed K
  target_bounded : Bornology.IsBounded K
  target_interior : (interior K).Nonempty
  target_frontier : frontier K = ⋃ i, segment Real (target i) (target (i + 1))

end ApollonianSuperharmonic

end
