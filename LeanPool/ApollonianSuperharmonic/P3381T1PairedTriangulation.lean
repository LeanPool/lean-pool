/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.MetricSpace.Bounded

public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import Mathlib.Analysis.Convex.Hull

-- [TABLET NODE: P3381T1PairedTriangulation]

/-!
# P3381T1PairedTriangulation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $p$ be a `P3381T1PolygonBoundary`, and let $X,K\subseteq
\mathbb R^2$.  A paired triangulation consists of distinct target points
$q_i$, a finite indexed family of triples $f_k$ of distinct vertex
indices, and the following certificates.  The target boundary segments
have exactly the same simplicity condition as the source boundary.
Distinct triples have distinct sets of indices, and every vertex index
occurs in a triple.  Both source and target triangles are nondegenerate
in the sense of `P3381T1TriangleDeterminant`.
Put
$$
 \Delta_k=\operatorname{conv}\{p_{f_k(0)},p_{f_k(1)},p_{f_k(2)}\},
 \qquad
 \Delta'_k=\operatorname{conv}\{q_{f_k(0)},q_{f_k(1)},q_{f_k(2)}\}.
$$
The coverage certificates are $X=\bigcup_k\Delta_k$ and
$K=\bigcup_k\Delta'_k$.  If $J_{kl}$ is the intersection of the two
sets of indices, the exact face-intersection certificates are
$$
 \Delta_k\cap\Delta_l=\operatorname{conv}\{p_i:i\in J_{kl}\},
 \qquad
 \Delta'_k\cap\Delta'_l=\operatorname{conv}\{q_i:i\in J_{kl}\}.
$$
The convex hull of the empty set is empty.  For any two distinct indices
$i,j$, precisely one triangle contains them both if they are cyclic
neighbors.  Otherwise precisely two triangles contain them both if any
does, and none do if none does.  These are counts of indexed triangles,
not an assertion about a drawing supplied elsewhere.

Finally, $K$ equals the convex hull of all $q_i$, is convex, closed and
bounded, has nonempty ambient interior, and its actual ambient frontier
is $\bigcup_i[q_i,q_{i+1}]$.  Every source boundary vertex, including a
straight vertex or an inserted rational port, remains an index in both
realizations.  No source diskness, source frontier formula,
homeomorphism, or separation conclusion is assumed.
-/
structure P3381T1PairedTriangulation {n : Nat}
    (p : P3381T1PolygonBoundary n) (X K : Set (Real × Real)) where
-- BODY
  /-- The target positions of the unchanged boundary labels. -/
  target : Fin (n + 3) → Real × Real
  target_injective : Function.Injective target
  target_edge_intersection : ∀ i j : Fin (n + 3), i ≠ j →
    segment Real (target i) (target (i + 1)) ∩
      segment Real (target j) (target (j + 1)) =
      {x | (x = target i ∨ x = target (i + 1)) ∧
        (x = target j ∨ x = target (j + 1))}
  /-- The number of indexed triangles in the common face family. -/
  count : Nat
  /-- The three boundary labels of each indexed triangle. -/
  face : Fin count → Fin 3 → Fin (n + 3)
  face_injective : ∀ k, Function.Injective (face k)
  face_distinct : Function.Injective (fun k => Set.range (face k))
  vertex_used : ∀ i, ∃ k j, face k j = i
  source_nondegenerate : ∀ k,
    P3381T1TriangleDeterminant (p.vertex ∘ face k) ≠ 0
  target_nondegenerate : ∀ k,
    P3381T1TriangleDeterminant (target ∘ face k) ≠ 0
  source_cover : X = ⋃ k, convexHull Real (Set.range (p.vertex ∘ face k))
  target_cover : K = ⋃ k, convexHull Real (Set.range (target ∘ face k))
  source_intersection : ∀ k l,
    convexHull Real (Set.range (p.vertex ∘ face k)) ∩
      convexHull Real (Set.range (p.vertex ∘ face l)) =
      convexHull Real (p.vertex '' (Set.range (face k) ∩ Set.range (face l)))
  target_intersection : ∀ k l,
    convexHull Real (Set.range (target ∘ face k)) ∩
      convexHull Real (Set.range (target ∘ face l)) =
      convexHull Real (target '' (Set.range (face k) ∩ Set.range (face l)))
  edge_count : ∀ i j : Fin (n + 3), i ≠ j →
    Set.ncard {k : Fin count |
      i ∈ Set.range (face k) ∧ j ∈ Set.range (face k)} =
      if j = i + 1 ∨ i = j + 1 then 1
      else if ∃ k, i ∈ Set.range (face k) ∧ j ∈ Set.range (face k) then 2 else 0
  target_hull : K = convexHull Real (Set.range target)
  target_convex : Convex Real K
  target_closed : IsClosed K
  target_bounded : Bornology.IsBounded K
  target_interior : (interior K).Nonempty
  target_frontier : frontier K = ⋃ i, segment Real (target i) (target (i + 1))

end ApollonianSuperharmonic

end
