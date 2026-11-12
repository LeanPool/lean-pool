/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.Basic
public import Mathlib.Basic.Real.Basic

public import Mathlib.Analysis.Convex.Segment

-- [TABLET NODE: P3381T1PolygonBoundary]

/-!
# P3381T1PolygonBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $n\ge0$, a polygonal boundary consists of $n+3$ rational plane
points $p_i$, indexed cyclically, with the following geometric conditions.
The points are distinct.  For different indices $i,j$, the closed
segments $[p_i,p_{i+1}]$ and $[p_j,p_{j+1}]$ intersect exactly in their
common endpoints.  In particular nonneighboring segments are disjoint,
and neighboring segments intersect only in their shared endpoint.
Straight vertices are allowed and are retained as indexed vertices;
inserting finitely many distinct rational points in the relative
interiors of the boundary segments is permitted when these conditions
continue to hold.  No interior region or disk model is part of this data.
-/
structure P3381T1PolygonBoundary (n : Nat) where
-- BODY
  /-- The distinct rational plane vertices in cyclic boundary order. -/
  vertex : Fin (n + 3) → Real × Real
  rational : ∀ i, ∃ r s : Rat, vertex i = ((r : Real), (s : Real))
  injective : Function.Injective vertex
  edge_intersection : ∀ i j : Fin (n + 3), i ≠ j →
    segment Real (vertex i) (vertex (i + 1)) ∩
      segment Real (vertex j) (vertex (j + 1)) =
      {x | (x = vertex i ∨ x = vertex (i + 1)) ∧
        (x = vertex j ∨ x = vertex (j + 1))}

end ApollonianSuperharmonic

end
