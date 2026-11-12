/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary

-- [TABLET NODE: P3475T1BoundarySubdivision]

/-!
# P3475T1BoundarySubdivision

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $q$ and $p$ be boundaries as in
`P3381T1PolygonBoundary`, with $r+3$ and $n+3$ vertices.
An ordered subdivision of $q$ by $p$ records an injective map $s$ of
coarse vertices to original indices, an edge index $e(j)$ and a real
parameter $t_j$ for each original index, satisfying
$$
0\le t_j<1,\qquad e(s(i))=i,\quad t_{s(i)}=0,\qquad
p_j=(1-t_j)q_{e(j)}+t_jq_{e(j)+1}.
$$
At each cyclic successor either the edge index stays the same and the
parameter strictly increases, or the edge index advances by one and the
new parameter is zero.  The carriers agree exactly:
$\bigcup_j[p_j,p_{j+1}]=\bigcup_i[q_i,q_{i+1}]$.
Thus the coarse endpoints are present, and each coarse edge is replaced
in its original direction by consecutive subsegments.  No region or
topological conclusion is part of this data.
-/
structure P3475T1BoundarySubdivision {r n : Nat}
    (q : P3381T1PolygonBoundary r) (p : P3381T1PolygonBoundary n) where
-- BODY
  /-- The original fine label at each coarse boundary vertex. -/
  start : Fin (r + 3) → Fin (n + 3)
  start_injective : Function.Injective start
  /-- The coarse edge containing each fine boundary vertex. -/
  edge : Fin (n + 3) → Fin (r + 3)
  /-- The parameter in [0,1) locating a fine vertex along its directed coarse edge. -/
  parameter : Fin (n + 3) → Real
  parameter_nonneg : ∀ j, 0 ≤ parameter j
  parameter_lt_one : ∀ j, parameter j < 1
  edge_start : ∀ i, edge (start i) = i
  parameter_start : ∀ i, parameter (start i) = 0
  vertex_formula : ∀ j,
    p.vertex j = (1 - parameter j) • q.vertex (edge j) +
      parameter j • q.vertex (edge j + 1)
  successor : ∀ j,
    (edge (j + 1) = edge j ∧ parameter j < parameter (j + 1)) ∨
    (edge (j + 1) = edge j + 1 ∧ parameter (j + 1) = 0)
  carrier_eq :
    (⋃ j, segment Real (p.vertex j) (p.vertex (j + 1))) =
      ⋃ i, segment Real (q.vertex i) (q.vertex (i + 1))

end ApollonianSuperharmonic

end
