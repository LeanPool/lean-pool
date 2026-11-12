/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3511T1CyclicDissection
public import LeanPool.ApollonianSuperharmonic.P3381T1PolygonBoundary
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import Mathlib.Data.Set.Card

-- [TABLET NODE: P3511T1SourceDissection]

/-!
# P3511T1SourceDissection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a boundary $p$ of `P3381T1PolygonBoundary` with $m=n+3$
vertices and a plane set $X$, a source dissection consists of a positive
integer $N$ and triples $f_k:\{0,1,2\}\to\{0,\ldots,m-1\}$,
$0\le k<N$.  The increasing full index list $[0,\ldots,m-1]$ and the
ordered list $(f_k)_{k<N}$ have a saved
`P3511T1CyclicDissection`.  Each triple is injective, their
index sets are distinct, and every boundary index occurs in a triple.
Every source triangle has nonzero
`P3381T1TriangleDeterminant`.  Writing
$\Delta_k=\operatorname{conv}\{p_{f_k(j)}:0\le j<3\}$, the geometric
certificates are
$$
 X=\bigcup_{k<N}\Delta_k,\qquad
 \Delta_k\cap\Delta_l=
 \operatorname{conv}\{p_i:i\in\operatorname{range}f_k
                         \cap\operatorname{range}f_l\}.
$$
For distinct indices $i,j$, the number of indexed triangles containing
both is one for cyclic neighbors, two for a used nonboundary pair,
and zero for an unused nonboundary pair.  The hull of an empty common
index set is empty.  No target coordinates, attachment ordering,
homeomorphism, or connectedness of the exterior is included.
-/
structure P3511T1SourceDissection {n : Nat}
    (p : P3381T1PolygonBoundary n) (X : Set (Real × Real)) where
-- BODY
  /-- The positive number of source triangles. -/
  count : Nat
  count_pos : 0 < count
  /-- The ordered triples of original labels in the saved cyclic dissection. -/
  face : Fin count → Fin 3 → Fin (n + 3)
  dissection : P3511T1CyclicDissection (Fin (n + 3))
    (List.ofFn (fun i : Fin (n + 3) => i)) (List.ofFn face)
  face_injective : ∀ k, Function.Injective (face k)
  face_distinct : Function.Injective (fun k => Set.range (face k))
  vertex_used : ∀ i, ∃ k j, face k j = i
  nondegenerate : ∀ k,
    P3381T1TriangleDeterminant (p.vertex ∘ face k) ≠ 0
  cover : X = ⋃ k, convexHull Real (Set.range (p.vertex ∘ face k))
  intersection : ∀ k l,
    convexHull Real (Set.range (p.vertex ∘ face k)) ∩
      convexHull Real (Set.range (p.vertex ∘ face l)) =
      convexHull Real (p.vertex '' (Set.range (face k) ∩ Set.range (face l)))
  edge_count : ∀ i j : Fin (n + 3), i ≠ j →
    Set.ncard {k : Fin count |
      i ∈ Set.range (face k) ∧ j ∈ Set.range (face k)} =
      if j = i + 1 ∨ i = j + 1 then 1
      else if ∃ k, i ∈ Set.range (face k) ∧ j ∈ Set.range (face k) then 2 else 0

end ApollonianSuperharmonic

end
