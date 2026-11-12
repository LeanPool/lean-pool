/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3381T1PairedTriangulation

-- [TABLET NODE: P3475T1TriangleTree]

/-!
# P3475T1TriangleTree

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a boundary $p$ and plane sets $X,K$, an exact triangle attachment tree
contains all the data and certificates of
`P3381T1PairedTriangulation` for $(p,X,K)$, together with a
positive triangle count and a permutation $o$ of the triangle indices.
For every $k>0$ there are distinct indices $a,b,c$ such that the $k$th
triangle in this order has vertex set $\{a,b,c\}$, $c$ occurs in no
earlier triangle, and precisely one earlier triangle contains both
$a,b$.  In both the source and target realizations, the intersection of
this triangle with the union of all earlier closed triangles is exactly
the entire segment joining the vertices $a,b$.
In particular the new triangle is attached along one old boundary edge;
it has no additional contact with the old union.  This records finite
attachment geometry, not connected complementary domains.
-/
structure P3475T1TriangleTree {n : Nat}
    (p : P3381T1PolygonBoundary n) (X K : Set (Real × Real))
    extends P3381T1PairedTriangulation p X K where
-- BODY
  count_pos : 0 < count
  /-- The triangle attachment order, with each later triangle attached along one old edge. -/
  order : Fin count ≃ Fin count
  attachment : ∀ k : Fin count, 0 < k.val →
    ∃ a b c : Fin (n + 3), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Set.range (face (order k)) = {a, b, c} ∧
      (∀ l : Fin count, l.val < k.val → c ∉ Set.range (face (order l))) ∧
      Set.ncard {l : Fin count | l.val < k.val ∧
        a ∈ Set.range (face (order l)) ∧ b ∈ Set.range (face (order l))} = 1 ∧
      (convexHull Real (Set.range (p.vertex ∘ face (order k))) ∩
        (⋃ l : {l : Fin count // l.val < k.val},
          convexHull Real (Set.range (p.vertex ∘ face (order l.val))))) =
          segment Real (p.vertex a) (p.vertex b) ∧
      (convexHull Real (Set.range (target ∘ face (order k))) ∩
        (⋃ l : {l : Fin count // l.val < k.val},
          convexHull Real (Set.range (target ∘ face (order l.val))))) =
          segment Real (target a) (target b)

end ApollonianSuperharmonic

end
