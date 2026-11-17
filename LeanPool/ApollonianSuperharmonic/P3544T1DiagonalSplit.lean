/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import LeanPool.ApollonianSuperharmonic.P3544T1RayParity
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order

-- [TABLET NODE: P3544T1DiagonalSplit]

/-!
# P3544T1DiagonalSplit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $p$ with $n+3$ vertices, this data consists of two integers
$n_L,n_R<n$, boundaries $p^L,p^R$ of
`P3381T1PolygonBoundary`, and injective index maps $\iota_L,\iota_R$
with $p^L=p\circ\iota_L$ and $p^R=p\circ\iota_R$.  It also consists
of distinct parent indices $a,b$, nonempty lists $U,V$, and a rotation
$k$, with the exact ordered-list identities
$$
 [0,\ldots,n+2].\operatorname{rotate}(k)=[a]+U+[b]+V,
 \quad\operatorname{ofFn}(\iota_L)=[a]+U+[b],\quad
 \operatorname{ofFn}(\iota_R)=[b]+V+[a].
$$
The image index sets intersect exactly in $\{a,b\}$.  Write
$e=[p_a,p_b]$, $e^\circ=(p_a,p_b)$, and use the carriers and odd sets
of `P3544T1BoundaryCarrier` and `P3544T1RayParity`.
The required geometric fields are
$$
 C_L\cup C_R=C_p\cup e,\quad C_L\cap C_R=e,\quad e^\circ\subset O_p,
 \quad(C_L\setminus e)\cap O_R=\varnothing,
 \quad(C_R\setminus e)\cap O_L=\varnothing.
$$
Off $C_L\cup C_R$, parent oddness is the exclusive-or of child oddness.
Balls use the product metric on the plane.
At each $x\in e^\circ$ there is a ball and a Boolean sign choice
on which the left and right odd sets are respectively the positive
and negative strict half-planes of $\det(p_b-p_a,y-p_a)$, or respectively
the negative and positive half-planes.  The determinant is equivalently
`P3381T1TriangleDeterminant` of $(p_a,p_b,y)$.
At either endpoint $z$ there is a ball on which
$$
 B(z,r)\cap O_p=B(z,r)\cap(O_L\cup O_R\cup e^\circ).
$$
No child face family, filled child intersection, or source dissection
is part of this split data.
-/
structure P3544T1DiagonalSplit {n : Nat} (p : P3381T1PolygonBoundary n) where
-- BODY
  /-- The size parameter of the left child polygon. -/
  leftParameter : Nat
  /-- The size parameter of the right child polygon. -/
  rightParameter : Nat
  left_lt : leftParameter < n
  right_lt : rightParameter < n
  /-- The boundary following the first saved cyclic arc and the diagonal. -/
  left : P3381T1PolygonBoundary leftParameter
  /-- The boundary following the complementary saved cyclic arc and the diagonal. -/
  right : P3381T1PolygonBoundary rightParameter
  /-- Embed the left child labels into the original cyclic boundary. -/
  il : Fin (leftParameter + 3) → Fin (n + 3)
  /-- Embed the right child labels into the original cyclic boundary. -/
  ir : Fin (rightParameter + 3) → Fin (n + 3)
  il_injective : Function.Injective il
  ir_injective : Function.Injective ir
  left_vertex : left.vertex = p.vertex ∘ il
  right_vertex : right.vertex = p.vertex ∘ ir
  /-- The first original boundary label at an endpoint of the splitting diagonal. -/
  a : Fin (n + 3)
  /-- The second original boundary label at the other diagonal endpoint. -/
  b : Fin (n + 3)
  a_ne_b : a ≠ b
  /-- The nonempty list of parent labels strictly inside the first saved arc. -/
  u : List (Fin (n + 3))
  /-- The nonempty list of parent labels strictly inside the complementary arc. -/
  v : List (Fin (n + 3))
  hu : 0 < u.length
  hv : 0 < v.length
  /-- The rotation identifying the saved pair of arcs with the original cyclic list. -/
  rotation : Nat
  parent_order : (List.ofFn (fun i : Fin (n + 3) => i)).rotate rotation =
    a :: (u ++ b :: v)
  left_order : List.ofFn il = a :: (u ++ [b])
  right_order : List.ofFn ir = b :: (v ++ [a])
  common_indices : Set.range il ∩ Set.range ir = {a, b}
  carrier_union : P3544T1BoundaryCarrier left ∪ P3544T1BoundaryCarrier right =
    P3544T1BoundaryCarrier p ∪ segment Real (p.vertex a) (p.vertex b)
  carrier_intersection : P3544T1BoundaryCarrier left ∩
    P3544T1BoundaryCarrier right = segment Real (p.vertex a) (p.vertex b)
  diagonal_odd : openSegment Real (p.vertex a) (p.vertex b) ⊆ P3544T1RayParity p
  left_arc_even : Disjoint
    (P3544T1BoundaryCarrier left \ segment Real (p.vertex a) (p.vertex b))
    (P3544T1RayParity right)
  right_arc_even : Disjoint
    (P3544T1BoundaryCarrier right \ segment Real (p.vertex a) (p.vertex b))
    (P3544T1RayParity left)
  parity_sum : ∀ x, x ∉ P3544T1BoundaryCarrier left →
    x ∉ P3544T1BoundaryCarrier right →
    (x ∈ P3544T1RayParity p ↔
      (x ∈ P3544T1RayParity left ∧ x ∉ P3544T1RayParity right) ∨
      (x ∉ P3544T1RayParity left ∧ x ∈ P3544T1RayParity right))
  diagonal_sides : ∀ x, x ∈ openSegment Real (p.vertex a) (p.vertex b) →
    ∃ r : Real, 0 < r ∧ ∃ s : Bool, ∀ y ∈ Metric.ball x r,
      (y ∈ P3544T1RayParity left ↔
        if s then 0 < P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y]
        else P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y] < 0) ∧
      (y ∈ P3544T1RayParity right ↔
        if s then P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y] < 0
        else 0 < P3381T1TriangleDeterminant ![p.vertex a, p.vertex b, y])
  endpoint_coherence : ∀ z ∈ ({p.vertex a, p.vertex b} : Set (Real × Real)),
    ∃ r : Real, 0 < r ∧
      Metric.ball z r ∩ P3544T1RayParity p =
        Metric.ball z r ∩ (P3544T1RayParity left ∪ P3544T1RayParity right ∪
          openSegment Real (p.vertex a) (p.vertex b))

end ApollonianSuperharmonic

end
