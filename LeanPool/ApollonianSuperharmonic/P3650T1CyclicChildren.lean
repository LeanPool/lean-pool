/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3544T1BoundaryCarrier

-- [TABLET NODE: P3650T1CyclicChildren]

/-!
# P3650T1CyclicChildren

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a parent boundary $p$ and specified indices $A,B$, these data
consist of sizes $n_L,n_R<n$, two boundaries $p^L,p^R$ of
`P3381T1PolygonBoundary`, and injective maps
$\iota_L:\{0,\ldots,n_L+2\}\to\{0,\ldots,n+2\}$ and
$\iota_R:\{0,\ldots,n_R+2\}\to\{0,\ldots,n+2\}$ with
$p^L=p\circ\iota_L$, $p^R=p\circ\iota_R$.
There are nonempty lists $U,V$ and a rotation $k$ satisfying
$$
 [0,\ldots,n+2].\operatorname{rotate}(k)=[A]+U+[B]+V,
 \qquad\operatorname{ofFn}(\iota_L)=[A]+U+[B],
 \qquad\operatorname{ofFn}(\iota_R)=[B]+V+[A].
$$
The two image sets intersect exactly in $\{A,B\}$. With
$e=[p_A,p_B]$ and the carriers of `P3544T1BoundaryCarrier`,
$C_L\cup C_R=C_p\cup e$ and $C_L\cap C_R=e$.
Every index on the displayed arcs is retained, including straight
vertices. No assertion about odd sets is a field of this record.
-/
structure P3650T1CyclicChildren {n : Nat} (p : P3381T1PolygonBoundary n)
    (a b : Fin (n + 3)) where
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

end ApollonianSuperharmonic

end
