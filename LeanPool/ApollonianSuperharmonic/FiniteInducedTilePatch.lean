/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation
public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: FiniteInducedTilePatch]

/-!
# FiniteInducedTilePatch

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $G$ be a plane triangulation whose vertices index prototiles $T_a$.
A *finite induced tile patch* consists of a nonempty finite vertex set
$K$ and a prototile $T_K$ whose cells are exactly
$$
  (T_K)_{\rm cells}=\bigcup_{a\in K}(T_a)_{\rm cells}.
$$
Distinct indices in $K$ must give distinct tiles.  The subgraph of $G$
induced by $K$ is connected: any two of its vertices are joined by a finite
$G$-path all of whose vertices remain in $K$.  The induced graph on the
complement is also connected, in the analogous pathwise sense.  The
prototile $T_K$, including its anchor, is retained as data so that later
topological conclusions concern the actual union tile rather than an
unspecified isomorphic copy.
-/
structure FiniteInducedTilePatch {ι : Type}
    (G : PlaneTriangulation ι) (tile : ι → ProtoTile) where
-- BODY
  /-- The finite nonempty set of vertices indexing the induced patch. -/
  indices : Finset ι
  /-- The literal union prototile, including its auxiliary anchor. -/
  unionTile : ProtoTile
  nonempty : indices.Nonempty
  tile_injective : Set.InjOn tile (indices : Set ι)
  exact_union : ∀ x, x ∈ unionTile.cells ↔
    ∃ a ∈ indices, x ∈ (tile a).cells
  induced_connected : ∀ a ∈ indices, ∀ b ∈ indices,
    ∃ p : List ι, p.head? = some a ∧ p.getLast? = some b ∧
      (∀ x ∈ p, x ∈ indices) ∧
      ∀ x y : ι, ∀ l₁ l₂ : List ι,
        p = l₁ ++ x :: y :: l₂ → G.adjacent x y
  complement_connected : ∀ a ∉ indices, ∀ b ∉ indices,
    ∃ p : List ι, p.head? = some a ∧ p.getLast? = some b ∧
      (∀ x ∈ p, x ∉ indices) ∧
      ∀ x y : ι, ∀ l₁ l₂ : List ι,
        p = l₁ ++ x :: y :: l₂ → G.adjacent x y

end ApollonianSuperharmonic

end
