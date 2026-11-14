/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: RootedFourNeighborForest]

/-!
# RootedFourNeighborForest

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A finite induced four-neighbor graph $W$ is a \emph{forest rooted at
$R\subseteq W$} if every nonroot has a parent joined to it by a lattice
edge, ranks strictly increase from parent to child, the rank-zero vertices
are exactly $R$, every root is its own parent, and every edge is a parent
edge.  These conditions force each connected component to be a tree
containing exactly one root.
-/
def RootedFourNeighborForest (W R : Finset GaussianInt) : Prop :=
-- BODY
  R ⊆ W ∧ ∃ parent : GaussianInt → GaussianInt, ∃ rank : GaussianInt → ℕ,
    (∀ r ∈ R, parent r = r) ∧
    (∀ x ∈ W, x ∉ R →
      parent x ∈ W ∧ FourNeighborAdjacent (parent x) x ∧
        rank (parent x) < rank x) ∧
    (∀ x ∈ W, x ∈ R ↔ rank x = 0) ∧
    (∀ x ∈ W, ∀ y ∈ W, FourNeighborAdjacent x y →
      x = parent y ∨ y = parent x)

end ApollonianSuperharmonic

end
