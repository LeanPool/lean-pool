/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected

-- [TABLET NODE: P4849T1Component]

/-!
# P4849T1Component

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For sets $A,C\subseteq\mathbb Z[i]$, write
$\operatorname{Component}(A,C)$ when $C$ is nonempty and four-neighbor
connected, $C\subseteq A$, and every point of $A$ adjacent to a point of
$C$ belongs to $C$. Here connectedness is the finite-list path predicate
of `FourNeighborConnected`, and adjacency is that of
`FourNeighborAdjacent`. Thus this predicate specifies a whole
connected component, not merely a connected subset of $A$.
-/
def P4849T1Component (A C : Set GaussianInt) : Prop :=
-- BODY
  FourNeighborConnected C ∧ C ⊆ A ∧
    ∀ x ∈ C, ∀ y ∈ A, FourNeighborAdjacent x y → y ∈ C

end ApollonianSuperharmonic

end
