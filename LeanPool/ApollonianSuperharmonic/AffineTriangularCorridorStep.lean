/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineTriangularFaceVertices
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent

-- [TABLET NODE: AffineTriangularCorridorStep]

/-!
# AffineTriangularCorridorStep

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $P,Q$ be two finite lattice-vertex lists and let $F,G$ be tagged
`AffineTriangularFace`s.  They make an affine triangular corridor
step, relative to $(P,Q)$, when $F\ne G$ and they share an entire
elementary edge $\{u,v\}$: the vertices $u\ne v$ are
`TriangularLatticeAdjacent` and both belong to
$V(F)\cap V(G)$ as defined by
`AffineTriangularFaceVertices`.  The shared edge must have one of
the following two audited forms after possibly naming its endpoints in the
opposite order:
$$
 \begin{array}{ll}
 \textnormal{crossing:}&u\in(P.\operatorname{drop}1).\operatorname{dropLast}
 \textnormal{ and }
 v\in(Q.\operatorname{drop}1).\operatorname{dropLast},\\
 \textnormal{fan:}&u\in(P.\operatorname{drop}1).\operatorname{dropLast}
 \cap(Q.\operatorname{drop}1).\operatorname{dropLast}.
 \end{array}
$$
In the fan case the second endpoint $v$ is unrestricted beyond being the
other endpoint of the common elementary edge.
-/
def AffineTriangularCorridorStep
    (forward reverse : List (Int × Int))
    (f g : AffineTriangularFace) : Prop :=
-- BODY
  f ≠ g ∧
  ∃ u v : Int × Int,
    u ≠ v ∧
    TriangularLatticeAdjacent u v ∧
    u ∈ AffineTriangularFaceVertices f ∧
    v ∈ AffineTriangularFaceVertices f ∧
    u ∈ AffineTriangularFaceVertices g ∧
    v ∈ AffineTriangularFaceVertices g ∧
    ((u ∈ (forward.drop 1).dropLast ∧
        v ∈ (reverse.drop 1).dropLast) ∨
      (u ∈ (forward.drop 1).dropLast ∧
        u ∈ (reverse.drop 1).dropLast))

end ApollonianSuperharmonic

end
