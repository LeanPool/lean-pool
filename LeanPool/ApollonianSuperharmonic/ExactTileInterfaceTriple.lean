/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: ExactTileInterfaceTriple]

/-!
# ExactTileInterfaceTriple

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An *exact tile-interface triple* for prototiles $A,B,C$ records a
lattice vertex $\rho$ and, for each of the pairs $AB,BC,CA$, the other
endpoint of a nontrivial simple path.  In each case the path's vertex set
and its set of actual supporting lattice edges are exactly the complete
common footprint of the pair, in the sense of
`SimpleGridPathBetween`, and one endpoint is $\rho$.  Finally,
$\rho$ is required to be the unique vertex common to all three footprints.
This is interface data; it does not itself assert that the three prototiles
are disks, cell-disjoint, or a touching triple.
-/
structure ExactTileInterfaceTriple (A B C : ProtoTile) where
-- BODY
  /-- The unique common lattice vertex of all three tile footprints. -/
  point : GaussianInt
  /-- The opposite endpoint of the complete interface between A and B. -/
  otherAB : GaussianInt
  /-- The opposite endpoint of the complete interface between B and C. -/
  otherBC : GaussianInt
  /-- The opposite endpoint of the complete interface between C and A. -/
  otherCA : GaussianInt
  pathAB : SimpleGridPathBetween
    (FootprintVertices A ∩ FootprintVertices B)
    (FootprintEdges A ∩ FootprintEdges B) point otherAB
  pathBC : SimpleGridPathBetween
    (FootprintVertices B ∩ FootprintVertices C)
    (FootprintEdges B ∩ FootprintEdges C) point otherBC
  pathCA : SimpleGridPathBetween
    (FootprintVertices C ∩ FootprintVertices A)
    (FootprintEdges C ∩ FootprintEdges A) point otherCA
  unique_common : ∀ x,
    x ∈ FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C ↔
      x = point

end ApollonianSuperharmonic

end
