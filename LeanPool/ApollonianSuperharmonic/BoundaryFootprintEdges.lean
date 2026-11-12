/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: BoundaryFootprintEdges]

/-!
# BoundaryFootprintEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The boundary-footprint edges of a prototile are the unit lattice edges
incident to exactly one of its cells.  Concretely, the horizontal edge
$\{z,z+1\}$ is a boundary edge exactly when precisely one of the cells based
at $z$ and $z-i$ belongs to the prototile, and the vertical edge
$\{z,z+i\}$ is a boundary edge exactly when precisely one of the cells based
at $z$ and $z-1$ belongs to it.  Thus these are actual boundary edges, not
edges inferred merely from their endpoints.
-/
def BoundaryFootprintEdges (T : ProtoTile) : Set (Finset GaussianInt) :=
-- BODY
  {e | ∃ z : GaussianInt,
    (e = {z, z + 1} ∧
      ((z ∈ T.cells ∧ z - ⟨0, 1⟩ ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - ⟨0, 1⟩ ∈ T.cells))) ∨
    (e = {z, z + ⟨0, 1⟩} ∧
      ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - 1 ∈ T.cells)))}

end ApollonianSuperharmonic

end
