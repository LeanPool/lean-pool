/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeTile

-- [TABLET NODE: ExactTileTiling]

/-!
# ExactTileTiling

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A collection $\mathcal T$ is an exact tiling of the lattice cells when every
member is a topological-disk lattice tile and every cell $s_x$ belongs to
exactly one member of $\mathcal T$.  Tile boundaries may intersect, but two
members may not share a cell.
-/
def ExactTileTiling (F : Set ProtoTile) : Prop :=
-- BODY
  (∀ T ∈ F, LatticeTile T) ∧
    ∀ x : LatticeCell, ∃ T ∈ F, x ∈ T.cells ∧
      ∀ U ∈ F, x ∈ U.cells → U = T

end ApollonianSuperharmonic

end
