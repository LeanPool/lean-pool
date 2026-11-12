/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: RegularTileFamily]

/-!
# RegularTileFamily

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a prototile $T$ and an additive lattice $L\subseteq\mathbb Z[i]$, the
regular translate family $T+L$ is the collection $\{T+u:u\in L\}$.
-/
def RegularTileFamily (T : ProtoTile) (L : AddSubgroup GaussianInt) :
    Set ProtoTile :=
-- BODY
  {U | ∃ u ∈ L, U = TileTranslation T u}

end ApollonianSuperharmonic

end
