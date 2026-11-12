/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GaussianTranslation
public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileTranslation]

/-!
# TileTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $u\in\mathbb Z[i]$, the translate $T+u$ is obtained by replacing every
cell $s_x$ by $s_{x+u}$ and replacing the degenerate anchor by its translate
by $u$.
-/
def TileTranslation (T : ProtoTile) (u : GaussianInt) : ProtoTile :=
-- BODY
  ⟨T.cells.image (GaussianTranslation u), GaussianTranslation u T.anchor⟩

end ApollonianSuperharmonic

end
