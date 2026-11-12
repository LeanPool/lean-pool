/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianReflection
public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileReflection]

/-!
# TileReflection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The reflection $rT$ of a prototile in the real axis has cell basepoints
$r x-i$ for $x$ a cell basepoint of $T$, and has anchor $r(a_T)$.  The
subtraction of $i$ is the lower-left-corner correction for reflecting a
closed unit square.  An empty prototile therefore remains empty and its
singleton footprint is reflected by reflecting its assigned anchor.
-/
def TileReflection (T : ProtoTile) : ProtoTile :=
-- BODY
  ⟨T.cells.image (fun x => GaussianReflection x - ⟨0, 1⟩),
    GaussianReflection T.anchor⟩

end ApollonianSuperharmonic

end
