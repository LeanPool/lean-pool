/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: TileCentroid]

/-!
# TileCentroid

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a nonempty prototile, $\operatorname{cent}(T)$ is the arithmetic mean
of the centers $x+(1+i)/2$ of its unit cells, equivalently the Euclidean
centroid of $I(T)$.  For an empty prototile it is its designated anchor.
-/
noncomputable def TileCentroid (T : ProtoTile) : Real × Real :=
-- BODY
  if T.cells.Nonempty then
    ((((T.cells.sum fun x => x.re : Int) : Real) / T.cells.card + (1 / 2 : Real)),
      (((T.cells.sum fun x => x.im : Int) : Real) / T.cells.card + (1 / 2 : Real)))
  else ((((T.anchor.re : Int) : Real)), (((T.anchor.im : Int) : Real)))

end ApollonianSuperharmonic

end
