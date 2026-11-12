/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: CentrallyReflectedAt]

/-!
# CentrallyReflectedAt

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two prototiles $T,U$ are centrally reflected about a point $x$ when
half-turn about $x$ carries the complete closed-square realization of $T$
onto that of $U$:
$$
 I(U)=\{\,2x-p:p\in I(T)\,\}.
$$
This relation concerns supporting cells and their edges, not only the sets
of footprint vertices.
-/
def CentrallyReflectedAt (x : Real × Real) (T U : ProtoTile) : Prop :=
-- BODY
  TileRealization U =
    (fun p : Real × Real => (2 * x.1 - p.1, 2 * x.2 - p.2)) ''
      TileRealization T

end ApollonianSuperharmonic

end
