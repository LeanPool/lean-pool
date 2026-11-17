/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.RegularTileFamily
public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.TilingLattice
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep

-- [TABLET NODE: TileString]

/-!
# TileString

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix a `BandPrototile` $T_C$ for $C$ and its regular translate family
$T_C+\Lambda_C$.  Thus the ambient family is the regular $C$-tiling, not
the translate family of an arbitrary prototile.  A tile string from $R$ to
$S$, with a chosen unit orientation $\epsilon$, is a finite list of
pairwise distinct tiles in this family, beginning
at $R$ and ending at $S$, with consecutive terms adjacent.  For
$c>1$, adjacency means `TileTouching`; for $c=1$ it is the
single triangular completion selected by
`UnitTriangularStep`: centroid differences satisfy
$\operatorname{UnitStep}_{\epsilon}$.  In particular, a string never
uses the eight-neighbor union of the two unit completions.

Every interior tile has nonnegative signed height above the directed line
from $\operatorname{cent}(R)$ to $\operatorname{cent}(S)$ and has an
adjacent tile of strictly negative signed height.  Here signed height is
the cross product
$$
 (y-y_R)(x_S-x_R)-(x-x_R)(y_S-y_R),
$$
which is the denominator-cleared form of the paper's imaginary-part
inequality.  When $R=S$, the string is the one-term list; otherwise the
pairwise-distinct condition forces distinct endpoints.
-/
def TileString (C : BandCircle) (orientation : Bool) (base R S : ProtoTile)
    (tiles : List ProtoTile) : Prop :=
-- BODY
  let adjacent := fun T U : ProtoTile =>
    if C.1.1.1 = 1 then
      ∃ v : GaussianInt,
        UnitTriangularStep orientation v ∧
        TileCentroid U - TileCentroid T = GaussianRealPoint v
    else TileTouching T U
  let height := fun T : ProtoTile =>
    ((TileCentroid T).2 - (TileCentroid R).2) *
        ((TileCentroid S).1 - (TileCentroid R).1) -
      ((TileCentroid T).1 - (TileCentroid R).1) *
        ((TileCentroid S).2 - (TileCentroid R).2)
  BandPrototile C.1.1 base ∧
    tiles.head? = some R ∧ tiles.getLast? = some S ∧
    tiles.Pairwise (fun T U => T ≠ U) ∧
    (∀ T, T ∈ tiles → T ∈ RegularTileFamily base (TilingLattice C)) ∧
    tiles.IsChain adjacent ∧
    ∀ pre T post, tiles = pre ++ T :: post →
      pre ≠ [] → post ≠ [] →
      0 ≤ height T ∧
      ∃ U ∈ RegularTileFamily base (TilingLattice C),
        adjacent T U ∧ height U < 0

end ApollonianSuperharmonic

end
