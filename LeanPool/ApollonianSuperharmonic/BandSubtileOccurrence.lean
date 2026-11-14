/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototile

-- [TABLET NODE: BandSubtileOccurrence]

/-!
# BandSubtileOccurrence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an ordered coordinate quadruple $q=(C_0,C_1,C_2,C_3)$ and a child
prototile $T$, a signed labeled subtile occurrence $S_i^\pm$ is a
prototile for $C_i$ whose footprint lies in that of $T$ and whose centroid
satisfies
$$
 \operatorname{cent}(S_i^\pm)-\operatorname{cent}(T)
 =\pm\tfrac12([v_{kj}]-[iv_{kj}])
$$
for the corresponding cyclic ordering $(i,j,k)$ of the three parents.
This definition records one labeled occurrence and does not assert that the
quadruple is proper.  In particular it also applies to the semiproper unit
configurations containing oriented lines.  The assertion that the six
occurrences cover $T$ is stated separately when needed.
-/
def BandSubtileOccurrence (q : Fin 4 → CircleCoordinates) (T : ProtoTile)
    (i : Fin 3) (s : Bool) (S : ProtoTile) : Prop :=
-- BODY
  BandPrototile (q i.succ) S ∧
    FootprintVertices S ⊆ FootprintVertices T ∧
    TileCentroid S - TileCentroid T =
      (if s = true then (1 : Real) else -1) •
        ((1 / 2 : Real) •
          ((GaussianRealPoint
              (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
            (-((GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ))
                  (q ((i + 1).succ)))).2),
              (GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ))
                  (q ((i + 1).succ)))).1))))

end ApollonianSuperharmonic

end
