/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototile

-- [TABLET NODE: AncestorTile]

/-!
# AncestorTile

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An ancestor tile is a tile reached by restriction through the recursive
six-piece construction.  Formally, $(C,T)$ is an ancestor of $(C',T')$
when there is a finite chain beginning at $(C,T)$ and ending at $(C',T')$
such that each term is a parent prototile in one of the six signed
positions inside the next term.  Thus its footprint is contained in the
next footprint and its centroid displacement is
$\pm\frac12(v_{kj}-iv_{kj})$ for the corresponding proper quadruple.
The reflexive case allows a tile to be its own ancestor.
-/
def AncestorTile (C C' : CircleCoordinates) (T T' : ProtoTile) : Prop :=
-- BODY
  Relation.ReflTransGen
    (fun X Y : CircleCoordinates × ProtoTile =>
      ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Bool,
        ProperBandQuadruple q ∧ q 0 = Y.1 ∧ q i.succ = X.1 ∧
        BandPrototile Y.1 Y.2 ∧ BandPrototile X.1 X.2 ∧
        FootprintVertices X.2 ⊆ FootprintVertices Y.2 ∧
        TileCentroid X.2 - TileCentroid Y.2 =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).1))))
    (C, T) (C', T')

end ApollonianSuperharmonic

end
