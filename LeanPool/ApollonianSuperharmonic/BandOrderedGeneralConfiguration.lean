/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple

-- [TABLET NODE: BandOrderedGeneralConfiguration]

/-!
# BandOrderedGeneralConfiguration

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An *ordered general configuration* for an ordered coordinate
quadruple $q=(C_0,C_1,C_2,C_3)$ consists of the following data and facts.
The quadruple is proper; none of its four entries is a line; and at most one
entry has curvature one.  Its curvatures satisfy
$$
 c_0>4,\qquad c_1>c_2\geq4,\qquad c_2\geq c_3.
$$
There are proper predecessor quadruples
$$
 r=(C_1,C_4,C_2,C_3),\qquad t=(C_2,C_3,C_5,C_6),
$$
where the full coordinate of the Soddy twin is
$$
 C_4=2(C_1+C_2+C_3)-C_0.
$$
Both predecessor children have curvature strictly less than $c_0$, and
the signed and nonnegative curvature identities
$$
 2c_1+2c_2+2c_3=c_0+c_4
$$
hold (the latter is expressed after taking nonnegative integer
curvatures).  Finally, the canonical vector identities obtained from the
displayed coordinate identifications are recorded explicitly:
$$
 v(r_2,r_0)=v(C_2,C_1),\quad
 v(r_3,r_0)=v(C_3,C_1),\quad
 v(t_1,t_0)=v(C_3,C_2).
$$
The entries $C_5,C_6$ are part of the second predecessor data.
-/
structure BandOrderedGeneralConfiguration
    (q : Fin 4 → CircleCoordinates) where
-- BODY
  proper : ProperBandQuadruple q
  noLine : ∀ i, (q i).1 ≠ 0
  atMostOneUnit : ∀ i j, (q i).1 = 1 → (q j).1 = 1 → i = j
  childLarge : 4 < (q 0).1
  order12 : (q 2).1 < (q 1).1
  secondLarge : 4 ≤ (q 2).1
  order23 : (q 3).1 ≤ (q 2).1
  /-- The predecessor presentation containing the first two parent circles. -/
  firstPredecessor : Fin 4 → CircleCoordinates
  /-- The second predecessor presentation used by the remaining parent pair. -/
  secondPredecessor : Fin 4 → CircleCoordinates
  firstProper : ProperBandQuadruple firstPredecessor
  secondProper : ProperBandQuadruple secondPredecessor
  firstChild : firstPredecessor 0 = q 1
  firstTwin : firstPredecessor 1 =
    (2 * (q 1).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 0).1,
      2 * (q 1).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 0).2)
  firstParentTwo : firstPredecessor 2 = q 2
  firstParentThree : firstPredecessor 3 = q 3
  secondChild : secondPredecessor 0 = q 2
  secondParentOne : secondPredecessor 1 = q 3
  firstSmaller : (firstPredecessor 0).1 < (q 0).1
  secondSmaller : (secondPredecessor 0).1 < (q 0).1
  soddy :
    2 * (q 1).1 + 2 * (q 2).1 + 2 * (q 3).1 =
      (q 0).1 + (firstPredecessor 1).1
  soddyNat :
    2 * Int.toNat (q 1).1 + 2 * Int.toNat (q 2).1 +
        2 * Int.toNat (q 3).1 =
      Int.toNat (q 0).1 + Int.toNat (firstPredecessor 1).1
  firstVectorTwo :
    BandVectors.1 (firstPredecessor 2) (firstPredecessor 0) =
      BandVectors.1 (q 2) (q 1)
  firstVectorThree :
    BandVectors.1 (firstPredecessor 3) (firstPredecessor 0) =
      BandVectors.1 (q 3) (q 1)
  secondVectorOne :
    BandVectors.1 (secondPredecessor 1) (secondPredecessor 0) =
      BandVectors.1 (q 3) (q 2)

end ApollonianSuperharmonic

end
