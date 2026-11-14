/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.FordCircleCoordinate
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter

-- [TABLET NODE: FordRecursiveQuadruple]

/-!
# FordRecursiveQuadruple

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford--Farey parameter $P$, its ordered recursive quadruple is
$$
 (C_{p,q},C^1_{p,q},C^2_{p,q},(0,-1)),
$$
where $C^2_{p,q}=C_{p_2,q_2}$ and
$C^1_{p,q}=C_{p_1,q_1}$ if $q_1>0$, while for $q_1=0$ its coordinate is
the oriented line $(0,1)$.  Thus the $q=1$ convention produces the two
oppositely oriented line parents $(0,1)$ and $(0,-1)$ and one unit-circle
parent; it never treats $C_{1,0}$ as a positive-curvature circle.
-/
def FordRecursiveQuadruple (P : FordFareyParameter) :
    Fin 4 → CircleCoordinates :=
-- BODY
  ![FordCircleCoordinate P.p P.q,
    if P.q₁ = 0 then (0, 1) else FordCircleCoordinate P.p₁ P.q₁,
    FordCircleCoordinate P.p₂ P.q₂,
    (0, -1)]

end ApollonianSuperharmonic

end
