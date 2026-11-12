/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple

-- [TABLET NODE: TangencyCoordinatePolarizationLaw]

/-!
# TangencyCoordinatePolarizationLaw

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a coordinate quadruple $q=(C_0,C_1,C_2,C_3)$, write
$C_i=(c_i,w_i)$ and $\delta_{ab}=c_bw_a-c_aw_b$.  The
tangency-coordinate polarization law means that, whenever $a,b,j$ are
pairwise distinct,
$$
 \operatorname{Re}(\delta_{aj})\operatorname{Re}(\delta_{bj})+
 \operatorname{Im}(\delta_{aj})\operatorname{Im}(\delta_{bj})
 =c_ac_b+c_j(c_a+c_b)-c_j^2.
$$
Equivalently, the real polarization
$[u,v]=u\overline v+\overline u v$ of the two determinants is twice the
right-hand side.
-/
def TangencyCoordinatePolarizationLaw (q : Fin 4 → CircleCoordinates) : Prop :=
-- BODY
  ∀ a b j : Fin 4, a ≠ b → a ≠ j → b ≠ j →
    let u := (q j).1 • (q a).2 - (q a).1 • (q j).2
    let v := (q j).1 • (q b).2 - (q b).1 • (q j).2
    u.re * v.re + u.im * v.im =
      (q a).1 * (q b).1 + (q j).1 * ((q a).1 + (q b).1) - (q j).1 ^ 2

end ApollonianSuperharmonic

end
