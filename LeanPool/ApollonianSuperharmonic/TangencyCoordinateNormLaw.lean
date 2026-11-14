/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates

-- [TABLET NODE: TangencyCoordinateNormLaw]

/-!
# TangencyCoordinateNormLaw

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a coordinate quadruple $q=(C_0,C_1,C_2,C_3)$, with
$C_i=(c_i,w_i)$, the tangency-coordinate norm law means that, for every
pair of distinct indices $i,j$,
$$
 \left|c_jw_i-c_iw_j\right|^2=(c_i+c_j)^2.
$$
This is an algebraic property of the coordinate quadruple and asserts no
geometric sidedness.
-/
def TangencyCoordinateNormLaw (q : Fin 4 → CircleCoordinates) : Prop :=
-- BODY
  ∀ i j : Fin 4, i ≠ j →
    Zsqrtd.norm ((q j).1 • (q i).2 - (q i).1 • (q j).2) =
      ((q i).1 + (q j).1) ^ 2

end ApollonianSuperharmonic

end
