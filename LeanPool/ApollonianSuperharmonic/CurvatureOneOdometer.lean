/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: CurvatureOneOdometer]

/-!
# CurvatureOneOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $z\in\mathbb Z[i]$, the standard curvature-one partial odometer
$u_z$ has domain $\{0,1,i,1+i\}$ and values
$$
 u_z(0)=u_z(1)=u_z(i)=0,\qquad u_z(1+i)=\operatorname{Im}z.
$$
As for every partial odometer, its stored total-function representative is
zero away from the displayed domain.
-/
def CurvatureOneOdometer (z : GaussianInt) : PartialOdometer :=
-- BODY
  { domain := {0, 1, ⟨0, 1⟩, 1 + ⟨0, 1⟩}
    value := fun x => if x = 1 + ⟨0, 1⟩ then z.im else 0
    value_outside := by
      intro x hx
      apply ite_eq_right
      intro h
      apply hx
      subst x
      simp }

end ApollonianSuperharmonic

end
