/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4981T1EdgePrescription

-- [TABLET NODE: P4981T1PrescriptionValue]

/-!
# P4981T1PrescriptionValue

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For prescription data as in `P4981T1EdgePrescription` and any
edge-value function
$F=(v,a):(\mathbb Z\times\mathbb Z[i])^2\to\mathbb Z[i]^2$,
its prescribed value is respectively
$$
 (0,1),\quad (-1,-1-z-i),\quad (-i,iz-1),\quad
 (1+i,1+z-iz).
$$
For proper data $(q,j)$ put $p_j=q_{j+1}$, with subscripts taken modulo
three, $x=F(p_j,p_{j+2})$, and $y=F(p_{j+1},p_j)$. Its value is
$(x_v-i y_v,x_a+i y_a)$.
-/
def P4981T1PrescriptionValue {e : CircleCoordinates × CircleCoordinates}
    (p : P4981T1EdgePrescription e)
    (F : CircleCoordinates × CircleCoordinates → GaussianInt × GaussianInt) :
    GaussianInt × GaussianInt :=
-- BODY
  let ii : GaussianInt := ⟨0, 1⟩
  match p with
  | .line => (0, 1)
  | .left z => (-1, -1 - z - ii)
  | .right z => (-ii, ii * z - 1)
  | .unit z => (1 + ii, 1 + z - ii * z)
  | .proper q _ j =>
      let x := F (q j.succ, q ((j + 2).succ))
      let y := F (q ((j + 1).succ), q j.succ)
      (x.1 - ii * y.1, x.2 + ii * y.2)

end ApollonianSuperharmonic

end
