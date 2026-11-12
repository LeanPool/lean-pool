/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: P5157T1StaircasePoint]

/-!
# P5157T1StaircasePoint

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Gaussian integer $z$, a Boolean $h$, an integer $s$, and $j\geq0$, put
$$
 p(z,h,s,j)=
 \begin{cases}
 z+(\lceil j/2\rceil,s\lfloor j/2\rfloor),&h=\mathrm{true},\\
 z+(\lfloor j/2\rfloor,s\lceil j/2\rceil),&h=\mathrm{false}.
 \end{cases}
$$
Thus, when $s=\pm1$, the staircase alternates a rightward unit step
and a vertical step of sign $s$, starting horizontally exactly when $h$ is true.
-/
def P5157T1StaircasePoint (z : GaussianInt) (horizontalFirst : Bool)
    (s : Int) (j : Nat) : GaussianInt :=
-- BODY
  z + ⟨(if horizontalFirst then (j + 1) / 2 else j / 2 : Nat),
    s * (if horizontalFirst then j / 2 else (j + 1) / 2 : Nat)⟩

end ApollonianSuperharmonic

end
