/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: P4250T1SlopeOffset]

/-!
# P4250T1SlopeOffset

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Gaussian integer $a$, let
$$
 d(a)=\bigl((\Re a-\Im a)/2,(\Im a+\Re a)/2\bigr).
$$
Thus, identifying the real plane with $\mathbb C$, $d(a)=(a+ia)/2$.
-/
noncomputable def P4250T1SlopeOffset (a : GaussianInt) : Real × Real :=
-- BODY
  (((a.re : Real) - (a.im : Real)) / 2,
    ((a.im : Real) + (a.re : Real)) / 2)

end ApollonianSuperharmonic

end
