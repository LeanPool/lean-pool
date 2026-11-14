/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: GaussianRealPoint]

/-!
# GaussianRealPoint

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The real point associated with $z=a+bi\in\mathbb Z[i]$ is
$[z]=(a,b)\in\mathbb R^2$.  Multiplication by $i$ therefore acts as the
quarter-turn $(a,b)\mapsto(-b,a)$.
-/
def GaussianRealPoint (z : GaussianInt) : Real × Real :=
-- BODY
  ((((z.re : Int) : Real)), (((z.im : Int) : Real)))

end ApollonianSuperharmonic

end
