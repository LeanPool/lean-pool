/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: GaussianQuarterTurn]

/-!
# GaussianQuarterTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The counterclockwise quarter-turn of the Gaussian-integer grid about the
origin is $q(a+bi)=-b+ai=iz$.
-/
def GaussianQuarterTurn (z : GaussianInt) : GaussianInt :=
-- BODY
  ⟨-z.im, z.re⟩

end ApollonianSuperharmonic

end
