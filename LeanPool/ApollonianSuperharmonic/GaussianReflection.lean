/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: GaussianReflection]

/-!
# GaussianReflection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Reflection of the Gaussian-integer grid in the real axis is
$r(a+bi)=a-bi=\overline z$.
-/
def GaussianReflection (z : GaussianInt) : GaussianInt :=
-- BODY
  ⟨z.re, -z.im⟩

end ApollonianSuperharmonic

end
