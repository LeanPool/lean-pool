/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: GlobalOdometerExtends]

/-!
# GlobalOdometerExtends

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An integer function $g$ on $\mathbb Z[i]$ *extends* a partial
odometer $h$, up to its irrelevant additive normalization, when there is
an integer $c$ such that $g(x)=h(x)+c$ at every point of the domain of
$h$.
-/
def GlobalOdometerExtends (g : IntegerLatticeFunction) (h : PartialOdometer) : Prop :=
-- BODY
  ∃ c : ℤ, ∀ x, x ∈ h.domain → g x = h.value x + c

end ApollonianSuperharmonic

end
